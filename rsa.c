/*
 * TP : Implémentation de RSA de manière sécurisée
 * 5CRYP Cryptologie - M2 Cyberdéfense - École Hexagone
 *
 * Sections:
 *   2. RSA Textbook 32 bits
 *   3.1 Attaque par dictionnaire
 *   3.2 PKCS#1 v1.5 (variante tronquée)
 *   3.3 Attaque de Bleichenbacher (démonstration)
 *   3.4 RSA OAEP (variante simplifiée)
 *   4. Attaques par canaux auxiliaires (timing)
 *
 * Compilation : gcc -std=c11 -O2 -Wall -Wextra -Wpedantic -o tp_rsa rsa.c -lssl -lcrypto
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <sys/time.h>
#include <openssl/rand.h>

/* ============================================================
 * Wrappers CSPRNG autour de RAND_bytes
 * ============================================================ */

static uint16_t rand_u16(void) {
    uint16_t val;
    if (RAND_bytes((unsigned char *)&val, sizeof(val)) != 1) {
        fprintf(stderr, "RAND_bytes failed\n");
        exit(1);
    }
    return val;
}

static uint32_t rand_u32(void) {
    uint32_t val;
    if (RAND_bytes((unsigned char *)&val, sizeof(val)) != 1) {
        fprintf(stderr, "RAND_bytes failed\n");
        exit(1);
    }
    return val;
}

static uint8_t rand_u8(void) {
    uint8_t val;
    if (RAND_bytes(&val, sizeof(val)) != 1) {
        fprintf(stderr, "RAND_bytes failed\n");
        exit(1);
    }
    return val;
}

// Retourne un uint64_t dans [lo, hi] (inclus)
static uint64_t rand_range(uint64_t lo, uint64_t hi) {
    if (lo >= hi) return lo;
    uint64_t range = hi - lo + 1;
    uint64_t val;
    RAND_bytes((unsigned char *)&val, sizeof(val));
    return lo + (val % range);
}

/* ============================================================
 * Utilitaires mathématiques
 * ============================================================ */

// Exponentiation rapide modulaire (square-and-multiply classique)
// ATTENTION: vulnérable aux attaques par canaux auxiliaires (cf. section 4)
uint64_t mod_exp(uint64_t base, uint64_t exp, uint64_t mod) {
    uint64_t result = 1;
    base %= mod;
    while (exp > 0) {
        if (exp & 1)
            result = (__uint128_t)result * base % mod;
        exp >>= 1;
        base = (__uint128_t)base * base % mod;
    }
    return result;
}

// Exponentiation rapide modulaire constante en temps (Montgomery ladder)
// Contre-mesure pour la section 4
uint64_t mod_exp_constant_time(uint64_t base, uint64_t exp, uint64_t mod) {
    uint64_t r0 = 1;
    uint64_t r1 = base % mod;
    for (int i = 63; i >= 0; i--) {
        if ((exp >> i) & 1) {
            r0 = (__uint128_t)r0 * r1 % mod;
            r1 = (__uint128_t)r1 * r1 % mod;
        } else {
            r1 = (__uint128_t)r0 * r1 % mod;
            r0 = (__uint128_t)r0 * r0 % mod;
        }
    }
    return r0;
}

// PGCD
uint64_t gcd(uint64_t a, uint64_t b) {
    while (b) {
        uint64_t t = b;
        b = a % b;
        a = t;
    }
    return a;
}

// Algorithme d'Euclide étendu
int64_t extended_gcd(int64_t a, int64_t b, int64_t *x, int64_t *y) {
    if (a == 0) {
        *x = 0;
        *y = 1;
        return b;
    }
    int64_t x1, y1;
    int64_t g = extended_gcd(b % a, a, &x1, &y1);
    *x = y1 - (b / a) * x1;
    *y = x1;
    return g;
}

// Inverse modulaire
uint64_t mod_inverse(uint64_t e, uint64_t phi) {
    int64_t x, y;
    int64_t g = extended_gcd((int64_t)e, (int64_t)phi, &x, &y);
    if (g != 1) return 0;
    return (uint64_t)((x % (int64_t)phi + (int64_t)phi) % (int64_t)phi);
}

// Test de Miller-Rabin (témoin aléatoire via RAND_bytes)
int miller_rabin(uint64_t n, int iterations) {
    if (n < 2) return 0;
    if (n == 2 || n == 3) return 1;
    if (n % 2 == 0) return 0;

    uint64_t d = n - 1;
    int r = 0;
    while (d % 2 == 0) {
        d /= 2;
        r++;
    }

    for (int i = 0; i < iterations; i++) {
        uint64_t a = rand_range(2, n - 2);
        uint64_t x = mod_exp(a, d, n);

        if (x == 1 || x == n - 1)
            continue;

        int found = 0;
        for (int j = 0; j < r - 1; j++) {
            x = (__uint128_t)x * x % n;
            if (x == n - 1) {
                found = 1;
                break;
            }
        }
        if (!found)
            return 0;
    }
    return 1;
}

// Génération d'un nombre premier de 16 bits via RAND_bytes
uint16_t generate_prime_16bit(void) {
    uint16_t candidate;
    do {
        candidate = rand_u16();
        candidate |= 0x8000; // bit de poids fort à 1 (16 bits complets)
        candidate |= 1;      // forcer impair
    } while (!miller_rabin(candidate, 20));
    return candidate;
}

// Poids de Hamming
int hamming_weight(uint32_t x) {
    int count = 0;
    while (x) {
        count += x & 1;
        x >>= 1;
    }
    return count;
}

/* ============================================================
 * Section 2 : RSA Textbook 32 bits
 * ============================================================ */

typedef struct {
    uint32_t n;
    uint32_t e;
    uint32_t d;
    uint16_t p;
    uint16_t q;
} RSAKey;

RSAKey rsa_keygen(void) {
    RSAKey key;
    key.e = 3;

    // gcd(e, phi(n)) = 1 => p ≢ 1 mod 3 et q ≢ 1 mod 3
    do {
        key.p = generate_prime_16bit();
    } while (key.p % 3 == 1);

    do {
        key.q = generate_prime_16bit();
    } while (key.q % 3 == 1 || key.q == key.p);

    key.n = (uint32_t)key.p * (uint32_t)key.q;

    uint32_t phi = (uint32_t)(key.p - 1) * (uint32_t)(key.q - 1);
    key.d = (uint32_t)mod_inverse(key.e, phi);

    return key;
}

uint32_t rsa_encrypt(uint32_t m, uint32_t e, uint32_t n) {
    return (uint32_t)mod_exp(m, e, n);
}

uint32_t rsa_decrypt(uint32_t c, uint32_t d, uint32_t n) {
    return (uint32_t)mod_exp(c, d, n);
}

/* ============================================================
 * Section 3.1 : Attaque par dictionnaire
 * ============================================================ */

void dictionary_attack(RSAKey *key) {
    printf("\n=== 3.1 Attaque par dictionnaire (m < 100) ===\n");

    clock_t start = clock();
    uint32_t ciphertexts[100];
    for (int m = 1; m < 100; m++) {
        ciphertexts[m] = rsa_encrypt((uint32_t)m, key->e, key->n);
    }
    clock_t elapsed_encrypt = clock() - start;
    printf("Temps pour chiffrer m=1..99 : %.6f s (%ld ticks)\n",
           (double)elapsed_encrypt / CLOCKS_PER_SEC, (long)elapsed_encrypt);

    uint32_t secret_m = 42;
    uint32_t target_c = rsa_encrypt(secret_m, key->e, key->n);
    printf("Chiffré cible (m=%u) : c = %u\n", secret_m, target_c);

    start = clock();
    for (int m = 1; m < 100; m++) {
        if (ciphertexts[m] == target_c) {
            clock_t elapsed_attack = clock() - start;
            printf("Message retrouvé : m = %d (en %.6f s, %ld ticks)\n",
                   m, (double)elapsed_attack / CLOCKS_PER_SEC, (long)elapsed_attack);
            break;
        }
    }
}

/* ============================================================
 * Section 3.2 : PKCS#1 v1.5 (variante tronquée)
 * ============================================================ */

// Format tronqué (sans le premier 0x00) : BT || PS || 0x00 || D
// Total = 4 octets = 32 bits

uint32_t pkcs15_encode(uint8_t message, uint8_t bt) {
    uint8_t ps;
    switch (bt) {
        case 0x00: ps = 0x00; break;
        case 0x01: ps = 0xFF; break;
        case 0x02:
            do { ps = rand_u8(); } while (ps == 0x00);
            break;
        default:
            fprintf(stderr, "BT invalide\n");
            return 0;
    }
    return ((uint32_t)bt << 24) | ((uint32_t)ps << 16) | ((uint32_t)0x00 << 8) | message;
}

int pkcs15_decode(uint32_t eb, uint8_t expected_bt) {
    uint8_t bt  = (eb >> 24) & 0xFF;
    uint8_t ps  = (eb >> 16) & 0xFF;
    uint8_t sep = (eb >>  8) & 0xFF;
    uint8_t msg =  eb        & 0xFF;

    if (bt != expected_bt) return -1;
    if (sep != 0x00)       return -1;

    switch (bt) {
        case 0x01: if (ps != 0xFF) return -1; break;
        case 0x02: if (ps == 0x00) return -1; break;
    }
    return msg;
}

int pkcs15_oracle(uint32_t c, RSAKey *key) {
    uint32_t decrypted = rsa_decrypt(c, key->d, key->n);
    uint8_t bt  = (decrypted >> 24) & 0xFF;
    uint8_t ps  = (decrypted >> 16) & 0xFF;
    uint8_t sep = (decrypted >>  8) & 0xFF;
    return (bt == 0x02 && sep == 0x00 && ps != 0x00);
}

void demo_pkcs15(RSAKey *key) {
    printf("\n=== 3.2 PKCS#1 v1.5 ===\n");

    uint8_t message = 0x2A;
    printf("Message original : 0x%02X (%d)\n", message, message);

    for (int bt = 0; bt <= 2; bt++) {
        uint32_t eb = pkcs15_encode(message, (uint8_t)bt);
        printf("\nBT=%d : EB = 0x%08X\n", bt, eb);

        if (eb >= key->n) {
            printf("  ATTENTION: EB >= n, on saute ce BT.\n");
            continue;
        }

        uint32_t c = rsa_encrypt(eb, key->e, key->n);
        printf("  Chiffré : %u\n", c);

        uint32_t decrypted_eb = rsa_decrypt(c, key->d, key->n);
        printf("  EB déchiffré : 0x%08X\n", decrypted_eb);

        int recovered = pkcs15_decode(decrypted_eb, (uint8_t)bt);
        if (recovered >= 0)
            printf("  Message récupéré : 0x%02X (%d) ✓\n", recovered, recovered);
        else
            printf("  Erreur de décodage ✗\n");
    }
}

/* ============================================================
 * Section 3.3 : Attaque de Bleichenbacher (démonstration)
 * ============================================================ */

void demo_bleichenbacher(RSAKey *key) {
    printf("\n=== 3.3 Attaque de Bleichenbacher (démonstration) ===\n");

    uint32_t B = 1 << 16;
    printf("B = 2^16 = %u\n", B);
    printf("Plage PKCS valide : [2B, 3B) = [%u, %u)\n", 2 * B, 3 * B);

    uint8_t message = 0x2A;
    uint32_t eb = pkcs15_encode(message, 0x02);

    if (eb >= key->n) {
        printf("EB >= n, impossible de démontrer l'attaque.\n");
        return;
    }

    uint32_t c = rsa_encrypt(eb, key->e, key->n);
    printf("Message original : 0x%02X, EB = 0x%08X, c = %u\n", message, eb, c);

    printf("\nDémonstration de la malléabilité :\n");
    int oracle_calls = 0;
    int conforming_found = 0;

    for (uint32_t s = 1; s < 1000 && conforming_found < 5; s++) {
        uint64_t se = mod_exp(s, key->e, key->n);
        uint64_t c_prime = (__uint128_t)se * c % key->n;
        oracle_calls++;

        if (pkcs15_oracle((uint32_t)c_prime, key)) {
            uint32_t sm = rsa_decrypt((uint32_t)c_prime, key->d, key->n);
            printf("  s=%u : oracle OK, s*m mod n = 0x%08X (PKCS conforme)\n", s, sm);
            conforming_found++;
        }
    }
    printf("Appels à l'oracle : %d, réponses conformes : %d\n", oracle_calls, conforming_found);
    printf("(Dans la vraie attaque, on raffine les bornes sur m itérativement.)\n");
}

/* ============================================================
 * Section 3.4 : RSA OAEP (variante simplifiée)
 * ============================================================ */

// MGF simplifiée : G(X) = ((X * 1103515245 + 12345) >> 16) & 0xFF
uint8_t mgf(uint8_t x) {
    uint32_t val = (uint32_t)x * 1103515245 + 12345;
    return (uint8_t)((val >> 16) & 0xFF);
}

uint32_t oaep_encode(uint8_t message, uint8_t seed) {
    uint8_t db          = message;
    uint8_t masked_db   = db ^ mgf(seed);
    uint8_t masked_seed = seed ^ mgf(masked_db);
    return ((uint32_t)0x00 << 16) | ((uint32_t)masked_seed << 8) | masked_db;
}

int oaep_decode(uint32_t em, uint8_t *message) {
    uint8_t first_byte  = (em >> 16) & 0xFF;
    uint8_t masked_seed = (em >>  8) & 0xFF;
    uint8_t masked_db   =  em        & 0xFF;

    if (first_byte != 0x00) return -1;

    uint8_t seed = masked_seed ^ mgf(masked_db);
    uint8_t db   = masked_db   ^ mgf(seed);

    *message = db;
    return 0;
}

void demo_oaep(RSAKey *key) {
    printf("\n=== 3.4 RSA OAEP (variante simplifiée) ===\n");

    uint8_t message = 0x2A;
    uint8_t seed = rand_u8();
    printf("Message : 0x%02X (%d), Seed : 0x%02X\n", message, message, seed);

    uint32_t em = oaep_encode(message, seed);
    printf("EM encodé : 0x%06X\n", em);

    if (em >= key->n) {
        printf("ATTENTION: EM >= n. On réduit le seed.\n");
        seed = 0x01;
        em = oaep_encode(message, seed);
        printf("Nouveau EM : 0x%06X (seed=0x%02X)\n", em, seed);
    }

    uint32_t c = rsa_encrypt(em, key->e, key->n);
    printf("Chiffré OAEP : %u\n", c);

    uint32_t decrypted_em = rsa_decrypt(c, key->d, key->n);
    printf("EM déchiffré : 0x%06X\n", decrypted_em);

    uint8_t recovered;
    if (oaep_decode(decrypted_em, &recovered) == 0)
        printf("Message récupéré : 0x%02X (%d) ✓\n", recovered, recovered);
    else
        printf("Erreur de décodage OAEP ✗\n");

    printf("\nPropriété probabiliste (même message, seeds différents) :\n");
    for (int i = 0; i < 5; i++) {
        uint8_t s = (uint8_t)(i * 37 + 13);
        uint32_t e = oaep_encode(message, s);
        if (e < key->n) {
            uint32_t ci = rsa_encrypt(e, key->e, key->n);
            printf("  seed=0x%02X -> EM=0x%06X -> c=%u\n", s, e, ci);
        }
    }
}

/* ============================================================
 * Section 4 : Attaques par canaux auxiliaires (timing)
 * ============================================================ */

typedef struct {
    uint64_t squarings;
    uint64_t multiplications;
} OpCount;

uint64_t mod_exp_counted(uint64_t base, uint64_t exp, uint64_t mod, OpCount *ops) {
    uint64_t result = 1;
    base %= mod;
    ops->squarings = 0;
    ops->multiplications = 0;
    while (exp > 0) {
        if (exp & 1) {
            result = (__uint128_t)result * base % mod;
            ops->multiplications++;
        }
        exp >>= 1;
        if (exp > 0) {
            base = (__uint128_t)base * base % mod;
            ops->squarings++;
        }
    }
    return result;
}

void timing_attack_analysis(RSAKey *key) {
    printf("\n=== 4. Attaques par canaux auxiliaires ===\n");

    uint32_t m = 12345;
    int iterations = 1000000;

    printf("Modulo n = %u, message m = %u\n", key->n, m);
    printf("Nombre d'itérations : %d\n\n", iterations);

    // Comptage d'opérations
    printf("--- Analyse du nombre d'opérations (square-and-multiply classique) ---\n");
    printf("%-15s %-10s %-15s %-15s %-15s\n",
           "Exposant", "HW", "Carrés", "Multiplications", "Total ops");

    for (int t = 0; t < 5; t++) {
        uint32_t exp = rand_u32();
        int hw = hamming_weight(exp);
        OpCount ops;
        mod_exp_counted(m, exp, key->n, &ops);
        printf("0x%08X      %-10d %-15lu %-15lu %-15lu\n",
               exp, hw, (unsigned long)ops.squarings,
               (unsigned long)ops.multiplications,
               (unsigned long)(ops.squarings + ops.multiplications));
    }

    OpCount ops;
    {
        uint32_t exp = 0xFFFFFFFF;
        mod_exp_counted(m, exp, key->n, &ops);
        printf("0xFFFFFFFF    %-10d %-15lu %-15lu %-15lu  <-- HW max\n",
               32, (unsigned long)ops.squarings, (unsigned long)ops.multiplications,
               (unsigned long)(ops.squarings + ops.multiplications));
    }
    {
        uint32_t exp = 0xA0000000;
        mod_exp_counted(m, exp, key->n, &ops);
        printf("0xA0000000    %-10d %-15lu %-15lu %-15lu  <-- HW min\n",
               hamming_weight(0xA0000000), (unsigned long)ops.squarings,
               (unsigned long)ops.multiplications,
               (unsigned long)(ops.squarings + ops.multiplications));
    }
    {
        uint32_t exp = 0x80000000;
        mod_exp_counted(m, exp, key->n, &ops);
        printf("0x80000000    %-10d %-15lu %-15lu %-15lu  <-- HW=1\n",
               1, (unsigned long)ops.squarings, (unsigned long)ops.multiplications,
               (unsigned long)(ops.squarings + ops.multiplications));
    }

    // Mesure de timing avec clock()
    printf("\n--- Mesure de timing (%d itérations) ---\n", iterations);
    printf("%-25s %-25s %-25s\n",
           "Exposant", "Classique", "Constant time");

    uint32_t test_exps[] = {0xFFFFFFFF, 0xA0000000, 0x55555555, 0x80000000, 0x00000003};
    const char* labels[] = {
        "0xFFFFFFFF (HW=32)",
        "0xA0000000 (HW=2)",
        "0x55555555 (HW=16)",
        "0x80000000 (HW=1)",
        "0x00000003 (HW=2, petit)"
    };

    for (int t = 0; t < 5; t++) {
        volatile uint32_t sink = 0;

        clock_t start = clock();
        for (int i = 0; i < iterations; i++) {
            sink += (uint32_t)mod_exp(m, test_exps[t], key->n);
        }
        clock_t elapsed_classic = clock() - start;

        start = clock();
        for (int i = 0; i < iterations; i++) {
            sink += (uint32_t)mod_exp_constant_time(m, test_exps[t], key->n);
        }
        clock_t elapsed_ct = clock() - start;

        printf("%-25s %6ld ticks (%6.1f ms)   %6ld ticks (%6.1f ms)\n",
               labels[t],
               (long)elapsed_classic,
               (double)elapsed_classic / CLOCKS_PER_SEC * 1000.0,
               (long)elapsed_ct,
               (double)elapsed_ct / CLOCKS_PER_SEC * 1000.0);
        (void)sink;
    }

    printf("\nObservation : avec l'exponentiation classique (square-and-multiply),\n");
    printf("le temps d'exécution dépend du poids de Hamming de l'exposant.\n");
    printf("Plus il y a de bits à 1, plus il y a de multiplications, donc plus c'est lent.\n");
    printf("Cela constitue un canal auxiliaire exploitable (timing side-channel).\n\n");
    printf("Contre-mesure : la Montgomery ladder effectue le même nombre d'opérations\n");
    printf("indépendamment de la valeur de l'exposant, rendant le temps constant.\n");
}

/* ============================================================
 * Main
 * ============================================================ */

int main(void) {
    printf("========================================\n");
    printf("  TP RSA - Implémentation sécurisée\n");
    printf("  M2 Cyberdéfense - École Hexagone\n");
    printf("========================================\n");

    // Section 2
    printf("\n=== 2. RSA Textbook 32 bits ===\n");
    RSAKey key = rsa_keygen();
    printf("Clef générée :\n");
    printf("  p = %u, q = %u\n", key.p, key.q);
    printf("  n = %u\n", key.n);
    printf("  e = %u\n", key.e);
    printf("  d = %u\n", key.d);

    uint32_t phi = (uint32_t)(key.p - 1) * (uint32_t)(key.q - 1);
    printf("  phi(n) = %u\n", phi);

    uint64_t check = (__uint128_t)key.e * key.d % phi;
    printf("  Vérification e*d mod phi(n) = %lu\n", (unsigned long)check);

    uint32_t m = 123456;
    if (m >= key.n) m = key.n - 1;
    uint32_t c = rsa_encrypt(m, key.e, key.n);
    uint32_t m_dec = rsa_decrypt(c, key.d, key.n);
    printf("\nTest : m = %u -> c = %u -> m' = %u %s\n",
           m, c, m_dec, (m == m_dec) ? "✓" : "✗");

    // Section 3.1
    dictionary_attack(&key);

    // Section 3.2
    demo_pkcs15(&key);

    // Section 3.3
    demo_bleichenbacher(&key);

    // Section 3.4
    demo_oaep(&key);

    // Section 4
    timing_attack_analysis(&key);

    return 0;
}