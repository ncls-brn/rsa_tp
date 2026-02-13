/*
 * TP : Implémentation de RSA de manière sécurisée
 * 5CRYP Cryptologie - M2 Cyberdéfense - École Hexagone
 *
 * Corrections principales :
 * - mod_exp_constant_time : suppression de la branche dépendante des bits (vrai constant-time via cswap masqué)
 * - mod_exp_counted : comptage cohérent (1 carré par bit traité, comme le square-and-multiply standard)
 * - clock_gettime : ajout du define POSIX pour compatibilité
 * - printf uint64_t : utilisation de PRIu64 (portable)
 */

#define _POSIX_C_SOURCE 199309L

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>
#include <string.h>
#include <time.h>

/* ============================================================
 * Utilitaires mathématiques
 * ============================================================ */

uint64_t mod_exp(uint64_t base, uint64_t exp, uint64_t mod) {
    if (mod == 0) return 0;
    uint64_t result = 1;
    base %= mod;
    while (exp > 0) {
        if (exp & 1ULL)
            result = (uint64_t)((__uint128_t)result * base % mod);
        exp >>= 1ULL;
        base = (uint64_t)((__uint128_t)base * base % mod);
    }
    return result;
}

/* cswap constant-time (mask = 0 ou 0xFFFF..FFFF) */
static inline void ct_cswap_u64(uint64_t *a, uint64_t *b, uint64_t mask) {
    uint64_t x = (*a ^ *b) & mask;
    *a ^= x;
    *b ^= x;
}

/*
 * Exponentiation modulaire "Montgomery ladder" sans branche dépendante des bits.
 * Remarque : en C, compiler et micro-architecture peuvent encore introduire des effets.
 * Pour un vrai usage crypto, préférer une lib dédiée (OpenSSL, libsodium, etc.).
 */
uint64_t mod_exp_constant_time(uint64_t base, uint64_t exp, uint64_t mod) {
    if (mod == 0) return 0;

    uint64_t r0 = 1 % mod;
    uint64_t r1 = base % mod;

    for (int i = 63; i >= 0; i--) {
        uint64_t bit = (exp >> (uint64_t)i) & 1ULL;
        uint64_t mask = 0ULL - bit; /* 0 -> 0x0, 1 -> 0xFFFF..FFFF */

        /* Si bit=1, swap pour obtenir le schéma ladder sans if */
        ct_cswap_u64(&r0, &r1, mask);

        /* ladder step */
        r0 = (uint64_t)((__uint128_t)r0 * r1 % mod); /* mul */
        r1 = (uint64_t)((__uint128_t)r1 * r1 % mod); /* square */

        /* swap inverse */
        ct_cswap_u64(&r0, &r1, mask);
    }
    return r0;
}

uint64_t gcd(uint64_t a, uint64_t b) {
    while (b) {
        uint64_t t = b;
        b = a % b;
        a = t;
    }
    return a;
}

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

uint64_t mod_inverse(uint64_t e, uint64_t phi) {
    int64_t x, y;
    int64_t g = extended_gcd((int64_t)e, (int64_t)phi, &x, &y);
    if (g != 1) return 0;
    int64_t r = x % (int64_t)phi;
    if (r < 0) r += (int64_t)phi;
    return (uint64_t)r;
}

int miller_rabin(uint64_t n, int iterations) {
    if (n < 2) return 0;
    if (n == 2 || n == 3) return 1;
    if ((n & 1ULL) == 0) return 0;

    uint64_t d = n - 1;
    int r = 0;
    while ((d & 1ULL) == 0) {
        d >>= 1ULL;
        r++;
    }

    for (int i = 0; i < iterations; i++) {
        uint64_t a = 2 + (uint64_t)(rand() % (int)(n - 3)); /* n ici <= 65535 */
        uint64_t x = mod_exp(a, d, n);

        if (x == 1 || x == n - 1) continue;

        int found = 0;
        for (int j = 0; j < r - 1; j++) {
            x = (uint64_t)((__uint128_t)x * x % n);
            if (x == n - 1) {
                found = 1;
                break;
            }
        }
        if (!found) return 0;
    }
    return 1;
}

uint16_t generate_prime_16bit() {
    uint16_t candidate;
    do {
        candidate = (uint16_t)((rand() % (0xFFFF - 0x8000)) + 0x8000);
        candidate |= 1;
    } while (!miller_rabin(candidate, 20));
    return candidate;
}

int hamming_weight(uint32_t x) {
    int count = 0;
    while (x) {
        count += (int)(x & 1U);
        x >>= 1U;
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

RSAKey rsa_keygen() {
    RSAKey key;
    key.e = 3;

    do { key.p = generate_prime_16bit(); } while (key.p % 3 == 1);
    do { key.q = generate_prime_16bit(); } while (key.q % 3 == 1 || key.q == key.p);

    key.n = (uint32_t)key.p * (uint32_t)key.q;

    uint32_t phi = (uint32_t)(key.p - 1) * (uint32_t)(key.q - 1);
    key.d = (uint32_t)mod_inverse(key.e, phi);

    if (key.d == 0) {
        fprintf(stderr, "Erreur: inverse modulaire introuvable (paramètres invalides)\n");
        exit(1);
    }

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
    uint32_t ciphertexts[100] = {0};
    for (int m = 1; m < 100; m++) {
        ciphertexts[m] = rsa_encrypt((uint32_t)m, key->e, key->n);
    }
    clock_t end = clock();
    double time_encrypt = (double)(end - start) / CLOCKS_PER_SEC;
    printf("Temps pour chiffrer m=1..99 : %.6f secondes\n", time_encrypt);

    uint32_t secret_m = 42;
    uint32_t target_c = rsa_encrypt(secret_m, key->e, key->n);
    printf("Chiffré cible (m=%u) : c = %u\n", secret_m, target_c);

    start = clock();
    for (int m = 1; m < 100; m++) {
        if (ciphertexts[m] == target_c) {
            end = clock();
            double time_attack = (double)(end - start) / CLOCKS_PER_SEC;
            printf("Message retrouvé : m = %d (en %.6f s)\n", m, time_attack);
            break;
        }
    }
}

/* ============================================================
 * Section 3.2 : PKCS#1 v1.5 (variante tronquée)
 * ============================================================ */

typedef struct {
    uint8_t bt;
    uint8_t ps;
    uint8_t message;
} PKCS15_Block;

uint32_t pkcs15_encode(uint8_t message, uint8_t bt) {
    uint8_t ps;
    switch (bt) {
        case 0x00: ps = 0x00; break;
        case 0x01: ps = 0xFF; break;
        case 0x02: ps = (uint8_t)((rand() % 255) + 1); break;
        default:
            fprintf(stderr, "BT invalide\n");
            return 0;
    }
    return ((uint32_t)bt << 24) | ((uint32_t)ps << 16) | ((uint32_t)0x00 << 8) | (uint32_t)message;
}

int pkcs15_decode(uint32_t eb, uint8_t expected_bt) {
    uint8_t bt  = (uint8_t)((eb >> 24) & 0xFF);
    uint8_t ps  = (uint8_t)((eb >> 16) & 0xFF);
    uint8_t sep = (uint8_t)((eb >>  8) & 0xFF);
    uint8_t msg = (uint8_t)(eb & 0xFF);

    if (bt != expected_bt) return -1;
    if (sep != 0x00) return -1;

    switch (bt) {
        case 0x00:
            break;
        case 0x01:
            if (ps != 0xFF) return -1;
            break;
        case 0x02:
            if (ps == 0x00) return -1;
            break;
        default:
            return -1;
    }
    return (int)msg;
}

int pkcs15_oracle(uint32_t c, RSAKey *key) {
    uint32_t decrypted = rsa_decrypt(c, key->d, key->n);
    uint8_t bt  = (uint8_t)((decrypted >> 24) & 0xFF);
    uint8_t ps  = (uint8_t)((decrypted >> 16) & 0xFF);
    uint8_t sep = (uint8_t)((decrypted >>  8) & 0xFF);
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
            printf("  ATTENTION: EB >= n, le chiffrement ne sera pas correct.\n");
            printf("  (eb=%u, n=%u). On saute ce BT.\n", eb, key->n);
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
 * Section 3.3 : Attaque de Bleichenbacher (démonstration simplifiée)
 * ============================================================ */

void demo_bleichenbacher(RSAKey *key) {
    printf("\n=== 3.3 Attaque de Bleichenbacher (démonstration) ===\n");

    uint32_t B = 1U << 16;
    printf("B = 2^16 = %u\n", B);
    printf("Plage PKCS valide : [2B, 3B) = [%u, %u)\n", 2 * B, 3 * B);

    uint8_t message = 0x2A;
    uint32_t eb = pkcs15_encode(message, 0x02);

    if (eb >= key->n) {
        printf("EB >= n, impossible de démontrer l'attaque avec ces paramètres.\n");
        return;
    }

    uint32_t c = rsa_encrypt(eb, key->e, key->n);
    printf("Message original : 0x%02X, EB = 0x%08X, c = %u\n", message, eb, c);

    printf("\nDémonstration de la malléabilité :\n");
    int oracle_calls = 0;
    int conforming_found = 0;

    for (uint32_t s = 1; s < 1000 && conforming_found < 5; s++) {
        uint64_t se = mod_exp(s, key->e, key->n);
        uint64_t c_prime = (uint64_t)((__uint128_t)se * c % key->n);
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

uint8_t mgf(uint8_t x) {
    uint32_t val = (uint32_t)x * 1103515245u + 12345u;
    return (uint8_t)((val >> 16) & 0xFFu);
}

uint32_t oaep_encode(uint8_t message, uint8_t seed) {
    uint8_t db = message;
    uint8_t masked_db = (uint8_t)(db ^ mgf(seed));
    uint8_t masked_seed = (uint8_t)(seed ^ mgf(masked_db));

    /* EM = 0x00 || maskedSeed || maskedDB (3 octets) */
    return ((uint32_t)0x00u << 16) | ((uint32_t)masked_seed << 8) | (uint32_t)masked_db;
}

int oaep_decode(uint32_t em, uint8_t *message) {
    uint8_t first_byte  = (uint8_t)((em >> 16) & 0xFFu);
    uint8_t masked_seed = (uint8_t)((em >>  8) & 0xFFu);
    uint8_t masked_db   = (uint8_t)(em & 0xFFu);

    if (first_byte != 0x00) return -1;

    uint8_t seed = (uint8_t)(masked_seed ^ mgf(masked_db));
    uint8_t db   = (uint8_t)(masked_db ^ mgf(seed));

    *message = db;
    return 0;
}

void demo_oaep(RSAKey *key) {
    printf("\n=== 3.4 RSA OAEP (variante simplifiée) ===\n");

    uint8_t message = 0x2A;
    uint8_t seed = (uint8_t)(rand() & 0xFF);
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
        uint8_t s = (uint8_t)((i * 37 + 13) & 0xFF);
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

static inline double get_time_ns() {
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0) return 0.0;
    return (double)ts.tv_sec * 1e9 + (double)ts.tv_nsec;
}

typedef struct {
    uint64_t squarings;
    uint64_t multiplications;
} OpCount;

/*
 * Square-and-multiply standard (LSB-first)
 * Chaque bit traité fait 1 carré.
 */
uint64_t mod_exp_counted(uint64_t base, uint64_t exp, uint64_t mod, OpCount *ops) {
    if (mod == 0) return 0;

    uint64_t result = 1 % mod;
    base %= mod;

    ops->squarings = 0;
    ops->multiplications = 0;

    while (exp > 0) {
        if (exp & 1ULL) {
            result = (uint64_t)((__uint128_t)result * base % mod);
            ops->multiplications++;
        }
        exp >>= 1ULL;

        if (exp > 0) {
            base = (uint64_t)((__uint128_t)base * base % mod);
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
    printf("Nombre d'itérations pour le timing : %d\n\n", iterations);

    printf("--- Analyse du nombre d'opérations (square-and-multiply classique) ---\n");
    printf("%-15s %-10s %-15s %-15s %-15s\n", "Exposant", "HW", "Carrés", "Multiplications", "Total ops");

    for (int t = 0; t < 5; t++) {
        uint32_t exp = (uint32_t)rand();
        int hw = hamming_weight(exp);
        OpCount ops = {0};
        mod_exp_counted(m, exp, key->n, &ops);
        printf("0x%08X      %-10d %-15" PRIu64 " %-15" PRIu64 " %-15" PRIu64 "\n",
               exp, hw, ops.squarings, ops.multiplications, ops.squarings + ops.multiplications);
    }

    OpCount ops = {0};
    {
        uint32_t exp = 0xFFFFFFFFu;
        mod_exp_counted(m, exp, key->n, &ops);
        printf("0xFFFFFFFF    %-10d %-15" PRIu64 " %-15" PRIu64 " %-15" PRIu64 "  <-- HW max\n",
               32, ops.squarings, ops.multiplications, ops.squarings + ops.multiplications);
    }
    {
        uint32_t exp = 0xA0000000u;
        mod_exp_counted(m, exp, key->n, &ops);
        printf("0xA0000000    %-10d %-15" PRIu64 " %-15" PRIu64 " %-15" PRIu64 "  <-- HW min\n",
               hamming_weight(0xA0000000u), ops.squarings, ops.multiplications, ops.squarings + ops.multiplications);
    }
    {
        uint32_t exp = 0x80000000u;
        mod_exp_counted(m, exp, key->n, &ops);
        printf("0x80000000    %-10d %-15" PRIu64 " %-15" PRIu64 " %-15" PRIu64 "  <-- HW=1\n",
               1, ops.squarings, ops.multiplications, ops.squarings + ops.multiplications);
    }

    printf("\n--- Mesure de timing (1M itérations) ---\n");
    printf("%-25s %-20s %-20s\n", "Exposant", "Classique (ns/op)", "Constant time (ns/op)");

    uint32_t test_exps[] = {0xFFFFFFFFu, 0xA0000000u, 0x55555555u, 0x80000000u, 0x00000003u};
    const char* labels[] = {
        "0xFFFFFFFF (HW=32)",
        "0xA0000000 (HW=2)",
        "0x55555555 (HW=16)",
        "0x80000000 (HW=1)",
        "0x00000003 (HW=2, petit)"
    };

    for (int t = 0; t < 5; t++) {
        volatile uint32_t sink = 0;

        double start = get_time_ns();
        for (int i = 0; i < iterations; i++) {
            sink += (uint32_t)mod_exp(m, test_exps[t], key->n);
        }
        double end = get_time_ns();
        double avg_classic = (end - start) / (double)iterations;

        start = get_time_ns();
        for (int i = 0; i < iterations; i++) {
            sink += (uint32_t)mod_exp_constant_time(m, test_exps[t], key->n);
        }
        end = get_time_ns();
        double avg_ct = (end - start) / (double)iterations;

        printf("%-25s %-20.1f %-20.1f\n", labels[t], avg_classic, avg_ct);
        (void)sink;
    }

    printf("\nObservation : avec l'exponentiation classique, le temps dépend du poids de Hamming.\n");
    printf("Contre-mesure : ladder sans branche dépendante des bits.\n");
}

/* ============================================================
 * Main
 * ============================================================ */

int main() {
    srand((unsigned)time(NULL));

    printf("========================================\n");
    printf("  TP RSA - Implémentation sécurisée\n");
    printf("  M2 Cyberdéfense - École Hexagone\n");
    printf("========================================\n");

    printf("\n=== 2. RSA Textbook 32 bits ===\n");
    RSAKey key = rsa_keygen();
    printf("Clef générée :\n");
    printf("  p = %u, q = %u\n", key.p, key.q);
    printf("  n = %u\n", key.n);
    printf("  e = %u\n", key.e);
    printf("  d = %u\n", key.d);
    printf("  phi(n) = %u\n", (uint32_t)(key.p - 1) * (uint32_t)(key.q - 1));

    uint32_t phi = (uint32_t)(key.p - 1) * (uint32_t)(key.q - 1);
    uint64_t check = (uint64_t)((__uint128_t)key.e * key.d % phi);
    printf("  Vérification e*d mod phi(n) = %" PRIu64 "\n", check);

    uint32_t m = 123456;
    if (m >= key.n) m = key.n - 1;
    uint32_t c = rsa_encrypt(m, key.e, key.n);
    uint32_t m_dec = rsa_decrypt(c, key.d, key.n);
    printf("\nTest : m = %u -> c = %u -> m' = %u %s\n",
           m, c, m_dec, (m == m_dec) ? "✓" : "✗");

    dictionary_attack(&key);
    demo_pkcs15(&key);
    demo_bleichenbacher(&key);
    demo_oaep(&key);
    timing_attack_analysis(&key);

    return 0;
}
