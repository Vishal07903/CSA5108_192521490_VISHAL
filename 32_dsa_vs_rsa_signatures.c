/*
 * ============================================================================
 *  EXPERIMENT 32 : DSA SIGNATURES ARE RANDOMISED - WHAT DOES THAT IMPLY?
 * ============================================================================
 *  Aim
 *  ---
 *  Because the value k is generated afresh for each signature, even if the same
 *  message is signed twice on different occasions the DSA signatures will
 *  differ.  This is not true of RSA signatures.  What is the implication of
 *  this difference?
 *
 *  DSA  (FIPS 186):   public: p, q (q | p-1), g of order q;   private x, public y = g^x mod p
 *      sign   : choose random k in [1,q-1]
 *               r = (g^k mod p) mod q
 *               s = k^-1 ( H(m) + x r ) mod q                signature = (r, s)
 *      verify : w = s^-1;  u1 = H(m) w;  u2 = r w;   accept iff  ((g^u1 y^u2) mod p) mod q = r
 *  RSA  (textbook hash-then-sign):   s = H(m)^d mod n,   verify  s^e mod n = H(m)
 *      -> no randomness: the same message ALWAYS yields the same signature.
 *
 *  IMPLICATIONS  (all demonstrated by the program)
 *   1. A DSA signature is not a unique, canonical function of the message.  Two
 *      different valid signatures exist for one message, so a signature cannot be
 *      used as a fingerprint or a deduplication key, and a verifier cannot tell
 *      from the signatures whether two signed documents are the same message.
 *      With RSA the signature is a deterministic "tag" - the same message gives the
 *      same bytes, which is convenient (comparison, caching) but also leaks
 *      whether the same message was signed before.
 *   2. SECURITY DEPENDS ON THE RANDOMNESS.  For every signature k must be
 *      unpredictable, secret and NEVER REUSED.  If the same k signs two messages,
 *      the private key can be computed from the two signatures:
 *         s1 - s2 = k^-1 (H1 - H2)   =>   k = (H1 - H2)(s1 - s2)^-1 mod q
 *         x = (s1 k - H1) r^-1 mod q
 *      (this broke real systems, e.g. Sony PS3 firmware signing).  Even a little
 *      bias in k leaks x over many signatures.  RSA signing needs no per-signature
 *      random number, so it has no such failure mode.
 *   3. DSA therefore needs a good random-number generator on the SIGNER's side at
 *      every signature (or a deterministic derivation of k as in RFC 6979); this
 *      matters for embedded devices and smart cards.
 *   4. Since signatures differ, replay protection cannot rely on "have I seen this
 *      signature before?" - include a nonce / timestamp inside the signed message.
 *      Equally, a signature does not by itself prove WHICH of several signing
 *      events produced it.
 *
 *  The program builds toy parameters (q ~ 31 bits, p ~ 62 bits - far too small for
 *  real use) with SHA-1 as the hash (leftmost bits, as FIPS 186 prescribes) and
 *      A. signs one message several times with DSA  (all different, all valid)
 *      B. signs it several times with RSA            (all identical)
 *      C. reuses k on two messages and recovers the private key
 *
 *  Compile :  gcc 32_dsa_vs_rsa_signatures.c -o dsa_rsa
 * ============================================================================
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* ======================================================================== */
/*  NUMBER-THEORY HELPERS (64-bit, 128-bit intermediates)                   */
/*  gcd, extended Euclid, modular inverse, fast modular exponentiation,     */
/*  deterministic Miller-Rabin primality test, trial-division factoring.    */
/* ======================================================================== */
typedef unsigned long long u64;
typedef long long          i64;
typedef unsigned __int128  u128;

__attribute__((unused)) static u64 gcd_u64(u64 a, u64 b) { while (b) { u64 t = a % b; a = b; b = t; } return a; }

static u64 mulmod(u64 a, u64 b, u64 m) { return (u64)((u128)a * b % m); }

static u64 powmod(u64 b, u64 e, u64 m)
{
    u64 r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = mulmod(r, b, m);
        b = mulmod(b, b, m);
        e >>= 1;
    }
    return r;
}

/* extended Euclid: returns g = gcd(a,b) and x,y with a*x + b*y = g */
static i64 egcd(i64 a, i64 b, i64 *x, i64 *y)
{
    if (b == 0) { *x = 1; *y = 0; return a; }
    i64 x1, y1, g = egcd(b, a % b, &x1, &y1);
    *x = y1;
    *y = x1 - (a / b) * y1;
    return g;
}

/* multiplicative inverse of a modulo m, or 0 if it does not exist */
static u64 modinv(u64 a, u64 m)
{
    i64 x, y, g = egcd((i64)(a % m), (i64)m, &x, &y);
    if (g != 1) return 0;
    x %= (i64)m;
    if (x < 0) x += (i64)m;
    return (u64)x;
}

static int is_prime(u64 n)
{
    static const u64 bases[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
    u64 d, x;
    int r = 0, i, j;
    if (n < 2) return 0;
    for (i = 0; i < 12; i++) { if (n == bases[i]) return 1; if (n % bases[i] == 0) return 0; }
    d = n - 1;
    while ((d & 1) == 0) { d >>= 1; r++; }
    for (i = 0; i < 12; i++) {
        x = powmod(bases[i], d, n);
        if (x == 1 || x == n - 1) continue;
        for (j = 1; j < r; j++) { x = mulmod(x, x, n); if (x == n - 1) break; }
        if (j == r) return 0;
    }
    return 1;
}

/* smallest prime factor by trial division; returns 0 if none up to sqrt */
__attribute__((unused)) static u64 trial_factor(u64 n)
{
    u64 p;
    for (p = 2; p * p <= n; p += (p == 2) ? 1 : 2) if (n % p == 0) return p;
    return 0;
}

/* next prime >= n */
__attribute__((unused)) static u64 next_prime(u64 n) { if (n < 2) n = 2; while (!is_prime(n)) n++; return n; }

/* simple xorshift PRNG for demos (NOT cryptographically secure) */
static u64 rng_state = 0x9E3779B97F4A7C15ULL;
__attribute__((unused)) static u64 rng_next(void)
{
    rng_state ^= rng_state << 13; rng_state ^= rng_state >> 7; rng_state ^= rng_state << 17;
    return rng_state;
}
/* ===================== end of number-theory helpers ====================== */


/* ------------------------------- SHA-1 -------------------------------------- */
typedef unsigned int u32;
typedef unsigned char u8;
#define ROL32(v, n) (((v) << (n)) | ((v) >> (32 - (n))))

static void sha1(const u8 *msg, size_t len, u8 out[20])
{
    u32 h[5] = {0x67452301u, 0xEFCDAB89u, 0x98BADCFEu, 0x10325476u, 0xC3D2E1F0u};
    size_t total = ((len + 8) / 64 + 1) * 64, i;
    u8 *buf = (u8 *)calloc(total, 1);
    u64 bits = (u64)len * 8;
    int j;
    memcpy(buf, msg, len);
    buf[len] = 0x80;
    for (j = 0; j < 8; j++) buf[total - 1 - (size_t)j] = (u8)(bits >> (8 * j));
    for (i = 0; i < total; i += 64) {
        u32 w[80], a = h[0], b = h[1], c = h[2], d = h[3], e = h[4];
        for (j = 0; j < 16; j++) w[j] = ((u32)buf[i + 4 * j] << 24) | ((u32)buf[i + 4 * j + 1] << 16) | ((u32)buf[i + 4 * j + 2] << 8) | buf[i + 4 * j + 3];
        for (j = 16; j < 80; j++) w[j] = ROL32(w[j - 3] ^ w[j - 8] ^ w[j - 14] ^ w[j - 16], 1);
        for (j = 0; j < 80; j++) {
            u32 f, k, t;
            if (j < 20)      { f = (b & c) | (~b & d);           k = 0x5A827999u; }
            else if (j < 40) { f = b ^ c ^ d;                    k = 0x6ED9EBA1u; }
            else if (j < 60) { f = (b & c) | (b & d) | (c & d);  k = 0x8F1BBCDCu; }
            else             { f = b ^ c ^ d;                    k = 0xCA62C1D6u; }
            t = ROL32(a, 5) + f + e + k + w[j];
            e = d; d = c; c = ROL32(b, 30); b = a; a = t;
        }
        h[0] += a; h[1] += b; h[2] += c; h[3] += d; h[4] += e;
    }
    free(buf);
    for (j = 0; j < 5; j++) { out[4 * j] = (u8)(h[j] >> 24); out[4 * j + 1] = (u8)(h[j] >> 16); out[4 * j + 2] = (u8)(h[j] >> 8); out[4 * j + 3] = (u8)h[j]; }
}

/* leftmost nbits (<= 62) of SHA-1(m) as an integer */
static u64 hash_bits(const char *m, int nbits)
{
    u8 d[20];
    u64 v = 0;
    int i;
    sha1((const u8 *)m, strlen(m), d);
    for (i = 0; i < 8; i++) v = (v << 8) | d[i];
    return v >> (64 - nbits);
}

/* ------------------------------- helpers ------------------------------------ */
static void read_line(const char *prompt, char *buf, size_t n)
{
    printf("%s", prompt);
    fflush(stdout);
    if (!fgets(buf, (int)n, stdin)) { printf("\n"); exit(0); }
    buf[strcspn(buf, "\r\n")] = '\0';
}

static u64 rand_range(u64 lo, u64 hi) { return lo + rng_next() % (hi - lo + 1); }          /* inclusive */

static u64 addmod(u64 a, u64 b, u64 m) { return (u64)(((u128)a + b) % m); }
static u64 submod(u64 a, u64 b, u64 m) { return (a % m + m - b % m) % m; }

typedef struct { u64 p, q, g, x, y; } Dsa;

static void dsa_setup(Dsa *k)
{
    u64 q, p, g, h;
    do { q = rand_range(1ULL << 30, (1ULL << 31) - 1) | 1; } while (!is_prime(q));
    for (;;) {                                                     /* p = m*q + 1 prime, about 62 bits */
        u64 m = rand_range(1ULL << 30, (1ULL << 31) - 1) & ~1ULL;
        p = m * q + 1;
        if (p < (1ULL << 61) && is_prime(p)) break;
    }
    for (h = 2;; h++) { g = powmod(h, (p - 1) / q, p); if (g > 1) break; }
    k->p = p; k->q = q; k->g = g;
    k->x = rand_range(1, q - 1);
    k->y = powmod(g, k->x, p);
}

static int dsa_sign_with_k(const Dsa *k, const char *m, u64 kk, u64 *r, u64 *s)
{
    u64 z = hash_bits(m, 31) % k->q;
    *r = powmod(k->g, kk, k->p) % k->q;
    if (*r == 0) return 0;
    *s = mulmod(modinv(kk, k->q), addmod(z, mulmod(k->x, *r, k->q), k->q), k->q);
    return *s != 0;
}

static void dsa_sign(const Dsa *k, const char *m, u64 *r, u64 *s, u64 *kused)
{
    u64 kk;
    do { kk = rand_range(1, k->q - 1); } while (!dsa_sign_with_k(k, m, kk, r, s));
    *kused = kk;
}

static int dsa_verify(const Dsa *k, const char *m, u64 r, u64 s)
{
    u64 z, w, u1, u2, v;
    if (r == 0 || r >= k->q || s == 0 || s >= k->q) return 0;
    z = hash_bits(m, 31) % k->q;
    w = modinv(s, k->q);
    u1 = mulmod(z, w, k->q);
    u2 = mulmod(r, w, k->q);
    v = mulmod(powmod(k->g, u1, k->p), powmod(k->y, u2, k->p), k->p) % k->q;
    return v == r;
}

int main(void)
{
    Dsa key;
    u64 pr, qr, n, phi, e = 65537, d, r[5], s[5], kk[5], zz;
    char msg[200], msg2[] = "Pay Bob 500 rupees";
    int i, same = 0;

    rng_state ^= (u64)time(NULL) * 0x2545F4914F6CDD1DULL;
    printf("=========================================\n");
    printf("   DSA (randomised) vs RSA (deterministic) SIGNATURES\n");
    printf("=========================================\n");

    {
        u8 dg[20]; int j;
        sha1((const u8 *)"abc", 3, dg);
        printf("SHA-1(\"abc\") = ");
        for (j = 0; j < 20; j++) printf("%02x", dg[j]);
        printf("   %s\n", !memcmp(dg, "\xa9\x99\x3e\x36\x47\x06\x81\x6a\xba\x3e\x25\x71\x78\x50\xc2\x6c\x9c\xd0\xd8\x9d", 20) ? "[PASS]" : "[FAIL]");
    }

    dsa_setup(&key);
    printf("\nToy DSA parameters (real DSA uses |p| >= 2048, |q| >= 224 bits):\n");
    printf("  q = %llu   p = %llu   g = %llu\n  private x = %llu   public y = g^x mod p = %llu\n", key.q, key.p, key.g, key.x, key.y);

    do { pr = rand_range(1ULL << 29, (1ULL << 30) - 1) | 1; } while (!is_prime(pr));
    do { qr = rand_range(1ULL << 29, (1ULL << 30) - 1) | 1; phi = (pr - 1) * (qr - 1); } while (!is_prime(qr) || qr == pr || gcd_u64(e, phi) != 1);
    n = pr * qr;
    d = modinv(e, phi);
    { int nb = 0; u64 t = n; while (t) { nb++; t >>= 1; } printf("Toy RSA key: n = %llu (%d bits), e = %llu\n", n, nb, e); }

    read_line("\nMessage to sign (Enter = \"Pay Alice 100 rupees\"): ", msg, sizeof msg);
    if (!msg[0]) strcpy(msg, "Pay Alice 100 rupees");

    /* ----------------------------- A. DSA ----------------------------------- */
    printf("\n=== A. DSA: sign \"%s\" five times ===\n", msg);
    printf("   #   r                s                valid?\n");
    for (i = 0; i < 5; i++) {
        dsa_sign(&key, msg, &r[i], &s[i], &kk[i]);
        printf("   %d   %-16llu %-16llu %s\n", i + 1, r[i], s[i], dsa_verify(&key, msg, r[i], s[i]) ? "yes" : "NO");
    }
    {
        int j, distinct = 1;
        for (i = 0; i < 5; i++) for (j = i + 1; j < 5; j++) if (r[i] == r[j] && s[i] == s[j]) distinct = 0;
        printf("   -> all five signatures %s, yet every one verifies for the SAME message.\n", distinct ? "DIFFER" : "(some equal - improbable)");
    }

    /* ----------------------------- B. RSA ----------------------------------- */
    printf("\n=== B. RSA (hash-then-sign): sign \"%s\" five times ===\n", msg);
    zz = hash_bits(msg, 59) % n;
    printf("   H(m) mod n = %llu\n   #   signature            valid?\n", zz);
    for (i = 0; i < 5; i++) {
        u64 sg = powmod(zz, d, n);
        printf("   %d   %-20llu %s\n", i + 1, sg, powmod(sg, e, n) == zz ? "yes" : "NO");
        s[i] = sg;
    }
    for (i = 1, same = 1; i < 5; i++) if (s[i] != s[0]) same = 0;
    printf("   -> all five RSA signatures are %s.\n", same ? "IDENTICAL (deterministic)" : "different?!");

    /* ----------------------------- C. k reuse ------------------------------- */
    printf("\n=== C. What goes wrong if k is reused (the price of needing randomness) ===\n");
    {
        u64 k = rand_range(1, key.q - 1), r1, s1, r2, s2, z1, z2, kr, xr;
        while (!dsa_sign_with_k(&key, msg, k, &r1, &s1)) k = rand_range(1, key.q - 1);
        if (!dsa_sign_with_k(&key, msg2, k, &r2, &s2)) { printf("unlucky draw, rerun\n"); return 1; }
        printf("   Signer reuses k = %llu for two DIFFERENT messages:\n", k);
        printf("     \"%s\"  ->  (r, s) = (%llu, %llu)\n     \"%s\"  ->  (r, s) = (%llu, %llu)\n", msg, r1, s1, msg2, r2, s2);
        printf("   Both signatures have the SAME r = %llu - the telltale sign of a repeated k.\n", r1);
        z1 = hash_bits(msg, 31) % key.q; z2 = hash_bits(msg2, 31) % key.q;
        if (r1 != r2) { printf("   (r differ - cannot happen)\n"); return 1; }
        {
            u64 ds = submod(s1, s2, key.q);
            if (ds == 0) { printf("   s1 = s2 (identical hashes) - rerun\n"); return 1; }
            kr = mulmod(submod(z1, z2, key.q), modinv(ds, key.q), key.q);
        }
        xr = mulmod(submod(mulmod(s1, kr, key.q), z1, key.q), modinv(r1, key.q), key.q);
        printf("\n   ATTACKER (public data only): k = (H1 - H2)/(s1 - s2) mod q = %llu   %s\n", kr, kr == k ? "[= the secret k]" : "");
        printf("                                x = (s1*k - H1)/r mod q       = %llu   (true private key %llu)  %s\n", xr, key.x, xr == key.x ? "<- PRIVATE KEY RECOVERED" : "");
        printf("   With x the attacker can forge DSA signatures on any message.\n");
    }

    printf("\nIMPLICATIONS\n"
           "  1. A DSA signature is not a unique function of the message: one message has many valid\n"
           "     signatures, so signatures cannot be used as message fingerprints / dedup keys, and\n"
           "     signing is non-repeatable.  RSA signatures are deterministic: same message, same bytes.\n"
           "  2. DSA security rests on a fresh, secret, unpredictable k for EVERY signature - reuse (or\n"
           "     bias) of k reveals the private key; RSA signing needs no per-signature randomness.\n"
           "  3. The signer needs a good random-number generator (or RFC 6979 deterministic k).\n"
           "  4. Replay protection must come from a nonce/timestamp inside the message, not from the\n"
           "     uniqueness of the signature.\n");
    return 0;
}
