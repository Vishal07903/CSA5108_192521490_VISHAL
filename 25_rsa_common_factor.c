/*
 * ============================================================================
 *  EXPERIMENT 25 : RSA - A PLAINTEXT BLOCK THAT SHARES A FACTOR WITH n
 * ============================================================================
 *  Aim
 *  ---
 *  We have a set of blocks encoded with the RSA algorithm and we do not have
 *  the private key.  Assume n = p*q and e is the public key.  Suppose someone
 *  tells us they know that one of the plaintext blocks has a common factor with
 *  n.  Does this help us in any way?
 *
 *  Answer : YES - it breaks the whole system.
 *  ------
 *  Let the block M share the prime p with n (so p | M, M != 0).  Then
 *        C = M^e mod n   =>   C = M^e (mod p) = 0 (mod p)
 *  so p divides C as well, and therefore
 *        gcd(C, n) = p            (it cannot be n unless M is a multiple of n).
 *  Computing a gcd is fast (Euclid), so for each intercepted ciphertext block
 *  we compute gcd(C_i, n); the block with gcd > 1 reveals p.  Then
 *        q = n / p,   phi(n) = (p-1)(q-1),   d = e^-1 mod phi(n)
 *  and ALL the blocks can be decrypted - not only the special one.
 *
 *  (For a random block the chance of sharing a factor with n is only about
 *  1/p + 1/q, negligible for large primes; but if the information is true -
 *  e.g. a block that is a multiple of p - the attack costs one gcd per block.)
 *
 *  The program
 *   1. generates an RSA key (primes ~ 2^30) and a message of several blocks,
 *      one of which is deliberately a multiple of p
 *   2. encrypts every block with the public key only
 *   3. plays the attacker: knowing only (e, n) and the ciphertext blocks it
 *      computes gcd(C_i, n) for every block, finds p, builds the private key
 *      and decrypts everything
 *
 *  Compile :  gcc 25_rsa_common_factor.c -o rsa_common
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


#define NBLK 8

static u64 random_prime(int bits)
{
    u64 lo = 1ULL << (bits - 1), p;
    do { p = lo + rng_next() % lo; p |= 1; } while (!is_prime(p));
    return p;
}

int main(void)
{
    u64 p, q, n, phi, e = 65537, d;
    u64 M[NBLK], C[NBLK], R[NBLK];
    int i, special = 5, found = -1;
    u64 pf, qf, phif, df;

    rng_state ^= (u64)time(NULL) * 0x2545F4914F6CDD1DULL;
    printf("=========================================\n");
    printf("   RSA : PLAINTEXT BLOCK SHARING A FACTOR WITH n\n");
    printf("=========================================\n");

    /* ---- key generation (the legitimate user) ---- */
    do {
        p = random_prime(30);
        q = random_prime(30);
        phi = (p - 1) * (q - 1);
    } while (p == q || gcd_u64(e, phi) != 1);
    n = p * q;
    d = modinv(e, phi);
    printf("\nUser's key (secret p, q are NOT known to the attacker):\n");
    printf("  p = %llu\n  q = %llu\n  n = %llu\n  public key  (e, n) = (%llu, %llu)\n", p, q, n, e, n);

    /* ---- the message: 8 blocks, block 6 is a multiple of p ---- */
    for (i = 0; i < NBLK; i++) {
        do { M[i] = 2 + rng_next() % (n - 3); } while (M[i] % p == 0 || M[i] % q == 0);
    }
    M[special] = p * (2 + rng_next() % 1000);              /* shares the factor p with n */
    printf("\nPlaintext blocks (sender):\n");
    for (i = 0; i < NBLK; i++) printf("  M%d = %-20llu%s\n", i + 1, M[i], i == special ? "  <- multiple of p  (shares a factor with n)" : "");
    for (i = 0; i < NBLK; i++) C[i] = powmod(M[i], e, n);
    printf("\nIntercepted ciphertext blocks  C = M^e mod n :\n");
    for (i = 0; i < NBLK; i++) printf("  C%d = %llu\n", i + 1, C[i]);

    /* ---- the attack ---- */
    printf("\n--------------- ATTACKER (knows only e, n and the C_i) ---------------\n");
    printf("Compute gcd(C_i, n) for every block:\n");
    for (i = 0; i < NBLK; i++) {
        u64 g = gcd_u64(C[i], n);
        printf("  gcd(C%d, n) = %llu%s\n", i + 1, g, g > 1 ? "   <-- non-trivial factor of n!" : "");
        if (g > 1 && g < n && found < 0) { found = i; pf = g; }
    }
    if (found < 0) { printf("No block shares a factor with n.\n"); return 1; }

    qf = n / pf;
    phif = (pf - 1) * (qf - 1);
    df = modinv(e, phif);
    printf("\nBlock %d gives the factor p' = %llu, so q' = n / p' = %llu\n", found + 1, pf, qf);
    printf("  (p', q') %s the user's real primes\n", ((pf == p && qf == q) || (pf == q && qf == p)) ? "ARE" : "are NOT");
    printf("  phi(n) = (p'-1)(q'-1) = %llu\n  d = e^-1 mod phi(n) = %llu   (user's real d = %llu) %s\n",
           phif, df, d, df == d ? "- identical" : "");

    printf("\nDecrypting ALL blocks with the recovered private key:\n");
    for (i = 0; i < NBLK; i++) {
        R[i] = powmod(C[i], df, n);
        printf("  C%d -> %-20llu %s\n", i + 1, R[i], R[i] == M[i] ? "[matches original]" : "[MISMATCH]");
    }
    printf("\nConclusion: knowing that ONE block shares a factor with n lets the attacker factor n\n"
           "with a single gcd and read every block - it helps enormously.\n");
    return 0;
}
