/*
 * ============================================================================
 *  EXPERIMENT 26 : RSA - IS IT SAFE TO CHANGE (e, d) BUT KEEP THE MODULUS n ?
 * ============================================================================
 *  Aim
 *  ---
 *  In an RSA public-key scheme each user has a public key e and a private key d.
 *  Suppose Bob leaks his private key.  Rather than generating a new modulus, he
 *  decides to generate a new public and a new private key (keeping n).  Is this
 *  safe?
 *
 *  Answer : NO.
 *  ------
 *  Knowing (e, d, n) lets anyone FACTOR n:
 *      e*d = 1 (mod phi(n))   so   k = e*d - 1  is a multiple of phi(n).
 *  Write k = 2^t * r with r odd.  For a random base g, the sequence
 *      g^r, g^(2r), g^(4r), ..., g^(2^t r) = g^k = 1  (mod n)
 *  ends in 1; if some term x is a "non-trivial square root of 1" (x^2 = 1 but
 *  x != +-1 mod n) then gcd(x-1, n) is a prime factor of n.  For a random g
 *  this works with probability >= 1/2, so a few tries always succeed.
 *  Once p and q are known, phi(n) is known, and for Bob's NEW public key e'
 *  anybody simply computes  d' = e'^-1 mod phi(n)  - the new private key.
 *  Changing the exponents but keeping n therefore gives NO protection; Bob must
 *  generate a completely new modulus (new p and q).
 *
 *  The program
 *   1. generates Bob's RSA key (n, e, d)  and shows he "leaks" d
 *   2. Eve factors n from (n, e, d) with the algorithm above, printing the trace
 *   3. Bob picks a new e', computes d', and publishes e'
 *   4. Eve computes d'' from e' and the factorisation - equal to Bob's d'
 *   5. Eve reads a message encrypted for Bob's "new" key
 *
 *  Compile :  gcc 26_rsa_leaked_private_key.c -o rsa_leak
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


static u64 random_prime(int bits)
{
    u64 lo = 1ULL << (bits - 1), p;
    do { p = lo + rng_next() % lo; p |= 1; } while (!is_prime(p));
    return p;
}

/* g^e mod n with a 128-bit exponent (e*d - 1 can exceed 64 bits) */
static u64 powmod128(u64 g, u128 e, u64 n)
{
    u64 r = 1 % n;
    g %= n;
    while (e) {
        if (e & 1) r = mulmod(r, g, n);
        g = mulmod(g, g, n);
        e >>= 1;
    }
    return r;
}

static void print_u128(u128 v)
{
    char b[48];
    int i = 0;
    if (v == 0) { printf("0"); return; }
    while (v) { b[i++] = (char)('0' + (int)(v % 10)); v /= 10; }
    while (i--) putchar(b[i]);
}

/* factor n given a valid pair (e, d); returns a non-trivial factor of n, or 0 */
static u64 factor_from_ed(u64 n, u64 e, u64 d, int verbose)
{
    u128 r = (u128)e * d - 1;                   /* k = e*d - 1, a multiple of phi(n) */
    int t = 0, attempt, i;

    while ((r & 1) == 0) { r >>= 1; t++; }      /* k = 2^t * r with r odd */
    if (verbose) { printf("  k = e*d - 1 = 2^%d * r   with r = ", t); print_u128(r); printf(" (odd)\n"); }

    for (attempt = 1; attempt <= 40; attempt++) {
        u64 g = 2 + rng_next() % (n - 3), x, prev, gg = gcd_u64(g, n);
        if (gg != 1) { if (verbose) printf("  attempt %d: g = %llu shares a factor with n directly: %llu\n", attempt, g, gg); return gg; }
        x = powmod128(g, r, n);
        if (verbose) printf("  attempt %d: g = %-12llu  g^r mod n = %llu\n", attempt, g, x);
        if (x == 1 || x == n - 1) { if (verbose) printf("             g^r = +-1  -> useless base, try another g\n"); continue; }
        for (i = 1; i <= t; i++) {
            prev = x;
            x = mulmod(x, x, n);
            if (verbose) printf("             square #%d: %llu\n", i, x);
            if (x == 1) {
                u64 f = gcd_u64(prev - 1, n);
                if (verbose) printf("             %llu^2 = 1 but %llu != +-1  =>  non-trivial square root of 1\n"
                                    "             gcd(%llu - 1, n) = %llu\n", prev, prev, prev, f);
                if (f > 1 && f < n) return f;
                break;
            }
            if (x == n - 1) break;
        }
    }
    return 0;
}

int main(void)
{
    u64 p, q, n, phi, e, d, e2, d2, d_eve, pf, qf, m, c, got;
    char buf[64];

    rng_state ^= (u64)time(NULL) * 0x2545F4914F6CDD1DULL;
    printf("=========================================\n");
    printf("   RSA : BOB LEAKS d AND KEEPS THE MODULUS\n");
    printf("=========================================\n");

    /* ---- Bob's key ---- */
    e = 65537;
    do {
        p = random_prime(30); q = random_prime(30);
        phi = (p - 1) * (q - 1);
    } while (p == q || gcd_u64(e, phi) != 1);
    n = p * q;
    d = modinv(e, phi);
    printf("\nBob's secret primes : p = %llu, q = %llu   (never published)\n", p, q);
    printf("Bob's public key    : (e, n) = (%llu, %llu)\n", e, n);
    printf("Bob's private key   : d = %llu    <-- LEAKED\n", d);

    /* ---- Eve factors n ---- */
    printf("\n---- Eve (knows n, e and the leaked d) factors n ----\n");
    pf = factor_from_ed(n, e, d, 1);
    if (!pf) { printf("unlucky - run again\n"); return 1; }
    qf = n / pf;
    printf("\n  Eve finds  n = %llu x %llu   (Bob's real primes: %llu, %llu) %s\n", pf, qf, p, q,
           ((pf == p && qf == q) || (pf == q && qf == p)) ? "[correct]" : "[wrong]");

    /* ---- Bob 'fixes' the problem by choosing new exponents ---- */
    do { e2 = 3 + 2 * (rng_next() % 100000); } while (gcd_u64(e2, phi) != 1);
    d2 = modinv(e2, phi);
    printf("\n---- Bob 'repairs' the situation: same n, NEW keys ----\n");
    printf("  new public key  e' = %llu   (published)\n  new private key d' = %llu   (kept secret)\n", e2, d2);

    /* ---- Eve derives the new private key ---- */
    d_eve = modinv(e2, (pf - 1) * (qf - 1));
    printf("\n---- Eve computes d' from e' and the factors ----\n");
    printf("  phi(n) = (%llu-1)(%llu-1) = %llu\n  d'(Eve) = e'^-1 mod phi(n) = %llu   %s Bob's new private key\n",
           pf, qf, (pf - 1) * (qf - 1), d_eve, d_eve == d2 ? "= EXACTLY" : "!=");

    /* ---- Alice sends something to Bob ---- */
    snprintf(buf, sizeof buf, "%u", 4242424u);
    m = strtoull(buf, NULL, 10) % n;
    c = powmod(m, e2, n);
    got = powmod(c, d_eve, n);
    printf("\nAlice encrypts M = %llu with Bob's NEW public key:  C = %llu\n", m, c);
    printf("Eve decrypts with her computed key:            M = %llu   %s\n", got, got == m ? "[SUCCESS - message read]" : "[fail]");
    printf("\nConclusion: NOT safe. Once d leaks, n is factored, so every key pair that uses this n is\n"
           "compromised. Bob must generate a completely new modulus (new p and q).\n");
    return 0;
}
