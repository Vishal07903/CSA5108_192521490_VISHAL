/*
 * ============================================================================
 *  EXPERIMENT 28 : A BROKEN VARIANT OF DIFFIE-HELLMAN
 * ============================================================================
 *  Aim
 *  ---
 *  In the Diffie-Hellman protocol each participant selects a secret number x
 *  and sends the other participant  a^x mod q  for some public number a.
 *  What would happen if the participants sent each other  x^a  (x to the power
 *  a)  for some public number a instead?
 *    - Give at least one method Alice and Bob could use to agree on a key.
 *    - Can Eve break your system without finding the secret numbers?
 *    - Can Eve find the secret numbers?
 *
 *  (The printed question lost its superscripts.  We treat it as the standard
 *  textbook problem "x^a mod q", and ALSO analyse the multiplicative reading
 *  "x*a mod q", since both break in the same way.)
 *
 *  ANSWER
 *  ------
 *  Real Diffie-Hellman  Y = a^x mod q  is secure because recovering x from Y is
 *  the DISCRETE LOGARITHM problem - believed infeasible for a large prime q.
 *
 *  Variant 1  Y = x^a mod q :
 *    - Key agreement: pick a public a with gcd(a, q-1) = 1 and let
 *      a' = a^-1 mod (q-1).  Then (x^a)^a' = x^(a a') = x (mod q) by Fermat.
 *      Alice sends Y_A = x_A^a, Bob sends Y_B = x_B^a; Alice computes
 *      x_B = Y_B^a' and Bob x_A = Y_A^a'; the shared key is K = x_A * x_B mod q.
 *      (In the program this public exponent is called k, to keep the name a
 *      for the generator used in the genuine protocol.)
 *    - Eve knows a, q, Y_A, Y_B, so she computes a' EXACTLY like Alice and Bob
 *      do (extended Euclid on a and q-1) and then x_A = Y_A^a', x_B = Y_B^a'.
 *      She finds the SECRET NUMBERS and the key in polynomial time - so yes,
 *      Eve can find the secret numbers (and so also the key).  Raising to a
 *      power is invertible when you know the exponent a; there is no hard
 *      problem protecting x.
 *    - If gcd(a, q-1) = g > 1 the map x -> x^a is g-to-1: Eve gets g
 *      candidates for each secret (g-th roots), still a tiny set.
 *
 *  Variant 2  Y = x*a mod q :
 *    - Key agreement: K = x_A * x_B * a mod q.  Alice computes x_A * Y_B,
 *      Bob computes x_B * Y_A - both equal x_A x_B a mod q.
 *    - Eve computes a^-1 mod q (extended Euclid): x_A = Y_A a^-1, x_B = Y_B a^-1,
 *      or directly K = Y_A * Y_B * a^-1 mod q.  Again she can break it WITHOUT
 *      the secrets (K = Y_A Y_B a^-1) and she can also find the secrets.
 *
 *  Program : builds a 40-bit prime q and a primitive root a, runs
 *    (A) genuine Diffie-Hellman and shows what Eve would have to do
 *        (baby-step giant-step discrete log, ~2^20 steps here - impossible for
 *        a 2048-bit prime),
 *    (B) variant 1  x^a   - and Eve's instant break,
 *    (C) variant 2  x*a   - and Eve's instant break.
 *
 *  Compile :  gcc 28_diffie_hellman_variant.c -o dh_variant
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


/* ---- helpers ------------------------------------------------------------- */
static u64 random_prime(int bits)
{
    u64 lo = 1ULL << (bits - 1), p;
    do { p = lo + rng_next() % lo; p |= 1; } while (!is_prime(p));
    return p;
}

/* distinct prime factors of m by trial division (m < 2^42 -> at most ~2*10^6 steps) */
static int factor_distinct(u64 m, u64 *f)
{
    int n = 0;
    u64 t;
    for (t = 2; t * t <= m; t += (t == 2) ? 1 : 2)
        if (m % t == 0) { f[n++] = t; while (m % t == 0) m /= t; }
    if (m > 1) f[n++] = m;
    return n;
}

static u64 primitive_root(u64 q)
{
    u64 f[16], g;
    int nf = factor_distinct(q - 1, f), i, ok;
    for (g = 2; g < q; g++) {
        ok = 1;
        for (i = 0; i < nf; i++) if (powmod(g, (q - 1) / f[i], q) == 1) { ok = 0; break; }
        if (ok) return g;
    }
    return 0;
}

typedef struct { u64 val, j; } Entry;
static int cmp_entry(const void *a, const void *b)
{
    u64 x = ((const Entry *)a)->val, y = ((const Entry *)b)->val;
    return (x > y) - (x < y);
}

/* baby-step giant-step: find x with a^x = y (mod q) */
static int bsgs(u64 a, u64 y, u64 q, u64 *x_out, u64 *steps)
{
    u64 m = 1, i, j, cur, factor, gamma;
    Entry *tab;
    Entry key, *hit;
    while (m * m < q) m++;
    tab = (Entry *)malloc(sizeof(Entry) * m);
    if (!tab) return 0;
    cur = 1;
    for (j = 0; j < m; j++) { tab[j].val = cur; tab[j].j = j; cur = mulmod(cur, a, q); }
    qsort(tab, (size_t)m, sizeof(Entry), cmp_entry);
    factor = modinv(powmod(a, m, q), q);                      /* a^-m */
    gamma = y;
    *steps = m;
    for (i = 0; i < m; i++) {
        key.val = gamma;
        hit = (Entry *)bsearch(&key, tab, (size_t)m, sizeof(Entry), cmp_entry);
        if (hit) { *x_out = i * m + hit->j; free(tab); *steps += i + 1; return 1; }
        gamma = mulmod(gamma, factor, q);
    }
    free(tab);
    return 0;
}

int main(void)
{
    u64 q, a, xA, xB, YA, YB, KA, KB, t0;
    u64 b, ainv_q1, ainv_q;
    u64 xa_found, steps = 0;
    clock_t c0;

    rng_state ^= (u64)time(NULL) * 0x2545F4914F6CDD1DULL;
    printf("=========================================\n");
    printf("   DIFFIE-HELLMAN AND A BROKEN VARIANT\n");
    printf("=========================================\n");

    q = random_prime(40);
    a = primitive_root(q);
    xA = 2 + rng_next() % (q - 3);
    xB = 2 + rng_next() % (q - 3);
    printf("\nPublic: prime q = %llu (40 bits), generator a = %llu\n", q, a);
    printf("Secret: Alice x_A = %llu     Bob x_B = %llu\n", xA, xB);

    /* ------------------------------ (A) real DH ------------------------------ */
    printf("\n=============== (A) GENUINE DIFFIE-HELLMAN :  Y = a^x mod q ===============\n");
    YA = powmod(a, xA, q); YB = powmod(a, xB, q);
    KA = powmod(YB, xA, q); KB = powmod(YA, xB, q);
    printf("  Alice sends Y_A = %llu      Bob sends Y_B = %llu\n", YA, YB);
    printf("  Alice's key = Y_B^x_A = %llu      Bob's key = Y_A^x_B = %llu   %s\n", KA, KB, KA == KB ? "(equal)" : "(DIFFERENT!)");
    printf("  Eve must solve a discrete logarithm to find x_A from Y_A.\n");
    printf("  (q is only 40 bits, so baby-step giant-step can do it in about 2^20 steps...)\n");
    c0 = clock();
    if (bsgs(a, YA, q, &xa_found, &steps))
        printf("  BSGS found x_A = %llu after about %llu table operations (%.2f s) %s\n", xa_found, steps,
               (double)(clock() - c0) / CLOCKS_PER_SEC, powmod(a, xa_found, q) == YA ? "[valid log]" : "");
    printf("  For a 2048-bit q this needs ~2^1024 steps - infeasible.  THAT is what protects real DH.\n");

    /* ------------------------------ (B) x^a --------------------------------- */
    printf("\n=============== (B) VARIANT 1 :  Y = x^a mod q ===============\n");
    do { b = 3 + 2 * (rng_next() % 1000003); } while (gcd_u64(b, q - 1) != 1);
    printf("  public exponent k = %llu  (chosen with gcd(k, q-1) = 1; this plays the role of the public number 'a' in\n"
           "  the question - renamed k so it is not confused with the generator a above)\n", b);
    YA = powmod(xA, b, q); YB = powmod(xB, b, q);
    printf("  Alice sends Y_A = x_A^k = %llu\n  Bob   sends Y_B = x_B^k = %llu\n", YA, YB);

    ainv_q1 = modinv(b, q - 1);
    printf("\n  KEY AGREEMENT: k^-1 mod (q-1) = %llu   (extended Euclid)\n", ainv_q1);
    {
        u64 xB_at_alice = powmod(YB, ainv_q1, q), xA_at_bob = powmod(YA, ainv_q1, q);
        KA = mulmod(xA, xB_at_alice, q); KB = mulmod(xB, xA_at_bob, q);
        printf("  Alice computes x_B = Y_B^(k^-1) = %llu, key = x_A * x_B = %llu\n", xB_at_alice, KA);
        printf("  Bob   computes x_A = Y_A^(k^-1) = %llu, key = x_B * x_A = %llu    %s\n", xA_at_bob, KB, KA == KB ? "(same key)" : "(DIFFERENT!)");
    }
    printf("\n  EVE sees q, k, Y_A, Y_B only.\n");
    t0 = powmod(YA, ainv_q1, q);
    printf("   - she computes k^-1 mod (q-1) = %llu just as they did\n", ainv_q1);
    printf("   - x_A = Y_A^(k^-1) = %llu   (Alice's real secret %llu) %s\n", t0, xA, t0 == xA ? "<- RECOVERED" : "");
    t0 = powmod(YB, ainv_q1, q);
    printf("   - x_B = Y_B^(k^-1) = %llu   (Bob's real secret %llu) %s\n", t0, xB, t0 == xB ? "<- RECOVERED" : "");
    printf("   - key = x_A * x_B mod q = %llu   %s\n", mulmod(powmod(YA, ainv_q1, q), powmod(YB, ainv_q1, q), q),
           mulmod(powmod(YA, ainv_q1, q), powmod(YB, ainv_q1, q), q) == KA ? "<- Eve has the SAME KEY, in microseconds" : "");
    printf("  => Eve finds the secret numbers and the key with two modular inverses/exponentiations.\n");

    /* ------------------------------ (C) x*a --------------------------------- */
    printf("\n=============== (C) VARIANT 2 :  Y = x*a mod q   (a = generator above) ===============\n");
    YA = mulmod(xA, a, q); YB = mulmod(xB, a, q);
    printf("  Alice sends Y_A = x_A*a = %llu\n  Bob   sends Y_B = x_B*a = %llu\n", YA, YB);
    KA = mulmod(xA, YB, q); KB = mulmod(xB, YA, q);
    printf("\n  KEY AGREEMENT: K = x_A*x_B*a mod q\n  Alice computes x_A * Y_B = %llu\n  Bob   computes x_B * Y_A = %llu   %s\n",
           KA, KB, KA == KB ? "(same key)" : "(DIFFERENT!)");
    ainv_q = modinv(a, q);
    printf("\n  EVE: a^-1 mod q = %llu\n", ainv_q);
    printf("   - WITHOUT the secrets:  K = Y_A * Y_B * a^-1 = %llu   %s\n",
           mulmod(mulmod(YA, YB, q), ainv_q, q), mulmod(mulmod(YA, YB, q), ainv_q, q) == KA ? "<- the shared key" : "<- wrong");
    printf("   - And the secrets themselves: x_A = Y_A * a^-1 = %llu (real %llu), x_B = Y_B * a^-1 = %llu (real %llu)\n",
           mulmod(YA, ainv_q, q), xA, mulmod(YB, ainv_q, q), xB);

    printf("\nANSWERS\n"
           "  * Alice and Bob can agree on a key in both variants (K = x_A x_B, or K = x_A x_B a).\n"
           "  * Eve CAN break the system without finding the secret numbers (variant 2: K = Y_A Y_B a^-1).\n"
           "  * Eve CAN find the secret numbers: the operation (multiply, or raise to a known power) is\n"
           "    easily inverted, unlike exponentiation a^x whose inverse is the discrete logarithm.\n");
    return 0;
}
