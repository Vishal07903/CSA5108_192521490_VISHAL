/*
 * ============================================================================
 *  EXPERIMENT 24 : RSA - FINDING THE PRIVATE KEY FROM A PUBLIC KEY
 * ============================================================================
 *  Aim
 *  ---
 *  In an RSA system the public key of a given user is e = 31, n = 3599.
 *  What is the private key of this user?
 *  Hint: first use trial-and-error to determine p and q; then use the extended
 *  Euclidean algorithm to find the multiplicative inverse of 31 modulo phi(n).
 *
 *  Method
 *  ------
 *   1. Factor n = p * q by trial division (n is tiny):   3599 = 59 * 61
 *   2. phi(n) = (p-1)(q-1) = 58 * 60 = 3480
 *   3. Check gcd(e, phi) = 1  (31 is prime and does not divide 3480)
 *   4. d = e^-1 mod phi(n): run the extended Euclidean algorithm on (phi, e)
 *      keeping the Bezout coefficients:  e*d + phi*y = 1
 *   5. Private key = {d, n} = {3031, 3599}.   Check  e*d mod phi = 1 :
 *         31 * 3031 = 93961 = 27 * 3480 + 1
 *   6. Demonstrate: encrypt M with the public key, decrypt with the private key.
 *
 *  The program uses the values above by default but accepts any (e, n) whose
 *  modulus fits in 64 bits (trial division is used, so n should be < ~10^12).
 *
 *  Compile :  gcc 24_rsa_private_key.c -o rsa_key
 * ============================================================================
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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


static void read_line(const char *prompt, char *buf, size_t n)
{
    printf("%s", prompt);
    fflush(stdout);
    if (!fgets(buf, (int)n, stdin)) { printf("\n"); exit(0); }
    buf[strcspn(buf, "\r\n")] = '\0';
}

/* extended Euclid with a printed table; returns inverse of e mod phi (0 if none) */
static i64 inverse_with_trace(i64 phi, i64 e)
{
    i64 r0 = phi, r1 = e, t0 = 0, t1 = 1;     /* invariant:  r_i = s_i*phi + t_i*e ; we only track t */
    i64 q, tmp;
    int step = 0;

    printf("\n  Extended Euclidean algorithm for gcd(%lld, %lld)\n", phi, e);
    printf("  step |   r(i-1)   r(i)  |  quotient |   t(i-1)    t(i)\n");
    printf("  -----+-----------------+-----------+---------------------\n");
    printf("   %2d  | %8lld %6lld  |     -     | %8lld %7lld\n", step++, r0, r1, t0, t1);
    while (r1 != 0) {
        q = r0 / r1;
        tmp = r0 - q * r1;  r0 = r1; r1 = tmp;
        tmp = t0 - q * t1;  t0 = t1; t1 = tmp;
        printf("   %2d  | %8lld %6lld  | %9lld | %8lld %7lld\n", step++, r0, r1, q, t0, t1);
    }
    printf("  gcd = %lld\n", r0);
    if (r0 != 1) return 0;
    printf("  Bezout: %lld * %lld + (%lld) * %lld = 1   so e^-1 = %lld = %lld (mod %lld)\n", e, t0,
           (1 - e * t0) / phi, phi, t0, ((t0 % phi) + phi) % phi, phi);
    return ((t0 % phi) + phi) % phi;
}

int main(void)
{
    char buf[128];
    u64 e = 31, n = 3599, p, q, phi, d, m, c, back;
    i64 inv;

    printf("=========================================\n");
    printf("   RSA : PRIVATE KEY FROM (e, n)\n");
    printf("=========================================\n");
    read_line("Public exponent e (Enter = 31): ", buf, sizeof buf);
    if (buf[0]) e = strtoull(buf, NULL, 10);
    read_line("Modulus n (Enter = 3599): ", buf, sizeof buf);
    if (buf[0]) n = strtoull(buf, NULL, 10);
    printf("\nPublic key  PU = {e, n} = {%llu, %llu}\n", e, n);

    /* ---- step 1: factor n by trial division ---- */
    printf("\nSTEP 1  Factor n by trial and error (divide by 2, 3, 5, 7, ... up to sqrt(n))\n");
    p = 0;
    {
        u64 t;
        for (t = 2; t * t <= n; t += (t == 2) ? 1 : 2) {
            if (n % t == 0) { p = t; break; }
            if (t < 60 && is_prime(t)) printf("   %llu does not divide %llu\n", t, n);
        }
    }
    if (!p) { printf("   n is prime (or 1) - not a valid RSA modulus.\n"); return 1; }
    q = n / p;
    printf("   found  %llu divides %llu:   n = %llu x %llu = %llu\n", p, n, p, q, p * q);
    printf("   p and q both prime? %s\n", (is_prime(p) && is_prime(q)) ? "yes" : "NO - n has more than two prime factors");

    /* ---- step 2: phi ---- */
    phi = (p - 1) * (q - 1);
    printf("\nSTEP 2  phi(n) = (p-1)(q-1) = %llu x %llu = %llu\n", p - 1, q - 1, phi);

    /* ---- step 3 ---- */
    printf("\nSTEP 3  gcd(e, phi(n)) = gcd(%llu, %llu) = %llu  -> e %s valid\n", e, phi, gcd_u64(e, phi),
           gcd_u64(e, phi) == 1 ? "is" : "is NOT");
    if (gcd_u64(e, phi) != 1) return 1;

    /* ---- step 4 ---- */
    printf("\nSTEP 4  d = e^-1 mod phi(n) by the extended Euclidean algorithm");
    inv = inverse_with_trace((i64)phi, (i64)e);
    d = (u64)inv;
    printf("\n  d = %llu\n", d);
    printf("  Check: e * d = %llu * %llu = %llu = %llu x %llu + %llu\n", e, d, e * d, (e * d) / phi, phi, (e * d) % phi);
    printf("  library check: modinv() gives %llu\n", modinv(e, phi));

    printf("\n>>> PRIVATE KEY  PR = {d, n} = {%llu, %llu}\n", d, n);

    /* ---- step 5: demo ---- */
    printf("\nSTEP 5  Test the key pair\n");
    read_line("  Enter a message block M < n (Enter = 1234, if n permits): ", buf, sizeof buf);
    m = buf[0] ? strtoull(buf, NULL, 10) : 1234 % n;
    if (m >= n) { printf("  M must be smaller than n.\n"); return 1; }
    c = powmod(m, e, n);
    back = powmod(c, d, n);
    printf("  Encrypt : C = M^e mod n = %llu^%llu mod %llu = %llu\n", m, e, n, c);
    printf("  Decrypt : M = C^d mod n = %llu^%llu mod %llu = %llu   %s\n", c, d, n, back, back == m ? "[OK]" : "[FAIL]");
    return 0;
}
