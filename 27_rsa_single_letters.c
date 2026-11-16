/*
 * ============================================================================
 *  EXPERIMENT 27 : RSA ON SINGLE LETTERS - AN INSECURE USE OF A SECURE CIPHER
 * ============================================================================
 *  Aim
 *  ---
 *  Bob uses RSA with a very large modulus n whose factorisation cannot be found
 *  in reasonable time.  Alice sends a message to Bob by representing each
 *  alphabetic character as an integer between 0 and 25 (A -> 0, ..., Z -> 25)
 *  and encrypting each number separately with RSA (large e, large n).
 *  Is this method secure?  If not, describe the most efficient attack.
 *
 *  Answer : NOT secure.
 *  ------
 *  Textbook RSA is DETERMINISTIC: the same plaintext always gives the same
 *  ciphertext.  Here there are only 26 possible plaintexts, so there are only 26
 *  possible ciphertext values  c_m = m^e mod n,  m = 0..25.
 *
 *  MOST EFFICIENT ATTACK (needs neither factoring n nor the private key):
 *      1. Eve knows Bob's public key (e, n).
 *      2. She encrypts every letter herself:  table[m] = m^e mod n  (26 modular
 *         exponentiations - milliseconds, whatever the size of n).
 *      3. For each intercepted ciphertext block she looks it up in the table;
 *         the matching entry IS the plaintext letter.
 *  The whole message is recovered with a lookup per character.  (Equivalent to
 *  a dictionary / chosen-plaintext attack; the cipher has degenerated into a
 *  fixed monoalphabetic substitution with a 26-symbol alphabet, which could also
 *  be broken by letter-frequency analysis.)
 *
 *  Fix: never encrypt tiny, guessable plaintexts directly.  Pad / randomise
 *  each block (RSA-OAEP) or encrypt a random session key and use a symmetric
 *  cipher for the message.
 *
 *  The program
 *   1. generates an RSA key with a ~60-bit modulus (big enough that Eve cannot
 *      factor it by hand; the attack never needs to)
 *   2. encrypts a message letter by letter
 *   3. runs the lookup-table attack and prints the recovered text
 *   4. shows the same-letter => same-ciphertext leak
 *   5. shows a randomised-padding version that defeats the table
 *
 *  Compile :  gcc 27_rsa_single_letters.c -o rsa_letters
 * ============================================================================
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
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


static void read_line(const char *prompt, char *buf, size_t n)
{
    printf("%s", prompt);
    fflush(stdout);
    if (!fgets(buf, (int)n, stdin)) { printf("\n"); exit(0); }
    buf[strcspn(buf, "\r\n")] = '\0';
}

static u64 random_prime(int bits)
{
    u64 lo = 1ULL << (bits - 1), p;
    do { p = lo + rng_next() % lo; p |= 1; } while (!is_prime(p));
    return p;
}

int main(void)
{
    char msg[256], letters[256], dec[256];
    u64 p, q, n, phi, e = 65537, d, C[256], table[26];
    int len = 0, i, m, hits = 0;

    rng_state ^= (u64)time(NULL) * 0x2545F4914F6CDD1DULL;
    printf("=========================================\n");
    printf("   RSA ENCRYPTING ONE LETTER AT A TIME\n");
    printf("=========================================\n");

    do {
        p = random_prime(30); q = random_prime(30);
        phi = (p - 1) * (q - 1);
    } while (p == q || gcd_u64(e, phi) != 1);
    n = p * q;
    d = modinv(e, phi);
    printf("\nBob's public key : (e, n) = (%llu, %llu)\n", e, n);
    printf("(Bob's private d and the primes are secret and are used ONLY to show Bob can decrypt)\n");

    read_line("\nAlice's message (letters only, Enter = MEETMEATSUNRISE): ", msg, sizeof msg);
    if (!msg[0]) strcpy(msg, "MEETMEATSUNRISE");
    for (i = 0; msg[i]; i++) if (isalpha((unsigned char)msg[i])) letters[len++] = (char)toupper((unsigned char)msg[i]);
    letters[len] = '\0';
    printf("Plaintext letters: %s\n", letters);

    /* ---- Alice encrypts each letter separately ---- */
    printf("\nAlice encrypts each letter separately:  C = m^e mod n\n  letter  m   ciphertext\n");
    for (i = 0; i < len; i++) {
        m = letters[i] - 'A';
        C[i] = powmod((u64)m, e, n);
        printf("    %c    %2d   %llu\n", letters[i], m, C[i]);
    }

    /* ---- Bob decrypts (sanity check) ---- */
    for (i = 0; i < len; i++) dec[i] = (char)('A' + (int)powmod(C[i], d, n));
    dec[len] = '\0';
    printf("\nBob decrypts with d: %s   %s\n", dec, strcmp(dec, letters) == 0 ? "[OK]" : "[FAIL]");

    /* ---- Eve's attack ---- */
    printf("\n------------------- EVE (knows only e, n and the ciphertexts) -------------------\n");
    printf("Step 1: encrypt all 26 letters with Bob's public key to build a table\n");
    for (m = 0; m < 26; m++) table[m] = powmod((u64)m, e, n);
    for (m = 0; m < 26; m++) printf("  %c -> %llu\n", 'A' + m, table[m]);

    printf("\nStep 2: look every intercepted block up in the table\n  ");
    for (i = 0; i < len; i++) {
        int found = -1;
        for (m = 0; m < 26; m++) if (table[m] == C[i]) found = m;
        dec[i] = found >= 0 ? (char)('A' + found) : '?';
        if (found >= 0) hits++;
    }
    dec[len] = '\0';
    printf("recovered: %s   (%d of %d blocks matched)\n", dec, hits, len);
    printf("Eve read the whole message with 26 encryptions and %d lookups - no factoring, no private key.\n", len);

    printf("\nThe repeated-letter leak: identical letters give identical ciphertext blocks, so even\n"
           "without the table Eve sees the letter pattern (like a monoalphabetic substitution cipher).\n");

    /* ---- the fix: randomised padding ---- */
    printf("\n------------------------ A (toy) FIX: RANDOMISED PADDING ------------------------\n");
    printf("Encode each letter as  m' = r*32 + m  with a fresh random r (about 2^28 choices), then RSA.\n");
    printf("  letter  ciphertext\n");
    for (i = 0; i < len && i < 8; i++) {
        u64 r = rng_next() % (1ULL << 28), mp = r * 32 + (u64)(letters[i] - 'A');
        C[i] = powmod(mp, e, n);
        printf("    %c    %llu\n", letters[i], C[i]);
    }
    {
        int found = 0;
        for (i = 0; i < len && i < 8; i++) for (m = 0; m < 26; m++) if (table[m] == C[i]) found++;
        printf("Eve's 26-entry table now matches %d of the blocks shown - the dictionary attack fails.\n", found);
    }
    printf("(Real systems use RSA-OAEP, or RSA only to transport a random symmetric key.)\n");
    return 0;
}
