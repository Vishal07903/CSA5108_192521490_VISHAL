/*
 * ============================================================================
 *  EXPERIMENT 5 : AFFINE CAESAR CIPHER
 * ============================================================================
 *  Aim
 *  ---
 *  Write a C program for the affine Caesar cipher, a generalisation of the
 *  Caesar cipher.  For each plaintext letter p, the ciphertext letter is
 *
 *        C = E([a, b], p) = (a*p + b) mod 26
 *
 *  A basic requirement of any encryption algorithm is that it be one-to-one:
 *  if p != q then E(k,p) != E(k,q), otherwise decryption is impossible.
 *  The affine cipher is not one-to-one for all values of a.
 *  Example: a = 2, b = 3  ->  E([2,3],0) = E([2,3],13) = 3.
 *
 *  Questions
 *  ---------
 *  a. Are there any limitations on the value of b?
 *     NO.  b is just a Caesar shift, so every b in 0..25 gives a valid
 *     (one-to-one) cipher as long as a is valid.  (b = 0 and a = 1 gives the
 *     identity mapping, which is valid but useless.)
 *
 *  b. Which values of a are not allowed?
 *     E is one-to-one  <=>  gcd(a, 26) = 1.  Since 26 = 2 * 13, a must be
 *     odd and not a multiple of 13.  Allowed (12 values):
 *         1 3 5 7 9 11 15 17 19 21 23 25
 *     NOT allowed (14 values): 0 and every even number 2..24, plus 13.
 *     Number of distinct keys = 12 * 26 = 312.
 *
 *  Decryption:   p = a^(-1) * (C - b) mod 26,  where a*a^(-1) = 1 (mod 26).
 *
 *  The program evaluates both questions, then encrypts / decrypts.
 *
 *  Compile :  gcc 05_affine_cipher.c -o affine
 * ============================================================================
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#define MAXLEN 2048

static void read_line(const char *prompt, char *buf, size_t n)
{
    printf("%s", prompt);
    fflush(stdout);
    if (!fgets(buf, (int)n, stdin)) { printf("\n"); exit(0); }
    buf[strcspn(buf, "\r\n")] = '\0';
}

static int read_int(const char *prompt)
{
    char b[64];
    read_line(prompt, b, sizeof b);
    return atoi(b);
}

static int gcd(int x, int y) { while (y) { int t = x % y; x = y; y = t; } return x; }

/* modular inverse of a mod m by brute force (m is only 26); -1 if none */
static int mod_inverse(int a, int m)
{
    int x;
    a %= m;
    for (x = 1; x < m; x++)
        if ((a * x) % m == 1) return x;
    return -1;
}

/* returns 1 if E(p) = (a*p+b) mod 26 is a permutation; prints first collision */
static int is_one_to_one(int a, int b, int verbose)
{
    int seen[26], p;
    for (p = 0; p < 26; p++) seen[p] = -1;
    for (p = 0; p < 26; p++) {
        int c = (a * p + b) % 26;
        if (seen[c] != -1) {
            if (verbose)
                printf("  NOT one-to-one: E(%d) = E(%d) = %d\n", seen[c], p, c);
            return 0;
        }
        seen[c] = p;
    }
    return 1;
}

static void analysis(void)
{
    int a, b, ok;
    printf("\n--- (a) Limitations on b -------------------------------------\n");
    for (a = 1; a < 26; a += 2) {
        if (gcd(a, 26) != 1) continue;
        ok = 1;
        for (b = 0; b < 26; b++) ok &= is_one_to_one(a, b, 0);
        printf("  a = %2d : all 26 values of b (0..25) give a one-to-one map : %s\n",
               a, ok ? "YES" : "NO");
    }
    printf("  => b has NO restriction; any b in 0..25 may be used.\n");

    printf("\n--- (b) Values of a that are NOT allowed ---------------------\n");
    printf("  a | gcd(a,26) | one-to-one? | inverse of a\n");
    printf("  --+-----------+-------------+-------------\n");
    for (a = 0; a < 26; a++) {
        int g = gcd(a, 26);
        ok = is_one_to_one(a, 0, 0);
        printf(" %2d |    %2d     |     %-3s     |", a, g, ok ? "yes" : "NO");
        if (ok) printf("   %d\n", mod_inverse(a, 26)); else printf("   none\n");
    }
    printf("\n  Allowed a     : ");
    for (a = 0; a < 26; a++) if (gcd(a, 26) == 1) printf("%d ", a);
    printf("\n  Not allowed a : ");
    for (a = 0; a < 26; a++) if (gcd(a, 26) != 1) printf("%d ", a);
    printf("\n\n  Worked example from the question (a = 2, b = 3):\n");
    is_one_to_one(2, 3, 1);
}

static void affine(const char *in, char *out, int a, int b, int decrypt)
{
    int ainv = mod_inverse(a, 26), i;
    for (i = 0; in[i]; i++) {
        if (isalpha((unsigned char)in[i])) {
            int base = isupper((unsigned char)in[i]) ? 'A' : 'a';
            int x = in[i] - base, y;
            if (!decrypt) y = (a * x + b) % 26;
            else          y = (((ainv * (x - b)) % 26) + 26) % 26;
            out[i] = (char)(base + y);
        } else out[i] = in[i];
    }
    out[i] = '\0';
}

static void get_key(int *a, int *b)
{
    for (;;) {
        *a = read_int("Enter a (must be coprime with 26): ");
        if (gcd(*a, 26) == 1) break;
        printf("  a = %d is NOT allowed (gcd(a,26) = %d); cipher would not be one-to-one.\n",
               *a, gcd(*a, 26));
    }
    *b = ((read_int("Enter b (any integer)             : ") % 26) + 26) % 26;
}

int main(void)
{
    char text[MAXLEN], out[MAXLEN];
    int choice, a, b, i;

    printf("=========================================\n");
    printf("   AFFINE CAESAR CIPHER  C = (a*p+b) mod 26\n");
    printf("=========================================\n");

    for (;;) {
        printf("\n1. Encrypt\n2. Decrypt\n3. Analyse allowed values of a and b\n4. Exit\n");
        choice = read_int("Choice: ");
        if (choice == 4) return 0;
        if (choice == 3) { analysis(); continue; }
        if (choice != 1 && choice != 2) { printf("Invalid choice.\n"); continue; }

        get_key(&a, &b);
        printf("\nUsing a = %d, b = %d, a^-1 = %d\n  plain : ", a, b, mod_inverse(a, 26));
        for (i = 0; i < 26; i++) printf("%c ", 'A' + i);
        printf("\n  cipher: ");
        for (i = 0; i < 26; i++) printf("%c ", 'A' + (a * i + b) % 26);
        printf("\n");

        if (choice == 1) {
            read_line("\nEnter plaintext : ", text, sizeof text);
            affine(text, out, a, b, 0);
            printf("Ciphertext      : %s\n", out);
        } else {
            read_line("\nEnter ciphertext: ", text, sizeof text);
            affine(text, out, a, b, 1);
            printf("Plaintext       : %s\n", out);
        }
    }
}
