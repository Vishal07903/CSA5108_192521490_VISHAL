/*
 * ============================================================================
 *  EXPERIMENT 6 : BREAKING AN AFFINE CIPHER BY FREQUENCY ANALYSIS
 * ============================================================================
 *  Aim
 *  ---
 *  A ciphertext has been generated with an affine cipher  C = (a*p + b) mod 26.
 *  The most frequent letter of the ciphertext is 'B' and the second most
 *  frequent is 'U'.  Break the code.
 *
 *  Method
 *  ------
 *  In English the most frequent letters are E (1st) and T (2nd).  Assume
 *       E (4)  -> B (1)           T (19) -> U (20)
 *  which gives two congruences in two unknowns:
 *       4a  + b = 1   (mod 26)
 *       19a + b = 20  (mod 26)
 *  Subtract:  15a = 19 (mod 26).  15^-1 = 7 (mod 26)  ->  a = 19*7 = 3.
 *  Then b = 1 - 4*3 = -11 = 15 (mod 26).   KEY: a = 3, b = 15.
 *  (gcd(3,26)=1 so the key is valid.)
 *
 *  The program does this for ANY two cipher letters.  It tries a list of
 *  likely plaintext pairs (E,T), (T,E), (E,A), (A,E), (E,O), ... , solves
 *  for every valid (a,b) by testing the congruences, discards keys with
 *  gcd(a,26) != 1 and, if a ciphertext is supplied, decrypts it with each
 *  candidate and ranks them by how English-like they are.
 *
 *  Modes
 *    1. Enter the two most frequent cipher letters only  (e.g. B and U)
 *    2. Enter a whole ciphertext - the program finds the two most frequent
 *       letters itself, then attacks it.
 *    3. Self test with a generated ciphertext
 *
 *  Compile :  gcc 06_affine_break.c -o affine_break -lm
 * ============================================================================
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <math.h>

#define MAXLEN 4096

static const double ENG[26] = {   /* English letter frequencies (%) */
    8.17, 1.49, 2.78, 4.25, 12.70, 2.23, 2.02, 6.09, 6.97, 0.15, 0.77, 4.03, 2.41,
    6.75, 7.51, 1.93, 0.10, 5.99, 6.33, 9.06, 2.76, 0.98, 2.36, 0.15, 1.97, 0.07 };

/* likely (most frequent, 2nd most frequent) plaintext pairs, tried in order */
static const char *PAIRS[] = { "ET", "TE", "EA", "AE", "EO", "OE", "ER", "ET", "TA", "AT", "EN", "NE", NULL };

static void read_line(const char *prompt, char *buf, size_t n)
{
    printf("%s", prompt);
    fflush(stdout);
    if (!fgets(buf, (int)n, stdin)) { printf("\n"); exit(0); }
    buf[strcspn(buf, "\r\n")] = '\0';
}

static int gcd(int x, int y) { while (y) { int t = x % y; x = y; y = t; } return x; }

static int mod_inverse(int a, int m)
{
    int x;
    for (x = 1; x < m; x++) if ((a * x) % m == 1) return x;
    return -1;
}

static void decrypt(const char *in, char *out, int a, int b)
{
    int ainv = mod_inverse(a, 26), i;
    for (i = 0; in[i]; i++) {
        if (isalpha((unsigned char)in[i])) {
            int base = isupper((unsigned char)in[i]) ? 'A' : 'a';
            int y = (((ainv * ((in[i] - base) - b)) % 26) + 26) % 26;
            out[i] = (char)(base + y);
        } else out[i] = in[i];
    }
    out[i] = '\0';
}

static void encrypt(const char *in, char *out, int a, int b)
{
    int i;
    for (i = 0; in[i]; i++) {
        if (isalpha((unsigned char)in[i])) {
            int base = isupper((unsigned char)in[i]) ? 'A' : 'a';
            out[i] = (char)(base + (a * (in[i] - base) + b) % 26);
        } else out[i] = in[i];
    }
    out[i] = '\0';
}

/* chi-square distance between text and English (smaller = more English) */
static double chi2(const char *s)
{
    int cnt[26] = {0}, n = 0, i;
    double x = 0;
    for (i = 0; s[i]; i++) if (isalpha((unsigned char)s[i])) { cnt[toupper((unsigned char)s[i]) - 'A']++; n++; }
    if (!n) return 1e9;
    for (i = 0; i < 26; i++) {
        double e = n * ENG[i] / 100.0, d = cnt[i] - e;
        x += d * d / e;
    }
    return x;
}

static void top_two(const char *s, char *first, char *second)
{
    int cnt[26] = {0}, i, a = 0, b = 1;
    for (i = 0; s[i]; i++) if (isalpha((unsigned char)s[i])) cnt[toupper((unsigned char)s[i]) - 'A']++;
    printf("\n  Cipher letter frequencies:\n");
    for (i = 0; i < 26; i++) if (cnt[i]) printf("    %c : %3d  %.*s\n", 'A' + i, cnt[i], cnt[i] > 60 ? 60 : cnt[i], "############################################################");
    a = 0; b = -1;
    for (i = 1; i < 26; i++) if (cnt[i] > cnt[a]) a = i;
    for (i = 0; i < 26; i++) if (i != a && (b < 0 || cnt[i] > cnt[b])) b = i;
    *first = (char)('A' + a);
    *second = (char)('A' + b);
}

typedef struct { int a, b, p1, p2; double score; } Cand;

static int cmp_cand(const void *x, const void *y)
{
    double d = ((const Cand *)x)->score - ((const Cand *)y)->score;
    return (d > 0) - (d < 0);
}

static void attack(char c1, char c2, const char *cipher)
{
    Cand cand[256];
    int nc = 0, i, a, b;
    char out[MAXLEN];

    printf("\n  Most frequent cipher letter = %c, second = %c\n", c1, c2);
    for (i = 0; PAIRS[i]; i++) {
        int p1 = PAIRS[i][0] - 'A', p2 = PAIRS[i][1] - 'A';
        int x1 = c1 - 'A', x2 = c2 - 'A', dup = 0, j;
        for (j = 0; j < nc; j++) if (cand[j].p1 == p1 && cand[j].p2 == p2) dup = 1;
        if (dup) continue;

        printf("\n  Assume %c -> %c and %c -> %c :\n", PAIRS[i][0], c1, PAIRS[i][1], c2);
        printf("     %2d*a + b = %2d (mod 26)\n     %2d*a + b = %2d (mod 26)\n", p1, x1, p2, x2);
        int found = 0;
        for (a = 1; a < 26; a++) {
            if (gcd(a, 26) != 1) continue;
            for (b = 0; b < 26; b++)
                if ((a * p1 + b) % 26 == x1 && (a * p2 + b) % 26 == x2) {
                    printf("     -> solution a = %d, b = %d  (a^-1 = %d)\n", a, b, mod_inverse(a, 26));
                    cand[nc].a = a; cand[nc].b = b; cand[nc].p1 = p1; cand[nc].p2 = p2;
                    if (cipher && cipher[0]) { decrypt(cipher, out, a, b); cand[nc].score = chi2(out); }
                    else cand[nc].score = 0;
                    nc++; found = 1;
                }
        }
        if (!found) printf("     -> no valid key (a would not be coprime with 26)\n");
    }

    if (nc == 0) { printf("\n  No candidate keys.\n"); return; }

    if (cipher && cipher[0]) qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    printf("\n==================== CANDIDATE KEYS%s ====================\n",
           (cipher && cipher[0]) ? " (best first)" : "");
    for (i = 0; i < nc; i++) {
        printf(" #%d  a = %2d, b = %2d   (%c->%c, %c->%c)", i + 1, cand[i].a, cand[i].b,
               'A' + cand[i].p1, c1, 'A' + cand[i].p2, c2);
        if (cipher && cipher[0]) {
            decrypt(cipher, out, cand[i].a, cand[i].b);
            printf("  chi2=%.1f\n      %.70s%s\n", cand[i].score, out, strlen(out) > 70 ? "..." : "");
        } else printf("\n");
    }
    printf("\nDecryption formula for the first key: P = %d * (C - %d) mod 26\n",
           mod_inverse(cand[0].a, 26), cand[0].b);
}

int main(void)
{
    char text[MAXLEN], c1, c2, buf[64], enc[MAXLEN];
    int mode;

    printf("=========================================\n");
    printf("   BREAKING THE AFFINE CIPHER\n");
    printf("=========================================\n");
    printf("1. I know the two most frequent cipher letters (e.g. B and U)\n"
           "2. I have a full ciphertext\n"
           "3. Self-test (encrypt a sample with a=3,b=15 and break it)\n");
    read_line("Mode: ", buf, sizeof buf);
    mode = atoi(buf);

    if (mode == 1) {
        read_line("Most frequent cipher letter : ", buf, sizeof buf); c1 = (char)toupper((unsigned char)buf[0]);
        read_line("Second most frequent letter : ", buf, sizeof buf); c2 = (char)toupper((unsigned char)buf[0]);
        attack(c1, c2, NULL);
    } else if (mode == 2) {
        read_line("Enter ciphertext: ", text, sizeof text);
        top_two(text, &c1, &c2);
        attack(c1, c2, text);
    } else {
        const char *sample = "The affine cipher is a type of monoalphabetic substitution cipher where each "
                             "letter in an alphabet is mapped to its numeric equivalent and then encrypted "
                             "using a simple mathematical function and converted back to a letter";
        encrypt(sample, enc, 3, 15);
        printf("\nSample ciphertext (a=3, b=15):\n%s\n", enc);
        top_two(enc, &c1, &c2);
        attack(c1, c2, enc);
    }
    return 0;
}
