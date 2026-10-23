/*
 * ============================================================================
 *  EXPERIMENT 12 : HILL CIPHER  (encryption and decryption with calculations)
 * ============================================================================
 *  Aim
 *  ---
 *  Encrypt the message "meet me at the usual place at ten rather than eight
 *  oclock" using the Hill cipher with the key
 *
 *             | 9  4 |
 *         K = | 5  7 |
 *
 *   a. Show your calculations and the result.
 *   b. Show the calculations for the corresponding decryption of the
 *      ciphertext to recover the original plaintext.
 *
 *  Algorithm  (column-vector convention, as in Stallings)
 *  ---------
 *  Letters are numbered a=0 .. z=25.  The plaintext is cut into blocks of n
 *  letters (n = size of the key matrix; pad with 'x' if needed).  For each
 *  block P (a column vector):
 *
 *        C = K * P  (mod 26)                     (encryption)
 *        P = K^-1 * C  (mod 26)                  (decryption)
 *
 *  K^-1 exists only if gcd(det K, 26) = 1.  For a 2x2 key:
 *        det = 9*7 - 4*5 = 43 = 17 (mod 26),   17^-1 = 23 (mod 26)
 *        K^-1 = 23 * |  7 -4 |  =  | 5 12 |   (mod 26)
 *                    | -5  9 |     | 15 25 |
 *
 *  The program handles any n x n key (2..6) using Gauss-Jordan elimination
 *  modulo 26 to find the inverse.  Press Enter at the prompts to run the exact
 *  experiment given above.
 *
 *  Compile :  gcc 12_hill_cipher.c -o hill
 * ============================================================================
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#define MAXN 6
#define MAXLEN 2048

typedef int Mat[MAXN][MAXN];

static void read_line(const char *prompt, char *buf, size_t n)
{
    printf("%s", prompt);
    fflush(stdout);
    if (!fgets(buf, (int)n, stdin)) { printf("\n"); exit(0); }
    buf[strcspn(buf, "\r\n")] = '\0';
}

static int mod26(int x) { x %= 26; return x < 0 ? x + 26 : x; }

static int gcd(int a, int b) { a = a < 0 ? -a : a; while (b) { int t = a % b; a = b; b = t; } return a; }

static int inv26(int a)
{
    int x;
    a = mod26(a);
    for (x = 1; x < 26; x++) if ((a * x) % 26 == 1) return x;
    return -1;
}

/* determinant (integer, by cofactor expansion; n <= 6 is tiny) */
static long det_rec(Mat m, int n)
{
    long d = 0;
    int c, i, j, k;
    Mat sub;
    if (n == 1) return m[0][0];
    if (n == 2) return (long)m[0][0] * m[1][1] - (long)m[0][1] * m[1][0];
    for (c = 0; c < n; c++) {
        for (i = 1; i < n; i++) {
            k = 0;
            for (j = 0; j < n; j++) if (j != c) sub[i - 1][k++] = m[i][j];
        }
        d += ((c % 2) ? -1 : 1) * (long)m[0][c] * det_rec(sub, n - 1);
    }
    return d;
}

/* inverse mod 26 by Gauss-Jordan; returns 0 if not invertible */
static int mat_inverse(Mat a, Mat out, int n)
{
    int aug[MAXN][2 * MAXN], i, j, k;
    for (i = 0; i < n; i++)
        for (j = 0; j < n; j++) { aug[i][j] = mod26(a[i][j]); aug[i][n + j] = (i == j); }

    for (i = 0; i < n; i++) {
        int piv = -1, iv;
        for (k = i; k < n; k++) if (gcd(aug[k][i], 26) == 1) { piv = k; break; }
        if (piv < 0) return 0;
        if (piv != i)
            for (j = 0; j < 2 * n; j++) { int t = aug[i][j]; aug[i][j] = aug[piv][j]; aug[piv][j] = t; }
        iv = inv26(aug[i][i]);
        for (j = 0; j < 2 * n; j++) aug[i][j] = mod26(aug[i][j] * iv);
        for (k = 0; k < n; k++) {
            int f;
            if (k == i) continue;
            f = aug[k][i];
            for (j = 0; j < 2 * n; j++) aug[k][j] = mod26(aug[k][j] - f * aug[i][j]);
        }
    }
    for (i = 0; i < n; i++) for (j = 0; j < n; j++) out[i][j] = aug[i][n + j];
    return 1;
}

static void print_mat(const char *name, Mat m, int n)
{
    int i, j;
    for (i = 0; i < n; i++) {
        printf("  %-8s", i == n / 2 ? name : "");
        printf("| ");
        for (j = 0; j < n; j++) printf("%3d ", m[i][j]);
        printf("|\n");
    }
}

/* apply key to text, printing the calculation of every block */
static void hill(const char *in, char *out, Mat k, int n, int verbose, const char *label)
{
    int len = (int)strlen(in), b, i, j, m = 0;
    if (verbose) printf("\n  %s - block calculations (C = K*P mod 26)\n", label);

    for (b = 0; b < len; b += n) {
        int p[MAXN], c[MAXN];
        for (i = 0; i < n; i++) p[i] = in[b + i] - 'a';

        if (verbose) {
            printf("  block %2d  \"", b / n + 1);
            for (i = 0; i < n; i++) putchar(in[b + i]);
            printf("\"  P = (");
            for (i = 0; i < n; i++) printf("%s%d", i ? "," : "", p[i]);
            printf(")\n");
        }
        for (i = 0; i < n; i++) {
            int sum = 0;
            if (verbose) printf("             row %d: ", i + 1);
            for (j = 0; j < n; j++) {
                sum += k[i][j] * p[j];
                if (verbose) printf("%s%d*%d", j ? " + " : "", k[i][j], p[j]);
            }
            c[i] = mod26(sum);
            if (verbose) printf(" = %d = %d (mod 26) -> '%c'\n", sum, c[i], 'a' + c[i]);
        }
        for (i = 0; i < n; i++) out[m++] = (char)('a' + c[i]);
    }
    out[m] = '\0';
}

int main(void)
{
    Mat K = {{9, 4}, {5, 7}}, Kinv;
    int n = 2, i, j;
    char buf[MAXLEN], msg[MAXLEN], clean[MAXLEN], ct[MAXLEN], pt[MAXLEN];
    long d;
    int len = 0;

    printf("=========================================\n");
    printf("         HILL CIPHER  (C = K.P mod 26)\n");
    printf("=========================================\n");

    read_line("Key size n (2-6, Enter = 2): ", buf, sizeof buf);
    if (buf[0]) n = atoi(buf);
    if (n < 2 || n > MAXN) n = 2;

    if (buf[0] && n != 2) {
        printf("Enter the %dx%d key row by row:\n", n, n);
        for (i = 0; i < n; i++)
            for (j = 0; j < n; j++) { printf("  K[%d][%d] = ", i + 1, j + 1); fflush(stdout);
                                      if (scanf("%d", &K[i][j]) != 1) return 1; }
        getchar();
    } else {
        n = 2;
        read_line("Use the key [9 4; 5 7]? (Enter = yes, or type 4 numbers a b c d): ", buf, sizeof buf);
        if (buf[0]) sscanf(buf, "%d %d %d %d", &K[0][0], &K[0][1], &K[1][0], &K[1][1]);
    }

    printf("\nKey matrix K:\n");
    print_mat("K = ", K, n);

    d = det_rec(K, n);
    printf("\ndet(K) = %ld = %d (mod 26),  gcd(det,26) = %d\n", d, mod26((int)d), gcd((int)d, 26));
    if (!mat_inverse(K, Kinv, n)) {
        printf("The key is NOT invertible mod 26 - it cannot be used for the Hill cipher.\n");
        return 1;
    }
    printf("det^-1 = %d (mod 26)\nK^-1 (mod 26):\n", inv26(mod26((int)d)));
    print_mat("K^-1 = ", Kinv, n);

    /* verify K * K^-1 = I */
    {
        int ok = 1;
        for (i = 0; i < n; i++)
            for (j = 0; j < n; j++) {
                int s = 0, k;
                for (k = 0; k < n; k++) s += K[i][k] * Kinv[k][j];
                if (mod26(s) != (i == j)) ok = 0;
            }
        printf("Check K * K^-1 = I (mod 26): %s\n", ok ? "OK" : "FAILED");
    }

    read_line("\nEnter plaintext (Enter = \"meet me at the usual place at ten rather than eight oclock\"): ",
              msg, sizeof msg);
    if (!msg[0]) strcpy(msg, "meet me at the usual place at ten rather than eight oclock");

    for (i = 0; msg[i]; i++) if (isalpha((unsigned char)msg[i])) clean[len++] = (char)tolower((unsigned char)msg[i]);
    clean[len] = '\0';
    while (len % n) clean[len++] = 'x';                 /* pad with x */
    clean[len] = '\0';

    printf("\nPlaintext (letters only, padded): %s  (%d letters = %d blocks)\n", clean, len, len / n);

    hill(clean, ct, K, n, 1, "ENCRYPTION");
    printf("\nCIPHERTEXT : ");
    for (i = 0; ct[i]; i++) { putchar(toupper((unsigned char)ct[i])); if (i % n == n - 1) putchar(' '); }

    printf("\n\n----------------------------------------------------------------\n");
    hill(ct, pt, Kinv, n, 1, "DECRYPTION (P = K^-1 * C mod 26)");
    printf("\nRECOVERED PLAINTEXT : %s\n", pt);
    printf("Matches the original: %s\n", strcmp(pt, clean) == 0 ? "YES" : "NO");
    return 0;
}
