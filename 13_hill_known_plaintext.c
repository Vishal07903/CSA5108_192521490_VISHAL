/*
 * ============================================================================
 *  EXPERIMENT 13 : KNOWN-PLAINTEXT AND CHOSEN-PLAINTEXT ATTACKS ON THE HILL CIPHER
 * ============================================================================
 *  Aim
 *  ---
 *  The Hill cipher succumbs to a known-plaintext attack if sufficient
 *  plaintext-ciphertext pairs are provided.  It is even easier to solve the
 *  Hill cipher if a chosen-plaintext attack can be mounted.  Implement both.
 *
 *  Theory  (column convention  C = K P  mod 26,  K is n x n)
 *  ------
 *  Stack n known plaintext blocks as columns of P and the corresponding
 *  ciphertext blocks as columns of C:        C = K * P   (mod 26)
 *  If P is invertible mod 26 (gcd(det P, 26) = 1) then
 *                       K = C * P^-1   (mod 26).
 *  With more than n pairs we try different sets of n pairs until one gives an
 *  invertible P, then verify the recovered K on all remaining pairs.
 *
 *  Chosen plaintext: choose the n unit vectors e1=(1,0,..), e2=(0,1,..),...
 *  ("baaa", "abaa", ...).  Then P = I and the ciphertexts ARE the columns of
 *  K - no matrix inversion is needed at all.
 *
 *  Menu
 *   1. Known-plaintext attack on data you type in
 *   2. Known-plaintext demo (random secret key is generated and attacked)
 *   3. Chosen-plaintext demo (attacker has an encryption oracle)
 *
 *  Compile :  gcc 13_hill_known_plaintext.c -o hill_attack
 * ============================================================================
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <time.h>

#define MAXN 5
#define MAXLEN 1024

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

static void mat_mul(Mat a, Mat b, Mat out, int n)
{
    int i, j, k;
    for (i = 0; i < n; i++)
        for (j = 0; j < n; j++) {
            int s = 0;
            for (k = 0; k < n; k++) s += a[i][k] * b[k][j];
            out[i][j] = mod26(s);
        }
}

static void print_mat(const char *name, Mat m, int n)
{
    int i, j;
    for (i = 0; i < n; i++) {
        printf("  %-8s| ", i == n / 2 ? name : "");
        for (j = 0; j < n; j++) printf("%3d ", m[i][j]);
        printf("|\n");
    }
}

static void encrypt_block(Mat k, const int *p, int *c, int n)
{
    int i, j;
    for (i = 0; i < n; i++) {
        int s = 0;
        for (j = 0; j < n; j++) s += k[i][j] * p[j];
        c[i] = mod26(s);
    }
}

/* text -> numbers (letters only); returns count */
static int to_nums(const char *s, int *v)
{
    int n = 0, i;
    for (i = 0; s[i]; i++) if (isalpha((unsigned char)s[i])) v[n++] = toupper((unsigned char)s[i]) - 'A';
    return n;
}

/*
 * Known-plaintext attack.  pt, ct : number arrays of equal length (multiple of n).
 * Tries every choice of n blocks (in order) until P is invertible, solves K,
 * then verifies against all blocks.  Returns 1 on success.
 */
static int known_plaintext(const int *pt, const int *ct, int len, int n, Mat K)
{
    int nb = len / n, idx[MAXN], i, j, tries = 0;

    if (nb < n) { printf("  Need at least %d blocks (%d letters); only %d supplied.\n", n, n * n, len); return 0; }

    /* iterate over combinations of n blocks out of nb (lexicographic) */
    for (i = 0; i < n; i++) idx[i] = i;
    for (;;) {
        Mat P, C, Pinv, Kc;
        int col, row, ok = 1, b;
        tries++;
        for (col = 0; col < n; col++)
            for (row = 0; row < n; row++) {
                P[row][col] = pt[idx[col] * n + row];
                C[row][col] = ct[idx[col] * n + row];
            }
        if (mat_inverse(P, Pinv, n)) {
            mat_mul(C, Pinv, Kc, n);                           /* K = C * P^-1 */
            for (b = 0; b < nb && ok; b++) {                    /* verify on all pairs */
                int c2[MAXN];
                encrypt_block(Kc, pt + b * n, c2, n);
                for (row = 0; row < n; row++) if (c2[row] != ct[b * n + row]) ok = 0;
            }
            if (ok) {
                printf("  Blocks used for the attack: ");
                for (i = 0; i < n; i++) printf("%d ", idx[i] + 1);
                printf("  (after %d attempt%s)\n", tries, tries == 1 ? "" : "s");
                printf("\n  Matrix P (known plaintext blocks as columns):\n");
                for (col = 0; col < n; col++)
                    for (row = 0; row < n; row++) P[row][col] = pt[idx[col] * n + row];
                print_mat("P = ", P, n);
                printf("  Matrix C (matching ciphertext blocks as columns):\n");
                for (col = 0; col < n; col++)
                    for (row = 0; row < n; row++) C[row][col] = ct[idx[col] * n + row];
                print_mat("C = ", C, n);
                mat_inverse(P, Pinv, n);
                printf("  P^-1 mod 26:\n");
                print_mat("P^-1 = ", Pinv, n);
                for (i = 0; i < n; i++) for (j = 0; j < n; j++) K[i][j] = Kc[i][j];
                return 1;
            }
        }
        /* next combination */
        for (i = n - 1; i >= 0 && idx[i] == nb - n + i; i--) ;
        if (i < 0) break;
        idx[i]++;
        for (j = i + 1; j < n; j++) idx[j] = idx[j - 1] + 1;
    }
    printf("  No set of %d blocks gave an invertible plaintext matrix consistent with all data.\n", n);
    return 0;
}

static void random_key(Mat K, int n)
{
    Mat tmp;
    int i, j;
    do {
        for (i = 0; i < n; i++) for (j = 0; j < n; j++) K[i][j] = rand() % 26;
    } while (!mat_inverse(K, tmp, n));
}

static void nums_to_str(const int *v, int len, char *s)
{
    int i;
    for (i = 0; i < len; i++) s[i] = (char)('A' + v[i]);
    s[len] = '\0';
}

int main(void)
{
    char buf[MAXLEN], pts[MAXLEN], cts[MAXLEN];
    int mode, n, i, j, pt[MAXLEN], ct[MAXLEN], len;
    Mat K, got;

    srand((unsigned)time(NULL));
    printf("=========================================\n");
    printf("   HILL CIPHER - KNOWN / CHOSEN PLAINTEXT ATTACK\n");
    printf("=========================================\n");
    printf("1. Known-plaintext attack on my own plaintext/ciphertext\n"
           "2. Known-plaintext demo with a random secret key\n"
           "3. Chosen-plaintext demo (encryption oracle)\n");
    read_line("Mode: ", buf, sizeof buf);
    mode = atoi(buf);

    read_line("Key size n (2-5, Enter = 2): ", buf, sizeof buf);
    n = buf[0] ? atoi(buf) : 2;
    if (n < 2 || n > MAXN) n = 2;

    if (mode == 1) {
        read_line("Known plaintext : ", pts, sizeof pts);
        read_line("Its ciphertext  : ", cts, sizeof cts);
        len = to_nums(pts, pt);
        if (len != to_nums(cts, ct) || len % n) {
            printf("Plaintext and ciphertext must have the same length, a multiple of n.\n");
            return 1;
        }
        printf("\n");
        if (known_plaintext(pt, ct, len, n, got)) {
            printf("\n  RECOVERED KEY:\n");
            print_mat("K = ", got, n);
        }
    } else if (mode == 2) {
        const char *text = "FRIDAYTHEATTACKBEGINSATDAWNSTOPALLUNITSMOVE";
        int tl = (int)strlen(text), blocks;
        random_key(K, n);
        len = 0;
        for (i = 0; i < tl; i++) pt[len++] = text[i] - 'A';
        while (len % n) pt[len++] = 'X' - 'A';
        blocks = len / n;
        for (i = 0; i < blocks; i++) encrypt_block(K, pt + i * n, ct + i * n, n);

        printf("\nSecret key (unknown to the attacker):\n");
        print_mat("K = ", K, n);
        nums_to_str(pt, len, pts); nums_to_str(ct, len, cts);
        printf("\nIntercepted pair\n  plaintext : %s\n  ciphertext: %s\n\n", pts, cts);
        if (known_plaintext(pt, ct, len, n, got)) {
            int same = 1;
            printf("\n  RECOVERED KEY:\n");
            print_mat("K = ", got, n);
            for (i = 0; i < n; i++) for (j = 0; j < n; j++) if (got[i][j] != K[i][j]) same = 0;
            printf("\n  Recovered key equals the secret key: %s\n", same ? "YES - cipher broken" : "NO");
        }
    } else {
        Mat rec;
        random_key(K, n);
        printf("\nSecret key held by the oracle (hidden from attacker):\n");
        print_mat("K = ", K, n);
        printf("\nAttacker submits the %d unit vectors as chosen plaintexts:\n", n);
        for (j = 0; j < n; j++) {
            int p[MAXN] = {0}, c[MAXN];
            p[j] = 1;
            encrypt_block(K, p, c, n);
            printf("  plaintext \"");
            for (i = 0; i < n; i++) putchar('A' + p[i]);
            printf("\" (e%d)  ->  ciphertext \"", j + 1);
            for (i = 0; i < n; i++) putchar('A' + c[i]);
            printf("\"  = column %d of K\n", j + 1);
            for (i = 0; i < n; i++) rec[i][j] = c[i];
        }
        printf("\nColumns collected  =>  RECOVERED KEY (no matrix inversion needed):\n");
        print_mat("K = ", rec, n);
        {
            int same = 1;
            for (i = 0; i < n; i++) for (j = 0; j < n; j++) if (rec[i][j] != K[i][j]) same = 0;
            printf("\n  Recovered key equals the secret key: %s\n", same ? "YES" : "NO");
        }
    }
    return 0;
}
