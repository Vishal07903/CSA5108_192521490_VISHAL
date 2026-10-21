/*
 * ============================================================================
 *  EXPERIMENT 10 : PLAYFAIR ENCRYPTION USING A GIVEN MATRIX
 * ============================================================================
 *  Aim
 *  ---
 *  Using the following Playfair matrix
 *
 *            M  F  H  I/J  K
 *            U  N  O  P    Q
 *            Z  V  W  X    Y
 *            E  L  A  R    G
 *            D  S  T  B    C
 *
 *  encrypt the message:   "Must see you over Cadogan West. Coming at once."
 *
 *  Method
 *  ------
 *   1. Remove spaces / punctuation, upper-case, J -> I.
 *   2. Break into digraphs; insert X between identical letters of a pair;
 *      pad the last single letter with X.
 *   3. Apply the Playfair rules (row -> right, column -> down, rectangle).
 *
 *  The program uses the matrix above by default; it can also be told to
 *  use any other 25-letter matrix typed by the user (to test other cases).
 *
 *  Compile :  gcc 10_playfair_given_matrix.c -o playfair_matrix
 * ============================================================================
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#define MAXLEN 2048

static char M[5][5] = {
    {'M','F','H','I','K'},
    {'U','N','O','P','Q'},
    {'Z','V','W','X','Y'},
    {'E','L','A','R','G'},
    {'D','S','T','B','C'}
};

static void read_line(const char *prompt, char *buf, size_t n)
{
    printf("%s", prompt);
    fflush(stdout);
    if (!fgets(buf, (int)n, stdin)) { printf("\n"); exit(0); }
    buf[strcspn(buf, "\r\n")] = '\0';
}

static void print_matrix(void)
{
    int r, c;
    printf("\n  +---+---+---+---+---+\n");
    for (r = 0; r < 5; r++) {
        printf("  |");
        for (c = 0; c < 5; c++) printf(M[r][c] == 'I' ? "I/J|" : " %c |", M[r][c]);
        printf("\n  +---+---+---+---+---+\n");
    }
}

static int load_matrix(const char *s)
{
    int used[26] = {0}, n = 0, i;
    char tmp[25];
    for (i = 0; s[i] && n < 25; i++) {
        char c = (char)toupper((unsigned char)s[i]);
        if (!isalpha((unsigned char)c)) continue;
        if (c == 'J') c = 'I';
        if (used[c - 'A']) return 0;
        used[c - 'A'] = 1;
        tmp[n++] = c;
    }
    if (n != 25) return 0;
    for (i = 0; i < 25; i++) M[i / 5][i % 5] = tmp[i];
    return 1;
}

static void find_pos(char ch, int *row, int *col)
{
    int r, c;
    if (ch == 'J') ch = 'I';
    for (r = 0; r < 5; r++)
        for (c = 0; c < 5; c++)
            if (M[r][c] == ch) { *row = r; *col = c; return; }
}

static int prepare(const char *in, char *out)
{
    char clean[MAXLEN];
    int n = 0, m = 0, i;
    for (i = 0; in[i]; i++)
        if (isalpha((unsigned char)in[i])) {
            char c = (char)toupper((unsigned char)in[i]);
            clean[n++] = (c == 'J') ? 'I' : c;
        }
    for (i = 0; i < n; i++) {
        out[m++] = clean[i];
        if (i + 1 < n) {
            if (clean[i] == clean[i + 1]) out[m++] = 'X';
            else                          out[m++] = clean[++i];
        } else out[m++] = (clean[i] == 'X') ? 'Z' : 'X';
    }
    out[m] = '\0';
    return m;
}

static void encrypt(const char *pt, char *ct)
{
    int i, m = 0;
    printf("\n  digraph  rule         positions            result\n"
             "  -------  -----------  -------------------  ------\n");
    for (i = 0; pt[i] && pt[i + 1]; i += 2) {
        int r1 = 0, c1 = 0, r2 = 0, c2 = 0;
        char x, y;
        const char *rule;
        find_pos(pt[i], &r1, &c1);
        find_pos(pt[i + 1], &r2, &c2);
        if (r1 == r2)      { x = M[r1][(c1 + 1) % 5]; y = M[r2][(c2 + 1) % 5]; rule = "same row"; }
        else if (c1 == c2) { x = M[(r1 + 1) % 5][c1]; y = M[(r2 + 1) % 5][c2]; rule = "same column"; }
        else               { x = M[r1][c2];           y = M[r2][c1];           rule = "rectangle"; }
        ct[m++] = x; ct[m++] = y;
        printf("   %c%c      %-11s  (%d,%d) and (%d,%d)      %c%c\n",
               pt[i], pt[i + 1], rule, r1 + 1, c1 + 1, r2 + 1, c2 + 1, x, y);
    }
    ct[m] = '\0';
}

static void groups(const char *s)
{
    int i;
    for (i = 0; s[i]; i++) { putchar(s[i]); if (i % 2) putchar(' '); }
    putchar('\n');
}

int main(void)
{
    char msg[MAXLEN], prep[2 * MAXLEN], ct[2 * MAXLEN], buf[256];

    printf("=========================================\n");
    printf("   PLAYFAIR WITH A GIVEN MATRIX\n");
    printf("=========================================\n");
    print_matrix();

    read_line("\nUse a different 25-letter matrix? (type it, or press Enter to keep): ", buf, sizeof buf);
    if (buf[0]) {
        if (load_matrix(buf)) print_matrix();
        else printf("  Not a valid matrix (need 25 distinct letters, I=J). Keeping default.\n");
    }

    read_line("\nEnter message (Enter = \"Must see you over Cadogan West. Coming at once.\"): ", msg, sizeof msg);
    if (!msg[0]) strcpy(msg, "Must see you over Cadogan West. Coming at once.");

    printf("\nOriginal message : %s\n", msg);
    prepare(msg, prep);
    printf("Prepared digraphs: "); groups(prep);
    encrypt(prep, ct);
    printf("\nCIPHERTEXT       : "); groups(ct);
    return 0;
}
