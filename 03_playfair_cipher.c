/*
 * ============================================================================
 *  EXPERIMENT 3 : PLAYFAIR CIPHER
 * ============================================================================
 *  Aim
 *  ---
 *  Write a C program for the Playfair algorithm, which is based on a 5x5
 *  matrix of letters constructed using a keyword.  Plaintext is encrypted two
 *  letters at a time using this matrix.
 *
 *  Matrix construction
 *  -------------------
 *  Write the keyword (duplicates removed) row by row, then fill the remaining
 *  cells with the unused letters of the alphabet in order.  I and J share one
 *  cell (J is treated as I).
 *
 *  Preparing the plaintext
 *  -----------------------
 *   - keep letters only, upper-case, J -> I
 *   - split into digraphs; if both letters of a pair are equal, insert a
 *     filler 'X' between them
 *   - if the last digraph has only one letter, append 'X' (or 'Z' if it is X)
 *
 *  Rules for each digraph (p1,p2)
 *   1. same row     -> take the letter to the RIGHT of each (wrap around)
 *   2. same column  -> take the letter BELOW each (wrap around)
 *   3. otherwise    -> rectangle rule: each letter is replaced by the letter in
 *                      its own row and the other letter's column
 *  Decryption uses LEFT / ABOVE instead of RIGHT / BELOW.
 *
 *  Compile :  gcc 03_playfair_cipher.c -o playfair
 * ============================================================================
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#define MAXLEN 2048

static char M[5][5];                         /* the key matrix */

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

/* ---- matrix ------------------------------------------------------------- */
static void build_matrix(const char *keyword)
{
    int used[26] = {0}, pos = 0, i;
    char c;

    for (i = 0; keyword[i]; i++) {
        c = (char)toupper((unsigned char)keyword[i]);
        if (!isalpha((unsigned char)c)) continue;
        if (c == 'J') c = 'I';
        if (!used[c - 'A']) { used[c - 'A'] = 1; M[pos / 5][pos % 5] = c; pos++; }
    }
    for (c = 'A'; c <= 'Z'; c++) {
        if (c == 'J') continue;
        if (!used[c - 'A']) { used[c - 'A'] = 1; M[pos / 5][pos % 5] = c; pos++; }
    }
}

static void print_matrix(void)
{
    int r, c;
    printf("\n  Playfair matrix (I/J share a cell)\n  +---+---+---+---+---+\n");
    for (r = 0; r < 5; r++) {
        printf("  |");
        for (c = 0; c < 5; c++) {
            if (M[r][c] == 'I') printf("I/J|");
            else                printf(" %c |", M[r][c]);
        }
        printf("\n  +---+---+---+---+---+\n");
    }
}

static void find_pos(char ch, int *row, int *col)
{
    int r, c;
    if (ch == 'J') ch = 'I';
    for (r = 0; r < 5; r++)
        for (c = 0; c < 5; c++)
            if (M[r][c] == ch) { *row = r; *col = c; return; }
}

/* ---- plaintext preparation ---------------------------------------------- */
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
            if (clean[i] == clean[i + 1]) out[m++] = 'X';  /* split double letters */
            else                          out[m++] = clean[++i];
        } else {
            out[m++] = (clean[i] == 'X') ? 'Z' : 'X';      /* pad odd length */
        }
    }
    out[m] = '\0';
    return m;
}

/* ---- one digraph --------------------------------------------------------- */
static void do_pair(char a, char b, char *x, char *y, int dir, const char **rule)
{
    int r1 = 0, c1 = 0, r2 = 0, c2 = 0;
    find_pos(a, &r1, &c1);
    find_pos(b, &r2, &c2);

    if (r1 == r2) {                               /* same row */
        *x = M[r1][(c1 + dir + 5) % 5];
        *y = M[r2][(c2 + dir + 5) % 5];
        *rule = "same row";
    } else if (c1 == c2) {                        /* same column */
        *x = M[(r1 + dir + 5) % 5][c1];
        *y = M[(r2 + dir + 5) % 5][c2];
        *rule = "same column";
    } else {                                      /* rectangle */
        *x = M[r1][c2];
        *y = M[r2][c1];
        *rule = "rectangle";
    }
}

static void process(const char *text, char *out, int dir, int verbose)
{
    int i, m = 0;
    char x, y;
    const char *rule;

    if (verbose) printf("\n  digraph -> result   (rule)\n  --------------------------\n");
    for (i = 0; text[i] && text[i + 1]; i += 2) {
        do_pair(text[i], text[i + 1], &x, &y, dir, &rule);
        out[m++] = x; out[m++] = y;
        if (verbose) printf("   %c%c    ->  %c%c      (%s)\n", text[i], text[i + 1], x, y, rule);
    }
    out[m] = '\0';
}

static void print_groups(const char *s)
{
    int i;
    for (i = 0; s[i]; i++) { putchar(s[i]); if (i % 2) putchar(' '); }
    putchar('\n');
}

int main(void)
{
    char key[128], text[MAXLEN], prep[2 * MAXLEN], out[2 * MAXLEN];
    int choice;

    printf("=========================================\n");
    printf("            PLAYFAIR CIPHER\n");
    printf("=========================================\n");

    read_line("Enter keyword: ", key, sizeof key);
    build_matrix(key);
    print_matrix();

    for (;;) {
        printf("\n1. Encrypt\n2. Decrypt\n3. Change keyword\n4. Exit\n");
        choice = read_int("Choice: ");
        if (choice == 4) return 0;

        if (choice == 1) {
            read_line("Enter plaintext: ", text, sizeof text);
            prepare(text, prep);
            printf("\nPrepared digraphs : "); print_groups(prep);
            process(prep, out, +1, 1);
            printf("\nCiphertext        : "); print_groups(out);
        } else if (choice == 2) {
            read_line("Enter ciphertext: ", text, sizeof text);
            prepare(text, prep);
            process(prep, out, -1, 1);
            printf("\nDecrypted text    : "); print_groups(out);
            printf("(remove filler X letters by reading the sense of the message)\n");
        } else if (choice == 3) {
            read_line("Enter new keyword: ", key, sizeof key);
            build_matrix(key);
            print_matrix();
        } else {
            printf("Invalid choice.\n");
        }
    }
}
