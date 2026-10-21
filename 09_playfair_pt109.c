/*
 * ============================================================================
 *  EXPERIMENT 9 : PLAYFAIR - THE PT-109 MESSAGE
 * ============================================================================
 *  Aim
 *  ---
 *  When the PT-109 American patrol boat, under the command of Lieutenant John
 *  F. Kennedy, was sunk by a Japanese destroyer, a message was received at an
 *  Australian wireless station in Playfair code:
 *
 *        KXJEY UREBE ZWEHE WRYTU HEYFS
 *        KREHE GOYFI WTTTU OLKSY CAJPO
 *        BOTEI ZONTX BYBNT GONEY CUZWR
 *        GDSON SXBOU YWRHE BAAHY USEDQ
 *
 *  The key used was "royal new zealand navy".  Decrypt the message.
 *
 *  Method
 *  ------
 *   1. Build the 5x5 Playfair matrix from the keyword ROYALNEWZEALANDNAVY
 *      (duplicates dropped, I/J share a cell).
 *   2. Decrypt every digraph:  same row -> letter to the LEFT,
 *      same column -> letter ABOVE, rectangle -> swap the columns.
 *   3. Remove filler 'X' letters / read the words.
 *
 *  Extra: if the key is not known, the program can run a keyword search
 *  (dictionary attack) over a built-in candidate list and rank each decryption
 *  by how many common English words it contains.
 *
 *  Compile :  gcc 09_playfair_pt109.c -o pt109
 * ============================================================================
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#define MAXLEN 1024

static const char *CIPHERTEXT =
    "KXJEY UREBE ZWEHE WRYTU HEYFS "
    "KREHE GOYFI WTTTU OLKSY CAJPO "
    "BOTEI ZONTX BYBNT GONEY CUZWR "
    "GDSON SXBOU YWRHE BAAHY USEDQ";

static char M[5][5];

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
    printf("\n  +---+---+---+---+---+\n");
    for (r = 0; r < 5; r++) {
        printf("  |");
        for (c = 0; c < 5; c++) printf(M[r][c] == 'I' ? "I/J|" : " %c |", M[r][c]);
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

/* decrypt one digraph; returns rule name */
static const char *dec_pair(char a, char b, char *x, char *y)
{
    int r1 = 0, c1 = 0, r2 = 0, c2 = 0;
    find_pos(a, &r1, &c1);
    find_pos(b, &r2, &c2);
    if (r1 == r2) { *x = M[r1][(c1 + 4) % 5]; *y = M[r2][(c2 + 4) % 5]; return "row"; }
    if (c1 == c2) { *x = M[(r1 + 4) % 5][c1]; *y = M[(r2 + 4) % 5][c2]; return "column"; }
    *x = M[r1][c2]; *y = M[r2][c1];
    return "rectangle";
}

static int clean(const char *in, char *out)
{
    int n = 0, i;
    for (i = 0; in[i]; i++)
        if (isalpha((unsigned char)in[i])) out[n++] = (char)toupper((unsigned char)in[i]);
    out[n] = '\0';
    return n;
}

static void decrypt(const char *ct, char *pt, int verbose)
{
    int i, n = (int)strlen(ct), m = 0;
    char x, y;
    for (i = 0; i + 1 < n; i += 2) {
        const char *rule = dec_pair(ct[i], ct[i + 1], &x, &y);
        pt[m++] = x; pt[m++] = y;
        if (verbose) printf("   %c%c -> %c%c  (%s)\n", ct[i], ct[i + 1], x, y, rule);
    }
    pt[m] = '\0';
}

/* score = how many common words appear in the decrypted string */
static int word_score(const char *s)
{
    static const char *W[] = { "THE", "AND", "BOAT", "LOST", "ACTION", "STRAIT", "MILES", "COVE",
                               "CREW", "REQUEST", "INFORMATION", "TWELVE", "ANY", "NINE", "ONE",
                               "SEND", "HELP", "ENEMY", "ISLAND", "NEAR", NULL };
    int sc = 0, i;
    for (i = 0; W[i]; i++) if (strstr(s, W[i])) sc += (int)strlen(W[i]);
    return sc;
}

int main(void)
{
    char ct[MAXLEN], pt[MAXLEN], buf[256];
    int i, n;
    static const char *CAND[] = { "ROYALNEWZEALANDNAVY", "ROYALNAVY", "KENNEDY", "AUSTRALIA",
                                  "PATROLBOAT", "NAVY", "PLAYFAIR", "JAPANESE", "SOLOMON",
                                  "ROYALNEWZEALANDAIRFORCE", NULL };

    printf("=========================================\n");
    printf("   PLAYFAIR - PT-109 MESSAGE DECRYPTION\n");
    printf("=========================================\n");

    n = clean(CIPHERTEXT, ct);
    printf("\nCiphertext (%d letters, %d digraphs):\n  %s\n", n, n / 2, CIPHERTEXT);

    printf("\n--- Part 1: decrypt with the known key \"royal new zealand navy\" ---\n");
    build_matrix("royal new zealand navy");
    print_matrix();
    printf("\nDigraph-by-digraph decryption:\n");
    decrypt(ct, pt, 1);

    printf("\nRaw plaintext      : ");
    for (i = 0; pt[i]; i++) { putchar(pt[i]); if (i % 5 == 4) putchar(' '); }
    printf("\n\nReading the plaintext with word breaks (X = filler / full stop):\n\n");
    printf("    PT BOAT ONE OH NINE LOST IN ACTION IN BLACKE(TT) STRAIT TWO MILES\n"
           "    SW MERESU COVE X CREW OF TWELVE X REQUEST ANY INFORMATION X\n");
    printf("\n  i.e.  \"PT boat 109 lost in action in Blackett Strait, two miles SW of\n"
           "         Meresu Cove. Crew of twelve. Request any information.\"\n");
    printf("\n  Note: the received digraph TT cannot occur in a genuine Playfair\n"
           "  message (a digraph never has two equal letters), so it is a garble in\n"
           "  transmission; it decrypts to SS, which is why BLACKETT reads BLACKESS.\n");

    printf("\n--- Part 2: dictionary attack (key unknown) ---\n");
    for (i = 0; CAND[i]; i++) {
        build_matrix(CAND[i]);
        decrypt(ct, pt, 0);
        printf("  key %-26s score %3d   %.40s...\n", CAND[i], word_score(pt), pt);
    }

    printf("\nThe key with the highest score is the correct one.\n");
    printf("\nTry your own keyword (blank to quit): ");
    fflush(stdout);
    while (fgets(buf, sizeof buf, stdin)) {
        buf[strcspn(buf, "\r\n")] = '\0';
        if (!buf[0]) break;
        build_matrix(buf);
        decrypt(ct, pt, 0);
        printf("  => %s\n  Another keyword (blank to quit): ", pt);
        fflush(stdout);
    }
    printf("\n");
    return 0;
}
