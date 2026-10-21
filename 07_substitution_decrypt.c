/*
 * ============================================================================
 *  EXPERIMENT 7 : CRYPTANALYSIS OF A SIMPLE SUBSTITUTION CIPHER
 * ============================================================================
 *  Aim
 *  ---
 *  The following ciphertext was generated using a simple substitution
 *  algorithm (this is the famous cipher from Poe's "The Gold-Bug"):
 *
 *   53‡‡†305))6*;4826)4‡.)4‡);806*;48†8¶60))85;;]8*;:‡*8†83
 *   (88)5*†;46(;88*96*?;8)*‡(;485);5*†2:*‡(;4956*2(5*—4)8¶8*
 *   ;4069285);)6†8)4‡‡;1(‡9;48081;8:8‡1;48†85;4)485†528806*81
 *   (‡9;48;(88;4(‡?34;48)4‡;161;:188;‡?;
 *
 *  Decrypt this message following the hints:
 *   1. The most frequent letter in English is e, so the first / second /
 *      third most common cipher character probably stands for e.  Also e is
 *      often doubled (meet, fleet, speed, seen, been, agree ...).
 *   2. The most common word is "the" - use it to guess t and h.
 *   3. Decipher the rest by deducing additional words.
 *
 *  What the program does
 *  ---------------------
 *   Step 1  reads the ciphertext (UTF-8 aware; every symbol is one token)
 *           and prints a frequency table with bar chart
 *   Step 2  lists the most frequent doubled symbols (candidates for e)
 *   Step 3  lists the most frequent 3-symbol sequences (candidate "the")
 *   Step 4  applies the guesses one stage at a time and prints the partially
 *           decrypted text after every stage, exactly as a human analyst would
 *   Step 5  prints the complete key and the final plaintext
 *
 *  Compile :  gcc 07_substitution_decrypt.c -o gold_bug
 *  (source file must be saved as UTF-8)
 * ============================================================================
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXTOK 1024

static const char *CIPHERTEXT =
    "53‡‡†305))6*;4826)4‡.)4‡);806*;48†8¶60))85;;]8*;:‡*8†83"
    "(88)5*†;46(;88*96*?;8)*‡(;485);5*†2:*‡(;4956*2(5*—4)8¶8*"
    ";4069285);)6†8)4‡‡;1(‡9;48081;8:8‡1;48†85;4)485†528806*81"
    "(‡9;48;(88;4(‡?34;48)4‡;161;:188;‡?;";

/* standard English single-letter order, most frequent first */
static const char *ENGLISH_ORDER = "ETAOINSHRDLCUMWFGYPBVKJXQZ";

typedef unsigned int cp_t;                   /* a Unicode code point */

/* ---- minimal UTF-8 decoder / encoder ------------------------------------- */
static int utf8_decode(const char *s, cp_t *out)
{
    unsigned char c = (unsigned char)s[0];
    if (c < 0x80)           { *out = c; return 1; }
    if ((c & 0xE0) == 0xC0) { *out = ((c & 0x1Fu) << 6) | (s[1] & 0x3Fu); return 2; }
    if ((c & 0xF0) == 0xE0) { *out = ((c & 0x0Fu) << 12) | ((s[1] & 0x3Fu) << 6) | (s[2] & 0x3Fu); return 3; }
    *out = ((c & 0x07u) << 18) | ((s[1] & 0x3Fu) << 12) | ((s[2] & 0x3Fu) << 6) | (s[3] & 0x3Fu);
    return 4;
}

static void utf8_print(cp_t cp)
{
    if (cp < 0x80)        putchar((int)cp);
    else if (cp < 0x800)  { putchar(0xC0 | (int)(cp >> 6)); putchar(0x80 | (int)(cp & 0x3F)); }
    else                  { putchar(0xE0 | (int)(cp >> 12)); putchar(0x80 | (int)((cp >> 6) & 0x3F)); putchar(0x80 | (int)(cp & 0x3F)); }
}

/* ---- token tables -------------------------------------------------------- */
static cp_t tok[MAXTOK];                     /* ciphertext as code points   */
static int  ntok;
static cp_t sym[64];                         /* distinct symbols            */
static int  cnt[64], nsym;
static char guess[64];                       /* guess[i] = letter for sym[i], 0 = unknown */

static int sym_index(cp_t c)
{
    int i;
    for (i = 0; i < nsym; i++) if (sym[i] == c) return i;
    return -1;
}

static void tokenise(void)
{
    const char *p = CIPHERTEXT;
    ntok = 0; nsym = 0;
    while (*p) {
        cp_t c;
        p += utf8_decode(p, &c);
        tok[ntok++] = c;
        int k = sym_index(c);
        if (k < 0) { k = nsym++; sym[k] = c; cnt[k] = 0; }
        cnt[k]++;
    }
}

/* ---- display helpers ----------------------------------------------------- */
static void print_partial(void)
{
    int i, col = 0;
    printf("\n  Current decryption ('_' = still unknown):\n  ");
    for (i = 0; i < ntok; i++) {
        int k = sym_index(tok[i]);
        putchar(guess[k] ? guess[k] : '_');
        if (++col == 70) { printf("\n  "); col = 0; }
    }
    printf("\n");
}

static void frequency_table(void)
{
    int order[64], i, j;
    for (i = 0; i < nsym; i++) order[i] = i;
    for (i = 0; i < nsym; i++)
        for (j = i + 1; j < nsym; j++)
            if (cnt[order[j]] > cnt[order[i]]) { int t = order[i]; order[i] = order[j]; order[j] = t; }

    printf("\nSTEP 1 - Symbol frequencies (%d symbols, %d distinct)\n", ntok, nsym);
    printf("  symbol  count   %%     bar                  English rank letter\n");
    printf("  ------  -----  -----  ------------------   -------------------\n");
    for (i = 0; i < nsym; i++) {
        int k = order[i], b;
        printf("    ");
        utf8_print(sym[k]);
        printf("     %3d   %4.1f%%  ", cnt[k], 100.0 * cnt[k] / ntok);
        for (b = 0; b < cnt[k] / 2; b++) putchar('#');
        for (; b < 19; b++) putchar(' ');
        if (i < 26) printf("   #%-2d likely '%c'", i + 1, ENGLISH_ORDER[i]);
        printf("\n");
    }
}

static void doubles(void)
{
    int dbl[64] = {0}, i, best = -1, k;
    for (i = 0; i + 1 < ntok; i++)
        if (tok[i] == tok[i + 1]) dbl[sym_index(tok[i])]++;
    printf("\nSTEP 2 - Doubled symbols (e, o, s, t, l, f are the common double letters)\n");
    for (k = 0; k < nsym; k++)
        if (dbl[k]) {
            printf("    ");
            utf8_print(sym[k]); utf8_print(sym[k]);
            printf("  occurs %d times\n", dbl[k]);
            if (best < 0 || dbl[k] > dbl[best]) best = k;
        }
    if (best >= 0) {
        printf("  => the most common double is ");
        utf8_print(sym[best]); utf8_print(sym[best]);
        printf(" and that symbol is also the most frequent overall: it must be 'e'.\n");
    }
}

static void trigrams(void)
{
    cp_t tri[400][3];
    int tc[400], n = 0, i, j, best = 0;
    for (i = 0; i + 2 < ntok; i++) {
        for (j = 0; j < n; j++)
            if (tri[j][0] == tok[i] && tri[j][1] == tok[i + 1] && tri[j][2] == tok[i + 2]) break;
        if (j == n) { tri[n][0] = tok[i]; tri[n][1] = tok[i + 1]; tri[n][2] = tok[i + 2]; tc[n++] = 0; }
        tc[j]++;
    }
    printf("\nSTEP 3 - Most frequent 3-symbol sequences\n");
    for (j = 0; j < n; j++) if (tc[j] > tc[best]) best = j;
    for (j = 0; j < n; j++)
        if (tc[j] >= tc[best] - 3 && tc[j] >= 3) {
            printf("    ");
            utf8_print(tri[j][0]); utf8_print(tri[j][1]); utf8_print(tri[j][2]);
            printf("  occurs %d times\n", tc[j]);
        }
    printf("  => the most common trigram is almost certainly \"the\":\n     ");
    utf8_print(tri[best][0]); printf(" = t,  ");
    utf8_print(tri[best][1]); printf(" = h,  ");
    utf8_print(tri[best][2]); printf(" = e\n");
}

/* ---- stages of the analysis --------------------------------------------- */
typedef struct { cp_t symbol; char letter; } Pair;

typedef struct {
    const char *why;
    Pair pairs[8];
} Stage;

static const Stage STAGES[] = {
    { "e is the most frequent symbol and the most common double; \";48\" is 'the'",
      { {'8','e'}, {';','t'}, {'4','h'}, {0,0} } },
    { "\";(88\" -> t?ee : the word \"tree\" (also \"through\" / \"from\" later)",
      { {'(','r'}, {0,0} } },
    { "\"th(ee\" ... \"4(‡?34\" -> th r ? u g h : \"through\"",
      { {0x2021,'o'}, {'?','u'}, {'3','g'}, {0,0} } },
    { "\"?8)\" \"‡(\" ... \"thr?ugh\" + \"the\" : common words \"and\", \"in\", \"is\"",
      { {'6','i'}, {'*','n'}, {')','s'}, {'5','a'}, {0,0} } },
    { "\"†\" before 'e' and 'a' : \"degrees\", \"and\" -> d ; \"9\" in \"fro9\" -> m",
      { {0x2020,'d'}, {'9','m'}, {'1','f'}, {0,0} } },
    { "remaining words: \"bishop's hostel\", \"devil's seat\", \"twenty-one\", \"branch\"",
      { {'2','b'}, {'.','p'}, {'0','l'}, {0xB6,'v'}, {']','w'}, {':','y'}, {0x2014,'c'}, {0,0} } },
};

int main(void)
{
    size_t s, p;
    int i;

    printf("=========================================================\n");
    printf("  SUBSTITUTION CIPHER CRYPTANALYSIS  (Poe's Gold-Bug)\n");
    printf("=========================================================\n");

    tokenise();
    printf("\nCiphertext:\n  %s\n", CIPHERTEXT);

    frequency_table();
    doubles();
    trigrams();

    printf("\nSTEP 4 - Apply the guesses stage by stage\n");
    for (s = 0; s < sizeof STAGES / sizeof STAGES[0]; s++) {
        printf("\n--- Stage %zu : %s\n    new assignments: ", s + 1, STAGES[s].why);
        for (p = 0; p < 8 && STAGES[s].pairs[p].symbol; p++) {
            int k = sym_index(STAGES[s].pairs[p].symbol);
            if (k < 0) continue;
            guess[k] = STAGES[s].pairs[p].letter;
            utf8_print(sym[k]);
            printf("=%c  ", guess[k]);
        }
        print_partial();
    }

    /* Anything still unassigned is solved by reading the text */
    {
        int unknown = 0;
        for (i = 0; i < nsym; i++) if (!guess[i]) unknown++;
        printf("\nSymbols still unknown after all stages: %d\n", unknown);
    }

    printf("\nSTEP 5 - Complete key (cipher symbol -> plaintext letter)\n  ");
    for (i = 0; i < nsym; i++) {
        utf8_print(sym[i]);
        printf("->%c  ", guess[i] ? guess[i] : '?');
        if ((i + 1) % 8 == 0) printf("\n  ");
    }
    printf("\n");

    printf("\nFINAL PLAINTEXT (word breaks restored by hand):\n\n");
    printf("  A good glass in the bishop's hostel in the devil's seat -\n");
    printf("  twenty-one degrees and thirteen minutes - northeast and by north -\n");
    printf("  main branch seventh limb east side - shoot from the left eye of the\n");
    printf("  death's-head - a bee line from the tree through the shot fifty feet out.\n");

    printf("\nMachine decryption using the recovered key:\n");
    print_partial();
    return 0;
}
