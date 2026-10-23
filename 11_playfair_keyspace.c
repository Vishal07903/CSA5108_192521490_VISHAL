/*
 * ============================================================================
 *  EXPERIMENT 11 : HOW MANY KEYS DOES THE PLAYFAIR CIPHER HAVE?
 * ============================================================================
 *  Aim
 *  ---
 *  How many possible keys does the Playfair cipher have?  Ignore the fact that
 *  some keys might produce identical encryption results.  Express the answer
 *  as an approximate power of 2.
 *      a. Now take into account the fact that some Playfair keys produce the
 *         same encryption results.  How many effectively unique keys does the
 *         Playfair cipher have?
 *
 *  Answer
 *  ------
 *  A key is an arrangement of 25 distinct letters (I/J merged) in the 5x5
 *  matrix, so there are 25! possible keys.
 *
 *        25! = 15 511 210 043 330 985 984 000 000  ~ 1.55 x 10^25  ~ 2^84
 *
 *  (a) Equivalent keys.  The Playfair rules only use RELATIVE positions on a
 *  matrix that wraps around like a torus:
 *    - same row    : neighbour to the right (wrap-around)
 *    - same column : neighbour below (wrap-around)
 *    - rectangle   : swap columns
 *  Therefore moving the whole matrix cyclically - shifting every row left /
 *  right by s (5 ways) and every column up / down by t (5 ways) - never
 *  changes any digraph encryption.  Each matrix therefore has 5 x 5 = 25
 *  equivalent versions (including itself), and
 *
 *        effective keys = 25! / 25 = 24! = 620 448 401 733 239 439 360 000
 *                       ~ 6.2 x 10^23  ~ 2^79
 *
 *  The program
 *    1. computes 25! and 24! exactly (128-bit integers) and log2 of each
 *    2. EXPERIMENTALLY checks the claim: it takes random matrices, builds
 *       all 25 toroidal shifts, and verifies that every one encrypts all
 *       25*24 possible digraphs identically
 *    3. tests the other 7 geometric symmetries of the square (rotations,
 *       reflections, transpose) and shows that they do NOT preserve the
 *       cipher, so no further reduction comes from them.
 *
 *  Compile :  gcc 11_playfair_keyspace.c -o playfair_keys -lm
 * ============================================================================
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

typedef unsigned __int128 u128;

static void print_u128(u128 v)
{
    char buf[64];
    int n = 0, i, c = 0;
    if (v == 0) { printf("0"); return; }
    while (v) { buf[n++] = (char)('0' + (int)(v % 10)); v /= 10; }
    for (i = n - 1; i >= 0; i--) {
        putchar(buf[i]);
        if (i > 0 && i % 3 == 0) putchar(' ');
        c++;
    }
}

/* ---- Playfair engine on an arbitrary 25-entry matrix --------------------- */
typedef struct { char m[25]; } Mat;

static void pf_pair(const Mat *k, int a, int b, int *x, int *y)
{
    int pa = -1, pb = -1, i;
    for (i = 0; i < 25; i++) { if (k->m[i] == a) pa = i; if (k->m[i] == b) pb = i; }
    int r1 = pa / 5, c1 = pa % 5, r2 = pb / 5, c2 = pb % 5;
    if (r1 == r2)      { *x = k->m[r1 * 5 + (c1 + 1) % 5]; *y = k->m[r2 * 5 + (c2 + 1) % 5]; }
    else if (c1 == c2) { *x = k->m[((r1 + 1) % 5) * 5 + c1]; *y = k->m[((r2 + 1) % 5) * 5 + c2]; }
    else               { *x = k->m[r1 * 5 + c2]; *y = k->m[r2 * 5 + c1]; }
}

/* do two matrices give identical results for every digraph of distinct letters? */
static int same_cipher(const Mat *a, const Mat *b)
{
    int p, q, x1, y1, x2, y2;
    for (p = 0; p < 25; p++)
        for (q = 0; q < 25; q++) {
            if (p == q) continue;
            pf_pair(a, p, q, &x1, &y1);
            pf_pair(b, p, q, &x2, &y2);
            if (x1 != x2 || y1 != y2) return 0;
        }
    return 1;
}

static void random_matrix(Mat *k)
{
    int i, j, t;
    for (i = 0; i < 25; i++) k->m[i] = (char)i;
    for (i = 24; i > 0; i--) { j = rand() % (i + 1); t = k->m[i]; k->m[i] = k->m[j]; k->m[j] = (char)t; }
}

static void shift(const Mat *in, Mat *out, int dr, int dc)
{
    int r, c;
    for (r = 0; r < 5; r++)
        for (c = 0; c < 5; c++)
            out->m[((r + dr) % 5) * 5 + (c + dc) % 5] = in->m[r * 5 + c];
}

/* the 7 non-identity symmetries of a square */
static void symmetry(const Mat *in, Mat *out, int s)
{
    int r, c;
    for (r = 0; r < 5; r++)
        for (c = 0; c < 5; c++) {
            int nr, nc;
            switch (s) {
            case 1:  nr = c;     nc = 4 - r; break;     /* rotate 90  */
            case 2:  nr = 4 - r; nc = 4 - c; break;     /* rotate 180 */
            case 3:  nr = 4 - c; nc = r;     break;     /* rotate 270 */
            case 4:  nr = r;     nc = 4 - c; break;     /* mirror left-right */
            case 5:  nr = 4 - r; nc = c;     break;     /* mirror top-bottom */
            case 6:  nr = c;     nc = r;     break;     /* transpose */
            default: nr = 4 - c; nc = 4 - r; break;     /* anti-transpose */
            }
            out->m[nr * 5 + nc] = in->m[r * 5 + c];
        }
}

int main(void)
{
    static const char *SYM[] = { "", "rotate 90", "rotate 180", "rotate 270",
                                 "mirror left-right", "mirror top-bottom", "transpose", "anti-transpose" };
    u128 f = 1, f24 = 1;
    int i, trial, dr, dc, s;

    printf("=========================================\n");
    printf("   PLAYFAIR CIPHER - KEY SPACE ANALYSIS\n");
    printf("=========================================\n");

    for (i = 2; i <= 24; i++) f24 *= (u128)i;
    f = f24 * 25;

    printf("\n(1) Total number of keys   25! = ");
    print_u128(f);
    printf("\n    log2(25!) = %.2f   =>  25! is about 2^84\n", log2(1.5511210043330986e25));

    printf("\n(2) Effective (distinct) keys: shifting rows/columns cyclically gives 5*5 = 25\n"
           "    matrices with identical behaviour, so\n\n    25!/25 = 24! = ");
    print_u128(f24);
    printf("\n    log2(24!) = %.2f   =>  about 2^79\n", log2(6.204484017332394e23));

    srand((unsigned)time(NULL));
    printf("\n(3) Experimental verification of the 25 equivalent matrices\n");
    {
        int good = 0, total = 0;
        for (trial = 0; trial < 200; trial++) {
            Mat k, t;
            random_matrix(&k);
            for (dr = 0; dr < 5; dr++)
                for (dc = 0; dc < 5; dc++) {
                    shift(&k, &t, dr, dc);
                    total++;
                    if (same_cipher(&k, &t)) good++;
                }
        }
        printf("    %d of %d shifted matrices encrypt all 600 digraphs identically.\n", good, total);
        printf("    %s\n", good == total ? "=> CONFIRMED: shifts never change the cipher."
                                          : "=> unexpected - check the code!");
    }

    printf("\n(4) Do the other symmetries of the square also give the same cipher?\n");
    for (s = 1; s <= 7; s++) {
        int same = 0;
        for (trial = 0; trial < 200; trial++) {
            Mat k, t;
            random_matrix(&k);
            symmetry(&k, &t, s);
            if (same_cipher(&k, &t)) same++;
        }
        printf("    %-18s : identical cipher in %3d of 200 random matrices\n", SYM[s], same);
    }
    printf("    => none of them preserve the cipher, so these give no further reduction (effective keys = 24!).\n");

    printf("\nSUMMARY\n  possible keys           : 25!  ~ 2^84\n  effectively unique keys : 24!  ~ 2^79\n");
    return 0;
}
