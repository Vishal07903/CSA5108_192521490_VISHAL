/*
 * ============================================================================
 *  EXPERIMENT 15 : AUTOMATIC LETTER-FREQUENCY ATTACK ON AN ADDITIVE CIPHER
 * ============================================================================
 *  Aim
 *  ---
 *  Write a program that can perform a letter-frequency attack on an additive
 *  (Caesar / shift) cipher without human intervention.  The software should
 *  produce possible plaintexts in rough order of likelihood.  The user
 *  interface should allow the user to specify "give me the top 10 possible
 *  plaintexts".
 *
 *  Method
 *  ------
 *  An additive cipher has only 26 keys.  For each key k the ciphertext is
 *  decrypted and given a LIKELIHOOD SCORE based on how closely the letter
 *  frequencies of the candidate match English:
 *
 *      score(k) = SUM over letters  count_i * ln( f_i )            (log-likelihood)
 *
 *  where f_i is the relative frequency of letter i in English and count_i is
 *  how often letter i appears in the candidate.  The larger the score the more
 *  likely the key.  The chi-square statistic
 *
 *      chi2(k) = SUM (observed_i - expected_i)^2 / expected_i
 *
 *  is shown beside it (smaller = better) as a cross-check.  Candidates are
 *  sorted by score and the best N are printed together with a probability
 *  estimate that the candidate is the right one (a softmax of the scores).
 *
 *  Compile :  gcc 15_additive_cipher_attack.c -o additive_attack -lm
 * ============================================================================
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <math.h>

#define MAXLEN 8192

static const double ENG[26] = {   /* English letter frequencies, % */
    8.167, 1.492, 2.782, 4.253, 12.702, 2.228, 2.015, 6.094, 6.966, 0.153, 0.772, 4.025, 2.406,
    6.749, 7.507, 1.929, 0.095, 5.987, 6.327, 9.056, 2.758, 0.978, 2.360, 0.150, 1.974, 0.074 };

typedef struct {
    int    key;
    double loglik, chi2, prob;
    char   text[MAXLEN];
} Cand;

static void read_line(const char *prompt, char *buf, size_t n)
{
    printf("%s", prompt);
    fflush(stdout);
    if (!fgets(buf, (int)n, stdin)) { printf("\n"); exit(0); }
    buf[strcspn(buf, "\r\n")] = '\0';
}

static void shift_text(const char *in, char *out, int k)
{
    int i;
    for (i = 0; in[i]; i++) {
        if (isalpha((unsigned char)in[i])) {
            int base = isupper((unsigned char)in[i]) ? 'A' : 'a';
            out[i] = (char)(base + ((in[i] - base - k) % 26 + 26) % 26);   /* decrypt with key k */
        } else out[i] = in[i];
    }
    out[i] = '\0';
}

static void score(Cand *c)
{
    int cnt[26] = {0}, n = 0, i;
    c->loglik = 0; c->chi2 = 0;
    for (i = 0; c->text[i]; i++)
        if (isalpha((unsigned char)c->text[i])) { cnt[toupper((unsigned char)c->text[i]) - 'A']++; n++; }
    if (!n) return;
    for (i = 0; i < 26; i++) {
        double e = n * ENG[i] / 100.0, d = cnt[i] - e;
        c->loglik += cnt[i] * log(ENG[i] / 100.0);
        c->chi2   += d * d / e;
    }
}

static int cmp(const void *a, const void *b)
{
    double d = ((const Cand *)b)->loglik - ((const Cand *)a)->loglik;   /* descending */
    return (d > 0) - (d < 0);
}

static void attack(const char *cipher, int topn)
{
    static Cand cand[26];
    int k, i;
    double mx, sum = 0;

    for (k = 0; k < 26; k++) {
        cand[k].key = k;
        shift_text(cipher, cand[k].text, k);
        score(&cand[k]);
    }
    qsort(cand, 26, sizeof(Cand), cmp);

    mx = cand[0].loglik;
    for (k = 0; k < 26; k++) { cand[k].prob = exp(cand[k].loglik - mx); sum += cand[k].prob; }
    for (k = 0; k < 26; k++) cand[k].prob /= sum;

    if (topn > 26) topn = 26;
    printf("\n  rank | key | letter | log-lik  |  chi2  | prob  | candidate plaintext\n");
    printf("  -----+-----+--------+----------+--------+-------+--------------------\n");
    for (i = 0; i < topn; i++) {
        printf("  %4d | %3d |   %c    | %8.1f | %6.1f | %4.1f%% | %.60s%s\n", i + 1, cand[i].key,
               'A' + cand[i].key, cand[i].loglik, cand[i].chi2, 100 * cand[i].prob, cand[i].text,
               strlen(cand[i].text) > 60 ? "..." : "");
    }
    printf("\n  Most likely key: %d  (ciphertext letter A decrypts to %c)\n",
           cand[0].key, 'A' + (26 - cand[0].key) % 26);
}

int main(void)
{
    char cipher[MAXLEN], buf[64];
    int topn;

    printf("=========================================\n");
    printf("  LETTER-FREQUENCY ATTACK ON ADDITIVE CIPHER\n");
    printf("=========================================\n");

    for (;;) {
        read_line("\nEnter ciphertext (blank to quit): ", cipher, sizeof cipher);
        if (!cipher[0]) break;
        read_line("How many top candidate plaintexts do you want? (default 10): ", buf, sizeof buf);
        topn = buf[0] ? atoi(buf) : 10;
        if (topn < 1) topn = 10;
        attack(cipher, topn);
    }
    return 0;
}
