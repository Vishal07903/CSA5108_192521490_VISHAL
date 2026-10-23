/*
 * ============================================================================
 *  EXPERIMENT 14 : ONE-TIME-PAD VERSION OF THE VIGENERE CIPHER
 * ============================================================================
 *  Aim
 *  ---
 *  In the one-time-pad version of the Vigenere cipher the key is a stream of
 *  random numbers between 0 and 26 (a shift per letter).  For example, if the
 *  key is 3 19 5 ..., the first plaintext letter is shifted by 3, the second
 *  by 19, the third by 5, and so on.
 *
 *    a. Encrypt the plaintext  "send more money"  with the key stream
 *             9 0 1 7 23 15 21 14 11 11 2 8 9
 *    b. Using the ciphertext produced in (a), find a key so that the
 *       ciphertext decrypts to the plaintext  "cash not needed".
 *
 *  Algorithm
 *  ---------
 *      C_i = (P_i + K_i) mod 26         P_i = (C_i - K_i) mod 26
 *  and, to force a chosen plaintext P' from a known ciphertext:
 *      K'_i = (C_i - P'_i) mod 26
 *  This is why a one-time pad gives "perfect secrecy": for ANY plaintext of
 *  the same length there is a key that produces the observed ciphertext, so
 *  the ciphertext carries no information about the real plaintext.
 *
 *  Answers  (computed by the program)
 *      (a) SEND MORE MONEY + 9 0 1 7 23 15 21 14 11 11 2 8 9  ->  BEOKJDMSXZPMH
 *      (b) key 25 4 22 3 22 15 19 5 19 21 12 8 4  gives "cash not needed"
 *
 *  Menu
 *   1. Run the exact experiment (parts a and b)
 *   2. Encrypt with a key stream you type in
 *   3. Encrypt with a randomly generated pad
 *   4. Decrypt with a key stream
 *   5. Find the key that turns a ciphertext into a chosen plaintext
 *
 *  Compile :  gcc 14_vigenere_one_time_pad.c -o otp
 * ============================================================================
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <time.h>

#define MAXLEN 1024

static void read_line(const char *prompt, char *buf, size_t n)
{
    printf("%s", prompt);
    fflush(stdout);
    if (!fgets(buf, (int)n, stdin)) { printf("\n"); exit(0); }
    buf[strcspn(buf, "\r\n")] = '\0';
}

static int mod26(int x) { x %= 26; return x < 0 ? x + 26 : x; }

/* keep only letters, return as 0..25 numbers */
static int letters(const char *s, int *v)
{
    int n = 0, i;
    for (i = 0; s[i]; i++) if (isalpha((unsigned char)s[i])) v[n++] = tolower((unsigned char)s[i]) - 'a';
    return n;
}

/* parse a whitespace separated list of integers */
static int parse_key(const char *s, int *k)
{
    int n = 0;
    char *end;
    const char *p = s;
    for (;;) {
        long v = strtol(p, &end, 10);
        if (end == p) break;
        k[n++] = (int)v;
        p = end;
    }
    return n;
}

static void print_nums(const char *label, const int *v, int n)
{
    int i;
    printf("%s", label);
    for (i = 0; i < n; i++) printf("%d ", v[i]);
    printf("\n");
}

static void print_letters(const char *label, const int *v, int n, int upper)
{
    int i;
    printf("%s", label);
    for (i = 0; i < n; i++) putchar((upper ? 'A' : 'a') + v[i]);
    printf("\n");
}

static void encrypt(const int *p, const int *k, int *c, int n)
{
    int i;
    for (i = 0; i < n; i++) c[i] = mod26(p[i] + k[i]);
}

static void decrypt(const int *c, const int *k, int *p, int n)
{
    int i;
    for (i = 0; i < n; i++) p[i] = mod26(c[i] - k[i]);
}

static void find_key(const int *c, const int *p, int *k, int n)
{
    int i;
    for (i = 0; i < n; i++) k[i] = mod26(c[i] - p[i]);
}

static void table(const int *p, const int *k, const int *c, int n, int enc)
{
    int i;
    printf("\n   i | %s | key | %s\n  ---+---+-----+-----------------------------\n",
           enc ? "plain" : "ciph.", enc ? "cipher" : "plain ");
    for (i = 0; i < n; i++)
        printf("  %2d |  %c (%2d) | %2d  | %c (%2d)   = (%2d %c %2d) mod 26\n", i + 1,
               'a' + p[i], p[i], k[i], 'A' + c[i], c[i], p[i], enc ? '+' : '-', k[i]);
}

static void experiment(void)
{
    int p[MAXLEN], k[MAXLEN], c[MAXLEN], p2[MAXLEN], k2[MAXLEN], d[MAXLEN], n, n2;
    static const char *KEY = "9 0 1 7 23 15 21 14 11 11 2 8 9";

    printf("\n================ PART (a) ================\n");
    n = letters("send more money", p);
    parse_key(KEY, k);
    print_letters("Plaintext  : ", p, n, 0);
    print_nums   ("Key stream : ", k, n);
    encrypt(p, k, c, n);
    table(p, k, c, n, 1);
    print_letters("\nCIPHERTEXT : ", c, n, 1);

    printf("\n================ PART (b) ================\n");
    n2 = letters("cash not needed", p2);
    printf("Want the ciphertext  ");
    print_letters("", c, n, 1);
    printf("to decrypt to        ");
    print_letters("", p2, n2, 0);
    if (n2 != n) { printf("Length mismatch.\n"); return; }
    find_key(c, p2, k2, n);
    print_nums("\nKey  K'_i = (C_i - P'_i) mod 26 : ", k2, n);
    decrypt(c, k2, d, n);
    table(d, k2, c, n, 0);
    print_letters("\nCheck - decrypting with the new key gives: ", d, n, 0);
    printf("\nConclusion: the same ciphertext can be \"decrypted\" to ANY message of equal\n"
           "length by choosing the right key - this is the perfect secrecy of a one-time pad.\n");
}

int main(void)
{
    char buf[MAXLEN], buf2[MAXLEN];
    int choice, p[MAXLEN], k[MAXLEN], c[MAXLEN], out[MAXLEN], n, nk, i;

    srand((unsigned)time(NULL));
    printf("=========================================\n");
    printf("   ONE-TIME-PAD VIGENERE CIPHER\n");
    printf("=========================================\n");

    for (;;) {
        printf("\n1. Run the experiment (send more money / cash not needed)\n"
               "2. Encrypt with my key stream\n3. Encrypt with a random pad\n"
               "4. Decrypt with a key stream\n5. Find key for a chosen plaintext\n6. Exit\n");
        read_line("Choice: ", buf, sizeof buf);
        choice = atoi(buf);
        if (choice == 6) return 0;

        if (choice == 1) { experiment(); continue; }

        if (choice == 2 || choice == 3) {
            read_line("Plaintext: ", buf, sizeof buf);
            n = letters(buf, p);
            if (choice == 2) {
                read_line("Key stream (numbers separated by spaces): ", buf2, sizeof buf2);
                nk = parse_key(buf2, k);
                if (nk < n) { printf("Key must be at least as long as the message (%d numbers).\n", n); continue; }
                for (i = 0; i < n; i++) k[i] = mod26(k[i]);
            } else {
                for (i = 0; i < n; i++) k[i] = rand() % 26;
                print_nums("Random pad    : ", k, n);
            }
            encrypt(p, k, c, n);
            table(p, k, c, n, 1);
            print_letters("\nCiphertext: ", c, n, 1);
        } else if (choice == 4) {
            read_line("Ciphertext: ", buf, sizeof buf);
            n = letters(buf, c);
            read_line("Key stream (numbers separated by spaces): ", buf2, sizeof buf2);
            nk = parse_key(buf2, k);
            if (nk < n) { printf("Key too short.\n"); continue; }
            decrypt(c, k, out, n);
            print_letters("Plaintext: ", out, n, 0);
        } else if (choice == 5) {
            read_line("Ciphertext      : ", buf, sizeof buf);
            n = letters(buf, c);
            read_line("Desired plaintext: ", buf2, sizeof buf2);
            if (letters(buf2, p) != n) { printf("Lengths differ.\n"); continue; }
            find_key(c, p, k, n);
            print_nums("Key stream required: ", k, n);
        } else printf("Invalid choice.\n");
    }
}
