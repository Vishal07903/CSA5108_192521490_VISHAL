/*
 * ============================================================================
 *  EXPERIMENT 2 : MONOALPHABETIC SUBSTITUTION CIPHER
 * ============================================================================
 *  Aim
 *  ---
 *  Write a C program for a monoalphabetic substitution cipher, which maps a
 *  plaintext alphabet to a ciphertext alphabet so that each letter of the
 *  plaintext alphabet maps to a single unique letter of the ciphertext
 *  alphabet.
 *
 *  Algorithm
 *  ---------
 *  The key is a permutation of the 26 letters.
 *      Encryption :  C = key[P]
 *      Decryption :  P = inverse_key[C]
 *  The key can be typed in or generated randomly (Fisher-Yates shuffle).
 *  The key is validated: it must contain 26 distinct letters.
 *
 *  Key space = 26! (about 4.03 x 10^26 ~ 2^88), far too large to brute force,
 *  but the cipher still falls to letter-frequency analysis (see Expt 16).
 *
 *  Compile :  gcc 02_monoalphabetic_cipher.c -o mono
 * ============================================================================
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <time.h>

#define MAXLEN 2048

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

/* returns 1 if key is a valid permutation of A-Z (and upper-cases it) */
static int validate_key(char *key)
{
    int seen[26] = {0}, i;
    if (strlen(key) != 26) return 0;
    for (i = 0; i < 26; i++) {
        if (!isalpha((unsigned char)key[i])) return 0;
        key[i] = (char)toupper((unsigned char)key[i]);
        if (seen[key[i] - 'A']++) return 0;
    }
    return 1;
}

static void random_key(char *key)
{
    int i, j;
    char t;
    for (i = 0; i < 26; i++) key[i] = (char)('A' + i);
    key[26] = '\0';
    for (i = 25; i > 0; i--) {             /* Fisher-Yates shuffle */
        j = rand() % (i + 1);
        t = key[i]; key[i] = key[j]; key[j] = t;
    }
}

static void show_table(const char *key)
{
    int i;
    printf("\n  plain : ");
    for (i = 0; i < 26; i++) printf("%c ", 'A' + i);
    printf("\n  cipher: ");
    for (i = 0; i < 26; i++) printf("%c ", key[i]);
    printf("\n");
}

static void encrypt(const char *in, char *out, const char *key)
{
    size_t i;
    for (i = 0; in[i]; i++) {
        if (isupper((unsigned char)in[i]))      out[i] = key[in[i] - 'A'];
        else if (islower((unsigned char)in[i])) out[i] = (char)tolower(key[in[i] - 'a']);
        else                                    out[i] = in[i];
    }
    out[i] = '\0';
}

static void decrypt(const char *in, char *out, const char *key)
{
    char inv[26];
    size_t i;
    for (i = 0; i < 26; i++) inv[key[i] - 'A'] = (char)('A' + i);   /* inverse permutation */
    for (i = 0; in[i]; i++) {
        if (isupper((unsigned char)in[i]))      out[i] = inv[in[i] - 'A'];
        else if (islower((unsigned char)in[i])) out[i] = (char)tolower(inv[in[i] - 'a']);
        else                                    out[i] = in[i];
    }
    out[i] = '\0';
}

static void get_key(char *key)
{
    char c[8];
    read_line("Generate a random key? (y/n): ", c, sizeof c);
    if (tolower((unsigned char)c[0]) == 'y') {
        random_key(key);
        printf("Generated key: %s\n", key);
    } else {
        for (;;) {
            read_line("Enter 26-letter permutation key: ", key, 64);
            if (validate_key(key)) break;
            printf("  Invalid: need 26 DISTINCT letters.\n");
        }
    }
}

int main(void)
{
    char text[MAXLEN], out[MAXLEN], key[64];
    int choice;

    srand((unsigned)time(NULL));
    printf("=========================================\n");
    printf("   MONOALPHABETIC SUBSTITUTION CIPHER\n");
    printf("=========================================\n");

    for (;;) {
        printf("\n1. Encrypt\n2. Decrypt\n3. Exit\n");
        choice = read_int("Choice: ");
        if (choice == 3) return 0;
        if (choice != 1 && choice != 2) { printf("Invalid choice.\n"); continue; }

        get_key(key);
        show_table(key);

        if (choice == 1) {
            read_line("\nEnter plaintext : ", text, sizeof text);
            encrypt(text, out, key);
            printf("Ciphertext      : %s\n", out);
        } else {
            read_line("\nEnter ciphertext: ", text, sizeof text);
            decrypt(text, out, key);
            printf("Plaintext       : %s\n", out);
        }
    }
}
