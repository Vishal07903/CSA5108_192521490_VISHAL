/*
 * ============================================================================
 *  EXPERIMENT 8 : KEYWORD (MONOALPHABETIC) CIPHER
 * ============================================================================
 *  Aim
 *  ---
 *  With a general monoalphabetic cipher, both sender and receiver must commit
 *  the permuted cipher sequence to memory.  A common technique for avoiding
 *  this is to use a keyword from which the cipher sequence can be generated.
 *
 *  Example - keyword CIPHER: write out the keyword followed by the unused
 *  letters in normal order and match this against the plaintext letters:
 *
 *      plain : a b c d e f g h i j k l m n o p q r s t u v w x y z
 *      cipher: C I P H E R A B D F G J K L M N O Q S T U V W X Y Z
 *
 *  Algorithm
 *  ---------
 *   1. upper-case the keyword, discard non-letters and repeated letters
 *   2. append every letter of the alphabet not yet used, in A..Z order
 *   3. this 26-letter string is the cipher alphabet
 *   4. encrypt with  C = cipher[P],  decrypt with the inverse table
 *
 *  Compile :  gcc 08_keyword_cipher.c -o keyword
 * ============================================================================
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

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

/* build cipher alphabet from keyword */
static void make_alphabet(const char *keyword, char *cipher)
{
    int used[26] = {0}, n = 0, i;
    char c;

    for (i = 0; keyword[i]; i++) {
        if (!isalpha((unsigned char)keyword[i])) continue;
        c = (char)toupper((unsigned char)keyword[i]);
        if (!used[c - 'A']) { used[c - 'A'] = 1; cipher[n++] = c; }
    }
    for (c = 'A'; c <= 'Z'; c++)
        if (!used[c - 'A']) cipher[n++] = c;
    cipher[n] = '\0';
}

static void show(const char *cipher)
{
    int i;
    printf("\n  plain : ");
    for (i = 0; i < 26; i++) printf("%c ", 'a' + i);
    printf("\n  cipher: ");
    for (i = 0; i < 26; i++) printf("%c ", cipher[i]);
    printf("\n");
}

static void crypt_text(const char *in, char *out, const char *cipher, int decrypt)
{
    char inv[26];
    int i;
    for (i = 0; i < 26; i++) inv[cipher[i] - 'A'] = (char)('A' + i);

    for (i = 0; in[i]; i++) {
        if (isalpha((unsigned char)in[i])) {
            int up = isupper((unsigned char)in[i]);
            int x = toupper((unsigned char)in[i]) - 'A';
            char y = decrypt ? inv[x] : cipher[x];
            out[i] = up ? y : (char)tolower((unsigned char)y);
        } else out[i] = in[i];
    }
    out[i] = '\0';
}

int main(void)
{
    char key[128], cipher[32], text[MAXLEN], out[MAXLEN];
    int choice;

    printf("=========================================\n");
    printf("       KEYWORD MONOALPHABETIC CIPHER\n");
    printf("=========================================\n");

    read_line("Enter keyword (e.g. CIPHER): ", key, sizeof key);
    make_alphabet(key, cipher);
    printf("\nKeyword            : %s", key);
    show(cipher);

    for (;;) {
        printf("\n1. Encrypt\n2. Decrypt\n3. New keyword\n4. Exit\n");
        choice = read_int("Choice: ");
        if (choice == 4) return 0;
        if (choice == 1) {
            read_line("Enter plaintext : ", text, sizeof text);
            crypt_text(text, out, cipher, 0);
            printf("Ciphertext      : %s\n", out);
        } else if (choice == 2) {
            read_line("Enter ciphertext: ", text, sizeof text);
            crypt_text(text, out, cipher, 1);
            printf("Plaintext       : %s\n", out);
        } else if (choice == 3) {
            read_line("Enter keyword: ", key, sizeof key);
            make_alphabet(key, cipher);
            show(cipher);
        } else printf("Invalid choice.\n");
    }
}
