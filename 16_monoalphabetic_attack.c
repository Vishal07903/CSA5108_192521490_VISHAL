/*
 * ============================================================================
 *  EXPERIMENT 16 : AUTOMATIC LETTER-FREQUENCY ATTACK ON ANY MONOALPHABETIC
 *                  SUBSTITUTION CIPHER
 * ============================================================================
 *  Aim
 *  ---
 *  Write a program that can perform a letter-frequency attack on ANY
 *  monoalphabetic substitution cipher without human intervention.  The
 *  software should produce possible plaintexts in rough order of likelihood.
 *  The user interface should allow the user to specify "give me the top 10
 *  possible plaintexts".
 *
 *  Method  (statistical hill climbing with random restarts)
 *  ------
 *   1. Initial key: rank the cipher letters by frequency and map them onto the
 *      English frequency order  E T A O I N S H R D L C U M W F G Y P B V K J X Q Z.
 *   2. Every candidate plaintext is scored by an English language model:
 *
 *          score = SUM log10 P(bigram)  +  SUM log10 P(trigram)
 *
 *      The bigram table (26 x 26) and the 700 most common trigrams below were
 *      measured from about 870,000 letters of English text.  A candidate that
 *      "looks like English" - in letters AND in letter pairs/triples - scores
 *      higher (the numbers are negative; closer to 0 is better).
 *   3. Hill climbing: repeatedly try swapping two letters of the key; keep the
 *      swap if the score improves; stop when no swap helps.
 *   4. Repeat from many different starting keys (random restarts), collect the
 *      DISTINCT final keys, sort by score and print the best N.
 *
 *  Works best on ciphertext of 150+ letters.  Spaces and punctuation are kept
 *  in the output but ignored by the statistics.
 *
 *  Compile :  gcc 16_monoalphabetic_attack.c -o mono_attack -lm
 * ============================================================================
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <math.h>
#include <time.h>

#define MAXLEN   8192
#define MAXKEEP  64
#define RESTARTS 600

/* English letters, most frequent first (used for the starting key) */
static const char *FREQ_ORDER = "ETAOINSHRDLCUMWFGYPBVKJXQZ";

/* ------------------------------------------------------------------ */
/*  ENGLISH LANGUAGE MODEL (measured from ~870,000 letters of English)  */
/*  BIGRAM_LL[a][b]  = log10 P(letter a followed by letter b)           */
/*  TRIGRAMS[]       = the 700 most common trigrams, log10 P            */
/*  any other trigram scores TRI_FLOOR                                  */
/* ------------------------------------------------------------------ */
static const float BIGRAM_LL[26][26] = {
    /* A */ {-3.92,-2.63,-2.36,-2.71,-4.60,-3.01,-2.86,-4.11,-2.69,-4.45,-3.01,-2.10,-2.45,-1.85,-4.36,-2.69,-4.38,-2.04,-2.24,-1.95,-2.93,-2.86,-3.29,-3.39,-2.83,-4.41},
    /* B */ {-2.96,-4.11,-3.91,-4.36,-2.45,-4.86,-4.64,-5.94,-3.17,-3.03,-5.16,-2.62,-4.52,-4.90,-3.08,-3.89,-5.94,-3.05,-3.48,-4.10,-2.68,-4.49,-4.71,-5.64,-2.84,-5.64},
    /* C */ {-2.37,-4.56,-3.17,-4.36,-2.25,-3.78,-4.90,-2.35,-2.82,-5.94,-2.93,-2.64,-3.94,-4.51,-2.07,-3.95,-4.98,-2.93,-3.79,-2.27,-2.70,-4.71,-4.18,-5.64,-4.13,-5.94},
    /* D */ {-2.62,-2.91,-3.11,-2.99,-2.16,-3.04,-3.80,-3.64,-2.20,-4.31,-4.23,-3.19,-3.37,-3.48,-2.45,-3.33,-4.94,-3.33,-2.71,-2.49,-2.97,-3.38,-2.98,-4.35,-3.31,-4.83},
    /* E */ {-2.13,-2.82,-2.03,-1.97,-2.43,-2.28,-2.85,-3.25,-2.35,-4.18,-3.74,-2.39,-2.38,-1.91,-2.49,-2.44,-3.04,-1.78,-1.87,-1.96,-2.96,-2.64,-2.57,-2.36,-2.71,-4.45},
    /* F */ {-2.75,-4.08,-3.60,-3.89,-2.85,-2.95,-4.43,-4.27,-2.29,-5.34,-4.28,-3.44,-3.95,-3.76,-2.28,-3.75,-5.64,-2.87,-3.40,-2.37,-2.89,-4.01,-3.81,-4.60,-3.01,-5.94},
    /* G */ {-2.86,-3.84,-3.45,-3.87,-2.49,-3.57,-3.70,-2.89,-2.78,-4.86,-4.58,-3.26,-3.62,-3.13,-3.14,-3.67,-4.66,-2.89,-3.08,-2.83,-2.99,-3.84,-3.49,-4.98,-4.07,-4.86},
    /* H */ {-2.14,-4.13,-3.54,-3.99,-1.63,-3.71,-4.31,-4.35,-2.28,-4.83,-4.68,-3.70,-3.66,-3.93,-2.53,-3.83,-5.34,-3.35,-3.50,-2.70,-3.51,-3.89,-3.91,-4.58,-3.85,-5.04},
    /* I */ {-2.89,-2.71,-2.32,-2.84,-2.74,-2.45,-2.74,-5.46,-4.12,-5.94,-3.42,-2.34,-2.50,-1.71,-2.11,-3.06,-4.49,-2.80,-1.96,-2.03,-4.31,-2.93,-4.62,-3.62,-4.98,-3.51},
    /* J */ {-4.46,-5.64,-4.94,-5.94,-3.03,-5.94,-5.94,-5.94,-5.94,-5.94,-5.24,-5.94,-5.34,-5.64,-4.19,-5.09,-5.94,-5.94,-4.76,-5.24,-3.55,-5.94,-5.94,-5.94,-5.64,-5.94},
    /* K */ {-3.47,-4.01,-4.02,-4.56,-2.70,-3.97,-4.42,-4.94,-3.19,-5.34,-4.94,-3.96,-4.08,-3.75,-3.82,-4.18,-5.94,-4.40,-3.23,-3.47,-3.90,-4.76,-3.73,-5.94,-4.21,-5.94},
    /* L */ {-2.43,-3.30,-3.33,-2.87,-2.06,-3.34,-4.03,-4.06,-2.18,-4.76,-4.22,-2.32,-3.45,-3.50,-2.50,-3.18,-5.16,-3.58,-2.85,-2.77,-2.68,-3.59,-3.46,-4.71,-2.58,-5.34},
    /* M */ {-2.20,-3.07,-3.69,-3.69,-2.16,-3.86,-4.34,-4.20,-2.80,-5.94,-4.51,-4.01,-2.67,-3.85,-2.55,-2.60,-5.94,-3.81,-2.94,-3.13,-3.07,-4.18,-3.47,-5.94,-3.90,-5.64},
    /* N */ {-2.29,-3.08,-2.42,-2.01,-2.20,-3.03,-2.12,-3.69,-2.55,-4.54,-3.67,-3.01,-3.14,-3.16,-2.27,-3.26,-4.86,-3.47,-2.21,-1.90,-2.77,-3.09,-3.26,-4.40,-2.75,-4.83},
    /* O */ {-2.93,-2.79,-2.70,-2.51,-3.09,-2.20,-3.00,-3.82,-3.08,-4.29,-3.43,-2.72,-2.30,-1.86,-3.02,-2.52,-4.90,-1.89,-2.67,-2.26,-2.09,-2.78,-2.58,-4.46,-3.86,-4.49},
    /* P */ {-2.51,-4.15,-4.03,-4.01,-2.42,-3.72,-4.76,-3.77,-2.94,-5.46,-4.86,-2.51,-4.31,-4.34,-2.74,-2.86,-5.64,-2.44,-3.57,-2.63,-3.02,-4.54,-4.10,-5.16,-3.02,-5.94},
    /* Q */ {-5.16,-5.94,-5.16,-5.94,-5.24,-5.46,-5.94,-5.94,-4.94,-5.64,-5.94,-5.46,-5.46,-5.94,-5.64,-5.94,-5.46,-5.16,-5.16,-5.46,-2.96,-5.94,-5.09,-5.94,-5.94,-5.94},
    /* R */ {-2.18,-3.38,-2.75,-2.78,-1.84,-3.15,-2.99,-3.72,-2.19,-4.76,-2.89,-3.10,-2.61,-2.84,-2.30,-3.09,-5.04,-2.76,-2.40,-2.29,-3.00,-3.38,-3.05,-4.56,-2.71,-5.16},
    /* S */ {-2.26,-3.17,-2.58,-3.08,-1.93,-2.86,-3.53,-2.79,-2.17,-4.28,-3.68,-2.85,-3.04,-2.90,-2.31,-2.62,-4.22,-3.15,-2.35,-1.93,-2.55,-3.48,-2.82,-4.42,-2.88,-4.71},
    /* T */ {-2.16,-3.12,-2.64,-3.25,-1.91,-3.01,-3.72,-1.51,-1.89,-4.64,-4.01,-2.87,-3.03,-3.29,-2.00,-3.21,-4.71,-2.42,-2.38,-2.27,-2.81,-3.45,-2.68,-3.71,-2.58,-5.09},
    /* U */ {-2.83,-2.98,-2.75,-3.10,-2.81,-3.43,-3.10,-3.62,-3.03,-4.76,-4.45,-2.67,-2.63,-2.48,-3.78,-2.95,-5.24,-2.52,-2.29,-2.37,-3.95,-5.09,-3.28,-5.46,-4.56,-5.34},
    /* V */ {-2.73,-5.94,-4.98,-5.24,-2.29,-5.46,-5.64,-5.64,-2.58,-5.94,-5.94,-5.94,-5.24,-5.46,-3.64,-5.94,-5.94,-5.64,-5.04,-4.76,-5.94,-5.16,-5.64,-5.94,-5.46,-5.94},
    /* W */ {-2.71,-4.41,-3.91,-4.21,-3.04,-3.98,-4.54,-2.55,-2.34,-5.16,-4.71,-3.92,-4.15,-3.62,-2.68,-4.15,-5.94,-3.31,-3.33,-3.37,-4.36,-4.11,-3.77,-5.94,-4.00,-5.94},
    /* X */ {-3.15,-4.62,-3.10,-4.49,-3.16,-3.98,-4.79,-4.20,-3.40,-5.94,-5.16,-4.49,-4.33,-4.46,-4.27,-3.14,-5.64,-4.54,-4.15,-2.80,-4.94,-5.09,-4.60,-4.33,-4.15,-5.64},
    /* Y */ {-2.90,-3.32,-3.18,-3.43,-3.35,-3.41,-3.94,-3.89,-2.99,-4.71,-4.16,-3.55,-3.48,-3.15,-2.25,-2.77,-5.34,-3.28,-2.90,-2.71,-3.60,-3.75,-3.16,-4.98,-3.74,-4.46},
    /* Z */ {-4.16,-5.34,-5.16,-5.34,-3.51,-5.09,-5.94,-5.34,-4.19,-5.94,-5.94,-5.46,-4.98,-5.64,-4.58,-5.94,-5.94,-5.16,-5.09,-4.98,-5.94,-5.94,-5.64,-5.94,-4.90,-4.98},
};

#define TRI_FLOOR (-6.24f)
typedef struct { const char *s; float ll; } Trigram;
#define NUM_TRIGRAMS 700
static const Trigram TRIGRAMS[NUM_TRIGRAMS] = {
    {"the",-1.69f},{"ion",-2.14f},{"ing",-2.21f},{"tio",-2.23f},{"and",-2.26f},{"ent",-2.30f},
    {"eth",-2.32f},{"you",-2.33f},{"for",-2.38f},{"ter",-2.42f},{"tha",-2.46f},{"thi",-2.46f},
    {"her",-2.47f},{"nth",-2.49f},{"sth",-2.50f},{"fth",-2.51f},{"ere",-2.51f},{"his",-2.51f},
    {"oft",-2.52f},{"use",-2.52f},{"hat",-2.53f},{"ati",-2.54f},{"com",-2.54f},{"int",-2.55f},
    {"ect",-2.56f},{"oth",-2.57f},{"hes",-2.58f},{"are",-2.59f},{"eco",-2.60f},{"ont",-2.60f},
    {"not",-2.61f},{"all",-2.61f},{"tth",-2.61f},{"ith",-2.61f},{"men",-2.61f},{"ate",-2.62f},
    {"est",-2.62f},{"ons",-2.63f},{"ine",-2.64f},{"ist",-2.64f},{"hec",-2.64f},{"sin",-2.65f},
    {"wit",-2.65f},{"edi",-2.65f},{"ers",-2.65f},{"cti",-2.66f},{"ver",-2.66f},{"con",-2.66f},
    {"ile",-2.66f},{"sta",-2.67f},{"tin",-2.67f},{"hen",-2.67f},{"ted",-2.68f},{"man",-2.68f},
    {"res",-2.69f},{"din",-2.70f},{"cha",-2.71f},{"fil",-2.71f},{"att",-2.71f},{"ert",-2.71f},
    {"rth",-2.72f},{"omm",-2.74f},{"sto",-2.74f},{"efi",-2.74f},{"ame",-2.74f},{"lic",-2.75f},
    {"rea",-2.75f},{"dth",-2.75f},{"tri",-2.75f},{"iti",-2.75f},{"pro",-2.76f},{"nse",-2.76f},
    {"set",-2.77f},{"ore",-2.77f},{"ort",-2.77f},{"can",-2.78f},{"ice",-2.78f},{"era",-2.78f},
    {"edt",-2.78f},{"ess",-2.78f},{"ese",-2.79f},{"tor",-2.79f},{"wor",-2.79f},{"mma",-2.80f},
    {"hef",-2.80f},{"ean",-2.80f},{"ble",-2.80f},{"ins",-2.80f},{"lin",-2.81f},{"efo",-2.81f},
    {"but",-2.81f},{"tho",-2.82f},{"sof",-2.82f},{"str",-2.82f},{"nta",-2.82f},{"esa",-2.83f},
    {"pre",-2.83f},{"ein",-2.83f},{"let",-2.83f},{"nde",-2.84f},{"sed",-2.85f},{"whe",-2.85f},
    {"ind",-2.85f},{"ngt",-2.85f},{"ina",-2.85f},{"ass",-2.86f},{"orm",-2.86f},{"ens",-2.86f},
    {"ple",-2.86f},{"nti",-2.87f},{"sio",-2.87f},{"ite",-2.87f},{"tot",-2.87f},{"hel",-2.87f},
    {"rin",-2.87f},{"vim",-2.88f},{"ete",-2.88f},{"eme",-2.88f},{"nce",-2.88f},{"abl",-2.89f},
    {"ext",-2.89f},{"mat",-2.89f},{"one",-2.89f},{"yth",-2.89f},{"mpl",-2.89f},{"han",-2.89f},
    {"typ",-2.89f},{"fin",-2.90f},{"ill",-2.90f},{"nst",-2.90f},{"nte",-2.90f},{"ono",-2.90f},
    {"les",-2.90f},{"ssi",-2.90f},{"ove",-2.91f},{"rec",-2.91f},{"ona",-2.91f},{"san",-2.91f},
    {"ret",-2.91f},{"tan",-2.91f},{"ndo",-2.91f},{"cen",-2.91f},{"ndi",-2.92f},{"def",-2.92f},
    {"any",-2.92f},{"ute",-2.92f},{"ran",-2.92f},{"eof",-2.92f},{"ren",-2.93f},{"ode",-2.93f},
    {"par",-2.93f},{"tat",-2.93f},{"art",-2.93f},{"ara",-2.93f},{"dto",-2.94f},{"cla",-2.94f},
    {"ndt",-2.94f},{"het",-2.94f},{"ecu",-2.94f},{"tis",-2.94f},{"ant",-2.94f},{"und",-2.94f},
    {"eto",-2.94f},{"gth",-2.94f},{"mod",-2.94f},{"tof",-2.95f},{"las",-2.95f},{"tem",-2.95f},
    {"nam",-2.95f},{"eli",-2.95f},{"eri",-2.95f},{"wil",-2.95f},{"rib",-2.95f},{"ype",-2.96f},
    {"eis",-2.96f},{"ora",-2.96f},{"ork",-2.96f},{"eso",-2.96f},{"der",-2.96f},{"met",-2.96f},
    {"tex",-2.96f},{"nts",-2.96f},{"val",-2.96f},{"our",-2.97f},{"nge",-2.97f},{"cal",-2.98f},
    {"red",-2.98f},{"ain",-2.98f},{"cop",-2.98f},{"ear",-2.98f},{"dit",-2.98f},{"dif",-2.98f},
    {"dis",-2.99f},{"pti",-2.99f},{"ibu",-2.99f},{"hem",-2.99f},{"hth",-2.99f},{"act",-3.00f},
    {"ume",-3.00f},{"ang",-3.00f},{"tte",-3.00f},{"ifi",-3.00f},{"isa",-3.00f},{"igh",-3.00f},
    {"ght",-3.00f},{"epr",-3.00f},{"rat",-3.00f},{"per",-3.01f},{"erm",-3.01f},{"out",-3.01f},
    {"eve",-3.01f},{"ser",-3.01f},{"get",-3.01f},{"nin",-3.02f},{"eda",-3.02f},{"ses",-3.02f},
    {"ord",-3.02f},{"edo",-3.02f},{"tto",-3.02f},{"rma",-3.02f},{"enc",-3.02f},{"ram",-3.02f},
    {"nds",-3.03f},{"tar",-3.03f},{"alu",-3.03f},{"sec",-3.03f},{"ces",-3.03f},{"rac",-3.03f},
    {"sar",-3.03f},{"nal",-3.03f},{"jec",-3.03f},{"app",-3.03f},{"hep",-3.03f},{"inc",-3.03f},
    {"hed",-3.03f},{"rsi",-3.03f},{"ned",-3.03f},{"ouc",-3.03f},{"bje",-3.03f},{"ive",-3.04f},
    {"lis",-3.04f},{"eci",-3.04f},{"ica",-3.04f},{"sor",-3.05f},{"rre",-3.05f},{"ide",-3.05f},
    {"sli",-3.05f},{"tch",-3.05f},{"pec",-3.05f},{"ase",-3.05f},{"ede",-3.05f},{"ary",-3.06f},
    {"oun",-3.06f},{"ify",-3.06f},{"spe",-3.06f},{"ene",-3.06f},{"fer",-3.06f},{"equ",-3.06f},
    {"sea",-3.06f},{"eit",-3.06f},{"ele",-3.06f},{"har",-3.07f},{"edb",-3.07f},{"ste",-3.07f},
    {"rom",-3.07f},{"atc",-3.07f},{"isi",-3.07f},{"hee",-3.07f},{"end",-3.07f},{"sse",-3.07f},
    {"sno",-3.07f},{"oni",-3.07f},{"als",-3.07f},{"ast",-3.08f},{"gra",-3.08f},{"ena",-3.08f},
    {"eyo",-3.08f},{"ntt",-3.08f},{"ise",-3.08f},{"win",-3.08f},{"ori",-3.08f},{"ave",-3.08f},
    {"whi",-3.08f},{"ope",-3.08f},{"nga",-3.08f},{"cur",-3.08f},{"unc",-3.08f},{"fro",-3.08f},
    {"esi",-3.08f},{"ust",-3.09f},{"ema",-3.09f},{"omp",-3.09f},{"obj",-3.09f},{"sco",-3.09f},
    {"nto",-3.09f},{"sfo",-3.09f},{"low",-3.10f},{"eat",-3.10f},{"its",-3.10f},{"scr",-3.10f},
    {"ofa",-3.10f},{"fun",-3.10f},{"tit",-3.10f},{"ree",-3.10f},{"don",-3.10f},{"nda",-3.10f},
    {"tco",-3.10f},{"ten",-3.11f},{"llo",-3.11f},{"ace",-3.11f},{"epa",-3.11f},{"nct",-3.11f},
    {"rig",-3.11f},{"ose",-3.11f},{"ari",-3.11f},{"pat",-3.11f},{"esu",-3.11f},{"hei",-3.11f},
    {"ous",-3.11f},{"rst",-3.11f},{"mes",-3.11f},{"ead",-3.11f},{"arg",-3.11f},{"uca",-3.12f},
    {"cte",-3.12f},{"heo",-3.12f},{"cep",-3.12f},{"tes",-3.12f},{"hav",-3.12f},{"eas",-3.12f},
    {"lly",-3.12f},{"ern",-3.12f},{"hin",-3.12f},{"nof",-3.13f},{"gin",-3.13f},{"ali",-3.13f},
    {"tic",-3.13f},{"tai",-3.13f},{"dby",-3.13f},{"age",-3.14f},{"nyo",-3.14f},{"ept",-3.14f},
    {"eno",-3.14f},{"ewi",-3.14f},{"tst",-3.14f},{"exc",-3.14f},{"esp",-3.14f},{"cod",-3.14f},
    {"toa",-3.14f},{"eus",-3.14f},{"ane",-3.14f},{"lue",-3.14f},{"ire",-3.14f},{"ake",-3.14f},
    {"tyo",-3.15f},{"nex",-3.15f},{"ond",-3.15f},{"een",-3.15f},{"imp",-3.15f},{"onl",-3.15f},
    {"tht",-3.15f},{"eex",-3.16f},{"lea",-3.16f},{"exp",-3.16f},{"isl",-3.16f},{"ded",-3.16f},
    {"ffe",-3.16f},{"pos",-3.16f},{"nan",-3.16f},{"opy",-3.16f},{"evi",-3.16f},{"ber",-3.16f},
    {"isc",-3.16f},{"emo",-3.17f},{"ift",-3.17f},{"may",-3.17f},{"fyo",-3.17f},{"sit",-3.17f},
    {"ngs",-3.17f},{"odi",-3.17f},{"rto",-3.17f},{"ult",-3.17f},{"eor",-3.18f},{"exa",-3.18f},
    {"esc",-3.18f},{"swi",-3.18f},{"ies",-3.18f},{"tur",-3.18f},{"ini",-3.18f},{"ors",-3.19f},
    {"ual",-3.19f},{"key",-3.19f},{"aco",-3.19f},{"tab",-3.19f},{"rei",-3.19f},{"tim",-3.19f},
    {"rit",-3.19f},{"ref",-3.19f},{"sho",-3.19f},{"eac",-3.20f},{"ich",-3.20f},{"nes",-3.20f},
    {"sis",-3.20f},{"oul",-3.20f},{"led",-3.20f},{"ner",-3.20f},{"hic",-3.20f},{"ack",-3.20f},
    {"syo",-3.20f},{"edw",-3.21f},{"ogr",-3.21f},{"ana",-3.21f},{"iss",-3.21f},{"ero",-3.21f},
    {"hou",-3.21f},{"rar",-3.21f},{"hea",-3.21f},{"exe",-3.22f},{"pla",-3.22f},{"amp",-3.22f},
    {"rog",-3.22f},{"xce",-3.22f},{"uto",-3.22f},{"ano",-3.22f},{"eva",-3.22f},{"cri",-3.22f},
    {"war",-3.22f},{"mbe",-3.22f},{"toc",-3.23f},{"has",-3.23f},{"ncl",-3.23f},{"ime",-3.23f},
    {"fol",-3.23f},{"err",-3.23f},{"ome",-3.23f},{"nsi",-3.23f},{"see",-3.23f},{"rso",-3.23f},
    {"pli",-3.23f},{"xam",-3.23f},{"ewh",-3.23f},{"cat",-3.23f},{"uld",-3.23f},{"eed",-3.24f},
    {"den",-3.24f},{"ans",-3.24f},{"bra",-3.24f},{"nly",-3.24f},{"rep",-3.24f},{"eta",-3.24f},
    {"lle",-3.24f},{"lec",-3.24f},{"edf",-3.24f},{"clu",-3.24f},{"new",-3.24f},{"oll",-3.24f},
    {"twi",-3.24f},{"son",-3.25f},{"usi",-3.25f},{"num",-3.25f},{"sen",-3.25f},{"uti",-3.25f},
    {"tom",-3.25f},{"mak",-3.25f},{"hew",-3.25f},{"oma",-3.25f},{"nit",-3.26f},{"ral",-3.26f},
    {"lit",-3.26f},{"fie",-3.26f},{"nsa",-3.26f},{"cut",-3.26f},{"spa",-3.26f},{"nbe",-3.26f},
    {"xec",-3.26f},{"loc",-3.26f},{"tra",-3.26f},{"anc",-3.26f},{"add",-3.26f},{"eal",-3.27f},
    {"ata",-3.27f},{"nor",-3.27f},{"tea",-3.27f},{"ngi",-3.27f},{"ntr",-3.27f},{"ach",-3.27f},
    {"ria",-3.27f},{"nis",-3.27f},{"ett",-3.27f},{"sam",-3.27f},{"lso",-3.28f},{"top",-3.28f},
    {"oti",-3.28f},{"oum",-3.28f},{"erw",-3.28f},{"ouw",-3.28f},{"che",-3.28f},{"isn",-3.28f},
    {"tal",-3.28f},{"sub",-3.28f},{"lud",-3.28f},{"ipt",-3.28f},{"sca",-3.28f},{"tet",-3.29f},
    {"lem",-3.29f},{"min",-3.29f},{"eca",-3.29f},{"rco",-3.29f},{"urs",-3.29f},{"rex",-3.29f},
    {"sas",-3.29f},{"dow",-3.29f},{"itt",-3.29f},{"erc",-3.29f},{"mus",-3.29f},{"rou",-3.29f},
    {"nco",-3.29f},{"twa",-3.29f},{"rip",-3.29f},{"pin",-3.29f},{"mth",-3.30f},{"ewo",-3.30f},
    {"por",-3.30f},{"opt",-3.30f},{"dfo",-3.30f},{"rgu",-3.30f},{"tos",-3.30f},{"suc",-3.30f},
    {"ech",-3.30f},{"sti",-3.31f},{"ror",-3.31f},{"gum",-3.31f},{"byt",-3.31f},{"tli",-3.31f},
    {"ttr",-3.31f},{"ubl",-3.31f},{"sus",-3.31f},{"lib",-3.31f},{"sal",-3.31f},{"vet",-3.31f},
    {"efu",-3.31f},{"ial",-3.31f},{"umb",-3.31f},{"que",-3.31f},{"ory",-3.31f},{"des",-3.31f},
    {"mor",-3.32f},{"odu",-3.32f},{"mea",-3.32f},{"lei",-3.32f},{"mov",-3.32f},{"cif",-3.32f},
    {"heb",-3.32f},{"bli",-3.32f},{"two",-3.32f},{"rti",-3.32f},{"hod",-3.32f},{"tsa",-3.33f},
    {"nfo",-3.33f},{"dwi",-3.33f},{"enu",-3.33f},{"var",-3.33f},{"sel",-3.33f},{"non",-3.33f},
    {"swh",-3.33f},{"rem",-3.33f},{"yin",-3.33f},{"pac",-3.33f},{"ied",-3.33f},{"cor",-3.33f},
    {"tse",-3.33f},{"etu",-3.33f},{"dan",-3.33f},{"ibr",-3.33f},{"anb",-3.33f},{"uch",-3.33f},
    {"wan",-3.34f},{"ure",-3.34f},{"rev",-3.34f},{"gen",-3.34f},{"sei",-3.34f},{"way",-3.34f},
    {"ost",-3.34f},{"sst",-3.34f},{"dir",-3.34f},{"nar",-3.34f},{"lti",-3.34f},{"now",-3.35f},
    {"oes",-3.35f},{"seq",-3.35f},{"rmi",-3.35f},{"aus",-3.35f},{"unt",-3.35f},{"syn",-3.35f},
    {"eti",-3.35f},{"dst",-3.35f},{"ven",-3.35f},{"urr",-3.35f},{"sre",-3.35f},{"asa",-3.35f},
    {"heg",-3.35f},{"tfo",-3.35f},{"sde",-3.35f},{"lat",-3.35f},{"eif",-3.35f},{"urn",-3.35f},
    {"ato",-3.35f},{"elo",-3.35f},{"rte",-3.36f},{"asi",-3.36f},{"lth",-3.36f},{"lef",-3.36f},
    {"ngo",-3.36f},{"ety",-3.36f},{"uen",-3.36f},{"isp",-3.36f},{"som",-3.36f},{"tre",-3.36f},
    {"fir",-3.36f},{"ict",-3.36f},{"how",-3.36f},{"onc",-3.36f},{"ris",-3.36f},{"det",-3.37f},
    {"nso",-3.37f},{"ani",-3.37f},{"len",-3.37f},{"oco",-3.37f},{"chi",-3.37f},{"doe",-3.37f},
    {"ail",-3.37f},{"rch",-3.37f},{"irs",-3.37f},{"cts",-3.37f},{"ard",-3.38f},{"ule",-3.38f},
    {"inf",-3.38f},{"cet",-3.38f},{"xpr",-3.38f},{"fte",-3.38f},{"ota",-3.38f},{"nat",-3.38f},
    {"kin",-3.38f},{"map",-3.38f},{"ign",-3.38f},{"bac",-3.38f},{"anu",-3.38f},{"tbe",-3.38f},
    {"ote",-3.39f},{"pen",-3.39f},{"ecl",-3.39f},{"ryo",-3.39f},{"cre",-3.39f},{"ofi",-3.39f},
    {"orr",-3.39f},{"tma",-3.39f},{"fic",-3.40f},{"dco",-3.40f},{"isu",-3.40f},{"lar",-3.40f},
    {"pub",-3.40f},{"ude",-3.40f},{"ows",-3.40f},{"orc",-3.40f},{"oin",-3.40f},{"cto",-3.40f},
    {"dat",-3.40f},{"ovi",-3.40f},{"sma",-3.40f},{"sou",-3.40f},{"doc",-3.41f},{"qui",-3.41f},
    {"cum",-3.41f},{"ita",-3.41f},{"hev",-3.41f},{"alp",-3.41f},{"owi",-3.41f},{"run",-3.41f},
    {"esw",-3.41f},{"nve",-3.41f},{"cov",-3.41f},{"inv",-3.41f},{"net",-3.41f},{"aty",-3.41f},
    {"urc",-3.41f},{"esn",-3.41f},{"lyt",-3.42f},{"dof",-3.42f},{"dic",-3.42f},{"yan",-3.42f},
    {"tso",-3.42f},{"erp",-3.42f},{"nus",-3.42f},{"das",-3.42f},{"rro",-3.42f},{"del",-3.42f},
    {"ela",-3.42f},{"ges",-3.42f},{"ocu",-3.42f},{"tly",-3.42f},
};

static float tri_ll[26][26][26];     /* filled from TRIGRAMS[] at start-up */

typedef struct { char key[27]; double score; } Result;   /* key[c] = plaintext letter for cipher letter c */

static void read_line(const char *prompt, char *buf, size_t n)
{
    printf("%s", prompt);
    fflush(stdout);
    if (!fgets(buf, (int)n, stdin)) { printf("\n"); exit(0); }
    buf[strcspn(buf, "\r\n")] = '\0';
}

static void init_tables(void)
{
    int a, b, c, i;
    for (a = 0; a < 26; a++) for (b = 0; b < 26; b++) for (c = 0; c < 26; c++) tri_ll[a][b][c] = TRI_FLOOR;
    for (i = 0; i < NUM_TRIGRAMS; i++)
        tri_ll[TRIGRAMS[i].s[0] - 'a'][TRIGRAMS[i].s[1] - 'a'][TRIGRAMS[i].s[2] - 'a'] = TRIGRAMS[i].ll;
}

/* letters of the ciphertext as 0..25, no punctuation */
static int extract(const char *s, int *v)
{
    int n = 0, i;
    for (i = 0; s[i]; i++) if (isalpha((unsigned char)s[i])) v[n++] = toupper((unsigned char)s[i]) - 'A';
    return n;
}

/* key[c] is the plaintext letter ('A'..'Z') assigned to cipher letter c */
static double score_key(const int *ct, int n, const char *key)
{
    double s = 0;
    int i;
    for (i = 0; i + 1 < n; i++) {
        int a = key[ct[i]] - 'A', b = key[ct[i + 1]] - 'A';
        s += BIGRAM_LL[a][b];
        if (i + 2 < n) s += tri_ll[a][b][key[ct[i + 2]] - 'A'];
    }
    return s;
}

static void initial_key(const int *ct, int n, char *key)
{
    int cnt[26] = {0}, idx[26], i, j;
    for (i = 0; i < n; i++) cnt[ct[i]]++;
    for (i = 0; i < 26; i++) idx[i] = i;
    for (i = 0; i < 26; i++)
        for (j = i + 1; j < 26; j++)
            if (cnt[idx[j]] > cnt[idx[i]]) { int t = idx[i]; idx[i] = idx[j]; idx[j] = t; }
    for (i = 0; i < 26; i++) key[idx[i]] = FREQ_ORDER[i];
    key[26] = '\0';
}

static void shuffle_some(char *key, int swaps)
{
    int i;
    for (i = 0; i < swaps; i++) {
        int a = rand() % 26, b = rand() % 26;
        char t = key[a]; key[a] = key[b]; key[b] = t;
    }
}

static double climb(const int *ct, int n, char *key)
{
    double best = score_key(ct, n, key);
    int improved = 1, a, b;
    while (improved) {
        improved = 0;
        for (a = 0; a < 25; a++)
            for (b = a + 1; b < 26; b++) {
                char t = key[a]; key[a] = key[b]; key[b] = t;
                double s = score_key(ct, n, key);
                if (s > best + 1e-9) { best = s; improved = 1; }
                else { t = key[a]; key[a] = key[b]; key[b] = t; }
            }
    }
    return best;
}

static int cmp(const void *a, const void *b)
{
    double d = ((const Result *)b)->score - ((const Result *)a)->score;
    return (d > 0) - (d < 0);
}

static void apply(const char *cipher, const char *key, char *out)
{
    int i;
    for (i = 0; cipher[i]; i++) {
        if (isupper((unsigned char)cipher[i]))      out[i] = key[cipher[i] - 'A'];
        else if (islower((unsigned char)cipher[i])) out[i] = (char)tolower((unsigned char)key[cipher[i] - 'a']);
        else out[i] = cipher[i];
    }
    out[i] = '\0';
}

static void attack(const char *cipher, int topn)
{
    static int ct[MAXLEN];
    int n = extract(cipher, ct), r, i, nres = 0, k;
    Result res[MAXKEEP + 1];
    char key[27], out[MAXLEN];

    if (n < 30) printf("\n  (Warning: only %d letters - results will be unreliable.)\n", n);

    printf("\n  Searching (%d restarts) ", RESTARTS);
    fflush(stdout);
    for (r = 0; r < RESTARTS; r++) {
        int dup = 0;
        double s;
        initial_key(ct, n, key);
        if (r % 2 == 0) shuffle_some(key, r == 0 ? 0 : 2 + r % 16);   /* perturb the frequency-based key */
        else            shuffle_some(key, 60);                         /* (almost) completely random start */
        s = climb(ct, n, key);
        for (k = 0; k < nres; k++) if (!strcmp(res[k].key, key)) dup = 1;
        if (!dup) {
            if (nres < MAXKEEP) { strcpy(res[nres].key, key); res[nres].score = s; nres++; }
            else if (s > res[nres - 1].score) { strcpy(res[nres - 1].key, key); res[nres - 1].score = s; }
            qsort(res, (size_t)nres, sizeof(Result), cmp);
        }
        if (r % 10 == 0) { putchar('.'); fflush(stdout); }
    }
    printf(" done (%d distinct keys found)\n", nres);

    if (topn > nres) topn = nres;
    printf("\n  Showing the %d most likely plaintexts (key maps cipher A..Z -> plain letters):\n", topn);
    for (i = 0; i < topn; i++) {
        apply(cipher, res[i].key, out);
        printf("\n  #%-2d score %.1f   key: %s\n      %.220s%s\n", i + 1, res[i].score, res[i].key,
               out, strlen(out) > 220 ? "..." : "");
    }
}

int main(void)
{
    char cipher[MAXLEN], buf[64];
    int topn;

    srand((unsigned)time(NULL));
    init_tables();

    printf("=========================================\n");
    printf("  FREQUENCY ATTACK ON MONOALPHABETIC CIPHER\n");
    printf("=========================================\n");

    for (;;) {
        read_line("\nEnter ciphertext (blank to quit): ", cipher, sizeof cipher);
        if (!cipher[0]) break;
        read_line("Give me the top N possible plaintexts, N = (default 10): ", buf, sizeof buf);
        topn = buf[0] ? atoi(buf) : 10;
        if (topn < 1) topn = 10;
        attack(cipher, topn);
    }
    return 0;
}
