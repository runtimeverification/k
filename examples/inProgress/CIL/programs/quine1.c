/* A simple quine (self-printing program), in standard C. */
 
/* Note: in designing this quine, we have tried to make the code clear
 * and readable, not concise and obscure as many quines are, so that
 * the general principle can be made clear at the expense of length.
 * In a nutshell: use the same data structure (called "progdata"
 * below) to output the program code (which it represents) and its own
 * textual representation. */
 
#include <stdio.h>
 
void quote(const char *s)
     /* This function takes a character string s and prints the
      * textual representation of s as it might appear formatted
      * in C code. */
{
    int i;
 
    printf("    \"");
    for (i=0; s[i]; ++i) {
        /* Certain characters are quoted. */
        if (s[i] == '\\')
            printf("\\\\");
        else if (s[i] == '"')
            printf("\\\"");
        else if (s[i] == '\n')
            printf("\\n");
        /* Others are just printed as such. */
        else
            printf("%c", s[i]);
        /* Also insert occasional line breaks. */
        if (i % 48 == 47)
            printf("\"\n    \"");
    }
    printf("\"");
}
 
/* What follows is a string representation of the program code,
 * from beginning to end (formatted as per the quote() function
 * above), except that the string _itself_ is coded as two
 * consecutive '@' characters. */
const char progdata[] =
    "/* A simple quine (self-printing program), in st"
    "andard C. */\n\n/* Note: in designing this quine, "
    "we have tried to make the code clear\n * and read"
    "able, not concise and obscure as many quines are"
    ", so that\n * the general principle can be made c"
    "lear at the expense of length.\n * In a nutshell:"
    " use the same data structure (called \"progdata\"\n"
    " * below) to output the program code (which it r"
    "epresents) and its own\n * textual representation"
    ". */\n\n#include <stdio.h>\n\nvoid quote(const char "
    "*s)\n     /* This function takes a character stri"
    "ng s and prints the\n      * textual representati"
    "on of s as it might appear formatted\n      * in "
    "C code. */\n{\n    int i;\n\n    printf(\"    \\\"\");\n "
    "   for (i=0; s[i]; ++i) {\n        /* Certain cha"
    "racters are quoted. */\n        if (s[i] == '\\\\')"
    "\n            printf(\"\\\\\\\\\");\n        else if (s["
    "i] == '\"')\n            printf(\"\\\\\\\"\");\n        e"
    "lse if (s[i] == '\\n')\n            printf(\"\\\\n\");"
    "\n        /* Others are just printed as such. */\n"
    "        else\n            printf(\"%c\", s[i]);\n   "
    "     /* Also insert occasional line breaks. */\n "
    "       if (i % 48 == 47)\n            printf(\"\\\"\\"
    "n    \\\"\");\n    }\n    printf(\"\\\"\");\n}\n\n/* What fo"
    "llows is a string representation of the program "
    "code,\n * from beginning to end (formatted as per"
    " the quote() function\n * above), except that the"
    " string _itself_ is coded as two\n * consecutive "
    "'@' characters. */\nconst char progdata[] =\n@@;\n\n"
    "int main(void)\n     /* The program itself... */\n"
    "{\n    int i;\n\n    /* Print the program code, cha"
    "racter by character. */\n    for (i=0; progdata[i"
    "]; ++i) {\n        if (progdata[i] == '@' && prog"
    "data[i+1] == '@')\n            /* We encounter tw"
    "o '@' signs, so we must print the quoted\n       "
    "      * form of the program code. */\n        {\n "
    "           quote(progdata);    /* Quote all. */\n"
    "            i++;                /* Skip second '"
    "@'. */\n        } else\n            printf(\"%c\", p"
    "rogdata[i]);  /* Print character. */\n    }\n    r"
    "eturn 0;\n}\n";
 
int main(void)
     /* The program itself... */
{
    int i;
 
    /* Print the program code, character by character. */
    for (i=0; progdata[i]; ++i) {
        if (progdata[i] == '@' && progdata[i+1] == '@')
            /* We encounter two '@' signs, so we must print the quoted
             * form of the program code. */
        {
            quote(progdata);    /* Quote all. */
            i++;                /* Skip second '@'. */
        } else
            printf("%c", progdata[i]);  /* Print character. */
    }
    return 0;
}
