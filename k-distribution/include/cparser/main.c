#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "node.h"
#include "parser.tab.h"
#include "scanner.h"

static void append(char *buf, size_t *bufidx, char *str, size_t len) {
  memcpy(buf+*bufidx, str, len);
  *bufidx = *bufidx + len;
}

char *enquote(char *str) {
  size_t len = strlen(str);
  size_t bufidx = 1;
  char *res = malloc(len*4+3);
  res[0] = '"';
  for(int idx = 0; idx < len; idx++) {
    char c = str[idx];
    switch (c) {
      case '"':  append(res, &bufidx, "\\\"", 2); break;
      case '\\': append(res, &bufidx, "\\\\", 2); break;
      case '\n': append(res, &bufidx, "\\n", 2);  break;
      case '\t': append(res, &bufidx, "\\t", 2);  break;
      case '\r': append(res, &bufidx, "\\r", 2);  break;
      default:
        if (c >= 32 && c < 127) {
          append(res, &bufidx, &c, 1);
        } else {
          char buf[5];
          sprintf(buf, "\\x%02hhx", (unsigned char)c);
	  append(res, &bufidx, buf, 4);
        }
    }
  }
  append(res, &bufidx, "\"", 2);
  return res;
}
	
void print(node *current) {
  printf("%s", current->symbol);
  if (!current->str) {
    printf("(");
    for (int i = 0; i < current->nchildren; i++) {
      node *child = current->children[i];
      print(child);
      if (i != current->nchildren - 1) printf(",");
    }
    printf(")");
  }
}

extern node *result;

int main(int argc, char **argv) {
  yyscan_t scanner;
  yylex_init(&scanner); 
  yyset_in(fopen(argv[1], "r"), scanner);
  yyparse(scanner);
  print(result);
  printf("\n");
  yylex_destroy(scanner);
}
