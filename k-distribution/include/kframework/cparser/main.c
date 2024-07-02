#include "node.h"
#include "parser.tab.h"
#include "scanner.h"

#include <assert.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct string_buffer {
  FILE *fp;
  char *buf;
  size_t capacity;
  size_t idx;
};

struct string_buffer string_buffer_new_memory(size_t initial) {
  assert(initial > 0 && "Invalid initial capacity");

  char *buf = malloc(sizeof(*buf) * initial);
  buf[0] = '\0';

  struct string_buffer ret
      = {.fp = NULL, .buf = buf, .capacity = initial, .idx = 0};
  return ret;
}

struct string_buffer string_buffer_new_file(FILE *fp) {
  struct string_buffer ret = {.fp = fp, .buf = NULL, .capacity = 0, .idx = 0};
  return ret;
}

void string_buffer_grow(struct string_buffer *sb) {
  if (sb->fp) {
    return;
  }

  size_t old_cap = sb->capacity;
  size_t new_cap = old_cap * 2;

  sb->buf = realloc(sb->buf, new_cap);
  sb->buf[old_cap] = 0;
  sb->capacity = new_cap;
}

int buf_printf(struct string_buffer *sb, char const *format, ...) {
  va_list args;
  va_start(args, format);

  if (sb->fp) {
    va_list copy;
    va_copy(copy, args);
    int result = vfprintf(sb->fp, format, copy);
    va_end(copy);

    va_end(args);
    return result;
  } else {
    va_list copy;
    va_copy(copy, args);
    int required = vsnprintf(NULL, 0, format, copy) + 1;
    va_end(copy);

    while ((sb->capacity - sb->idx) < required) {
      string_buffer_grow(sb);
    }

    va_list copy_2;
    va_copy(copy_2, args);
    vsnprintf(sb->buf + sb->idx, required, format, args);
    va_end(copy_2);

    sb->idx += required - 1;
    va_end(args);
    return required;
  }
}

static void append(char *buf, size_t *bufidx, char *str, size_t len) {
  memcpy(buf + *bufidx, str, len);
  *bufidx = *bufidx + len;
}

char *enquote(char *str) {
  size_t len = strlen(str);
  size_t bufidx = 1;
  char *res = malloc(len * 4 + 3);
  res[0] = '"';
  for (int idx = 0; idx < len; idx++) {
    char c = str[idx];
    switch (c) {
    case '"': append(res, &bufidx, "\\\"", 2); break;
    case '\\': append(res, &bufidx, "\\\\", 2); break;
    case '\n': append(res, &bufidx, "\\n", 2); break;
    case '\t': append(res, &bufidx, "\\t", 2); break;
    case '\r': append(res, &bufidx, "\\r", 2); break;
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

static bool equalsSymbol(node *x0, node *x1) {
  return strcmp(x0->symbol, x1->symbol) == 0;
}

bool equalsNode(node *x0, node *x1) {
  if (x0->str != x1->str) {
    return false;
  }
  if (x0->str) {
    return strcmp(x0->symbol, x1->symbol) == 0;
  } else {
    if (!(equalsSymbol(x0, x1) && x0->nchildren == x1->nchildren)) {
      return false;
    }
    for (size_t i = 0; i < x0->nchildren; i++) {
      if (!equalsNode(x0->children[i], x1->children[i])) {
        return false;
      }
    }
    return true;
  }
}

// Define an ordering on nodes as follows:
//   - Any string node is < any constructor node
//   - String nodes are compared via strcmp
//   - Constructor nodes are:
//     - First compared by symbol via strcmp
//     - If their symbols are identical, they are compared recursively:
//       - First by their number of children
//       - Then lexicographically over their children
//
// Returns true if x0 < x1
bool ltNode(node *x0, node *x1) {
    if (x0->str && x1->str) {
        return strcmp(x0->symbol, x1->symbol) < 1;
    }

    if (x0->str && !x1->str) {
        return true;
    }

    if (!x0->str && x1->str) {
        return false;
    }

    if (!equalsSymbol(x0, x1)) {
        return strcmp(x0->symbol, x1->symbol) < 1;
    }

    if (x0->nchildren != x1->nchildren) {
        return x0->nchildren < x1->nchildren;
    }

    for (size_t i = 0; i < x0->nchildren; i++) {
        if (!equalsNode(x0->children[i], x1->children[i])) {
            return ltNode(x0->children[i], x1->children[i]);
        }
    }

    return false;
}

char *injSymbol(char *lesser, char *greater) {
  char *prefix = "inj{";
  char *infix = ", ";
  char *suffix = "}";
  size_t len = strlen(prefix) + strlen(suffix) + strlen(lesser)
               + strlen(greater) + strlen(infix) + 1;
  char *symbol = malloc(len);
  strcpy(symbol, prefix);
  strcat(symbol, lesser);
  strcat(symbol, infix);
  strcat(symbol, greater);
  strcat(symbol, suffix);
  return symbol;
}

YYSTYPE mergeAmb(YYSTYPE x0, YYSTYPE x1) {
  if (equalsNode(x0.nterm, x1.nterm)) {
    return x0;
  }

  if(ltNode(x1.nterm, x0.nterm)) {
    YYSTYPE tmp = x0;
    x0 = x1;
    x1 = tmp;
  }

  node *n = malloc(sizeof(node) + sizeof(node *) * 2);
  node *x0n = x0.nterm;
  node *x1n = x1.nterm;
  char *prefix = "Lblamb{";
  char *suffix = "}";
  size_t len = strlen(prefix) + strlen(suffix) + strlen(x0n->sort) + 1;
  char *symbol = malloc(len);
  strcpy(symbol, prefix);
  strcat(symbol, x0n->sort);
  strcat(symbol, suffix);
  n->location = x0n->location;
  n->hasLocation = false;
  n->symbol = symbol;
  n->sort = x0n->sort;
  n->str = false;
  n->nchildren = 2;
  n->children[0] = x0n;
  n->children[1] = x1n;
  YYSTYPE result = {.nterm = n};
  return result;
}

void print(struct string_buffer *sb, node *current) {
  if (current->hasLocation) {
    buf_printf(sb, "Lbl'Hash'location{");
    buf_printf(sb, "%s", current->sort);
    buf_printf(sb, "}(");
  }
  buf_printf(sb, "%s", current->symbol);
  if (!current->str) {
    buf_printf(sb, "(");
    for (int i = 0; i < current->nchildren; i++) {
      node *child = current->children[i];
      print(sb, child);
      if (i != current->nchildren - 1)
        buf_printf(sb, ",");
    }
    buf_printf(sb, ")");
  }
  if (current->hasLocation) {
    buf_printf(
        sb,
        ", \\dv{SortString{}}(%s), \\dv{SortInt{}}(\"%d\"), "
        "\\dv{SortInt{}}(\"%d\"), \\dv{SortInt{}}(\"%d\"), "
        "\\dv{SortInt{}}(\"%d\"))",
        enquote(current->location.filename), current->location.first_line,
        current->location.first_column, current->location.last_line,
        current->location.last_column);
  }
}

extern node *result;
extern char *filename;

static void parse_internal(
    struct string_buffer *sb, char *program_name, char *input_file,
    char *location_file) {
  yyscan_t scanner;
  yylex_init(&scanner);

  filename = location_file;

  FILE *f = fopen(input_file, "r");
  if (!f) {
    int len = strlen(program_name) + strlen(input_file) + 19;
    char *buf = malloc(len);
    snprintf(buf, len, "%s: cannot access '%s'", program_name, input_file);
    perror(buf);
    exit(1);
  }

  yyset_in(f, scanner);

  int status = yyparse(scanner);
  if (status) {
    exit(status);
  }

  print(sb, result);
  yylex_destroy(scanner);
}

#define CONCAT(X, Y) X##Y
#define NAME(sort) CONCAT(parse_, sort)
#define PARSER_FUNCTION NAME(K_BISON_PARSER_SORT)

#define XSTR(S) #S
#define STR(S) XSTR(S)

char *PARSER_FUNCTION(char *input_file, char *location_file) {
  struct string_buffer sb = string_buffer_new_memory(1024);

  if (!location_file) {
    location_file = input_file;
  }

  parse_internal(&sb, STR(PARSER_FUNCTION), input_file, location_file);
  return sb.buf;
}

#ifdef K_BISON_PARSER_MAIN

int main(int argc, char **argv) {
  if (argc < 2 || argc > 3) {
    fprintf(stderr, "usage: %s <file> [<filename>]\n", argv[0]);
    exit(1);
  }

  char *location_file;
  if (argc == 3) {
    location_file = argv[2];
  } else {
    location_file = argv[1];
  }

  struct string_buffer sb = string_buffer_new_file(stdout);
  parse_internal(&sb, argv[0], argv[1], location_file);
  printf("\n");
}

#endif
