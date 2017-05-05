#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <string.h>
value load_symbol(char* start, char* end) {
  CAMLparam0();
  CAMLlocal1(s);
  size_t len = end-start;
  s = caml_alloc_string(len);
  memcpy(String_val(s), start, len);
  CAMLreturn(s);
}

extern char _binary_kore_term_start[];
extern char _binary_kore_term_end[];
value load_kore_term(value unit) {
    CAMLparam1(unit);
    CAMLreturn(load_symbol(_binary_kore_term_start, _binary_kore_term_end));
}
extern char _binary_marshal_term_start[];
extern char _binary_marshal_term_end[];
value load_marshal_term(value unit) {
    CAMLparam1(unit);
    CAMLreturn(load_symbol(_binary_marshal_term_start, _binary_marshal_term_end));
}

