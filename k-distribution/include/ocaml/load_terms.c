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
#define RESOURCE(name) \
extern char _binary_##name##_start[];\
extern char _binary_##name##_end[];\
value load_##name(value unit) {\
    CAMLparam1(unit);\
    CAMLreturn(load_symbol(_binary_##name##_start, _binary_##name##_end));\
}

RESOURCE(kore_term)
RESOURCE(marshal_term)
RESOURCE(plugin_path)
RESOURCE(native_binary)
