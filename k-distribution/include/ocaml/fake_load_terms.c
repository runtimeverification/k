#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>

value load_native_binary(value unit) {
  CAMLparam1(unit);
  CAMLlocal1(s);
  s = caml_alloc_string(0);
  CAMLreturn(s);
}
