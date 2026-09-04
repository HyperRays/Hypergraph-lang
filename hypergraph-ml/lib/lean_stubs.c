#include <pthread.h>
#include <stdint.h>

#include <caml/alloc.h>
#include <caml/fail.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>
#include <lean/lean.h>

extern void lean_initialize(void);
extern lean_object *initialize_HypergraphML_HypergraphML(uint8_t builtin);
extern lean_object *hypergraphml_bridge(lean_object *input);

static pthread_once_t hypergraphml_once = PTHREAD_ONCE_INIT;
static pthread_mutex_t hypergraphml_mutex = PTHREAD_MUTEX_INITIALIZER;
static int hypergraphml_initialized = 0;

static void hypergraphml_initialize(void) {
  lean_initialize();
  lean_object *result = initialize_HypergraphML_HypergraphML(1);
  if (lean_io_result_is_error(result)) {
    lean_io_result_show_error(result);
    lean_dec_ref(result);
    return;
  }
  lean_dec_ref(result);
  lean_io_mark_end_initialization();
  hypergraphml_initialized = 1;
}

CAMLprim value caml_hypergraphml_bridge(value input) {
  CAMLparam1(input);
  CAMLlocal1(output);

  pthread_once(&hypergraphml_once, hypergraphml_initialize);
  if (!hypergraphml_initialized) {
    caml_failwith("failed to initialize the Lean runtime");
  }

  pthread_mutex_lock(&hypergraphml_mutex);
  lean_object *lean_input = lean_mk_string(String_val(input));
  lean_object *lean_output = hypergraphml_bridge(lean_input);
  output = caml_copy_string(lean_string_cstr(lean_output));
  lean_dec(lean_output);
  pthread_mutex_unlock(&hypergraphml_mutex);

  CAMLreturn(output);
}

