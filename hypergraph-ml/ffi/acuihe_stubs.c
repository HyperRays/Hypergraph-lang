#include "acuihe_native.h"
#include <caml/alloc.h>
#include <caml/custom.h>
#include <caml/fail.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>
#include <caml/threads.h>
#include <pthread.h>
#include <stdlib.h>

/* Lean's host-runtime entry points are exported but not declared in lean.h. */
void lean_initialize(void);
void lean_initialize_thread(void);
void lean_finalize_thread(void);

static pthread_once_t runtime_once = PTHREAD_ONCE_INIT;
static pthread_key_t thread_key;
static const char *runtime_error = NULL;

static void finalize_thread(void *registered) {
  if (registered != NULL) lean_finalize_thread();
}

static void initialize_runtime(void) {
  if (pthread_key_create(&thread_key, finalize_thread) != 0) {
    runtime_error = "ACUIhE: cannot allocate Lean thread-local state";
    return;
  }
  lean_initialize();
  lean_object *result = initialize_HypergraphFFI_HypergraphFFI(1);
  if (!lean_io_result_is_ok(result)) {
    lean_io_result_show_error(result);
    lean_dec(result);
    runtime_error = "ACUIhE: Lean module initialization failed";
    return;
  }
  lean_dec(result);
  lean_io_mark_end_initialization();
  if (acuihe_v1_abi_version(lean_box(0)) != 1) {
    runtime_error = "ACUIhE: incompatible native API version";
    return;
  }
  /* lean_initialize initialized this thread already. */
  if (pthread_setspecific(thread_key, (void *)1) != 0)
    runtime_error = "ACUIhE: cannot register the initial Lean thread";
}

static int enter_lean(void) {
  if (pthread_once(&runtime_once, initialize_runtime) != 0 || runtime_error != NULL)
    return 0;
  if (pthread_getspecific(thread_key) == NULL) {
    lean_initialize_thread();
    if (pthread_setspecific(thread_key, (void *)1) != 0) {
      lean_finalize_thread();
      return 0;
    }
  }
  return 1;
}

static void require_runtime(void) {
  if (!enter_lean()) caml_failwith(runtime_error != NULL ? runtime_error :
                                  "ACUIhE: cannot initialize this Lean thread");
}

enum handle_kind { TERM, GRAPH, SOLUTION, TEMPORARY };

struct handle {
  lean_object *object;
  enum handle_kind kind;
};

#define Handle_val(v) (*(struct handle **)Data_custom_val(v))

static void finalize_handle(value v) {
  struct handle *handle = Handle_val(v);
  if (handle == NULL) return;
  if (handle->object != NULL) {
    /* A finalizer can run on a domain that has not previously called Lean. */
    if (!enter_lean()) abort();
    lean_dec(handle->object);
  }
  free(handle);
  Handle_val(v) = NULL;
}

static struct custom_operations handle_ops = {
  "hypergraph.acuihe.native.v1", finalize_handle,
  custom_compare_default, custom_hash_default,
  custom_serialize_default, custom_deserialize_default,
  custom_compare_ext_default, custom_fixed_length_default
};

static value allocate_handle(enum handle_kind kind) {
  CAMLparam0();
  CAMLlocal1(result);
  result = caml_alloc_custom(&handle_ops, sizeof(struct handle *), 4096, 1048576);
  Handle_val(result) = NULL;
  struct handle *handle = malloc(sizeof(*handle));
  if (handle == NULL) caml_raise_out_of_memory();
  handle->object = NULL;
  handle->kind = kind;
  Handle_val(result) = handle;
  CAMLreturn(result);
}

static lean_object *borrow_handle(value v, enum handle_kind kind) {
  if (!Is_block(v) || Tag_val(v) != Custom_tag || Custom_ops_val(v) != &handle_ops ||
      Handle_val(v) == NULL || Handle_val(v)->object == NULL || Handle_val(v)->kind != kind)
    caml_invalid_argument("ACUIhE: invalid native handle");
  return Handle_val(v)->object;
}

static lean_object *own_handle(value v, enum handle_kind kind) {
  lean_object *object = borrow_handle(v, kind);
  lean_inc(object);
  return object;
}

static size_t symbol_id(value v) {
  if (!Is_long(v) || Long_val(v) < 0)
    caml_invalid_argument("ACUIhE: symbol IDs must be nonnegative OCaml integers");
  return (size_t)Long_val(v);
}

static void store_owned(struct handle *handle, lean_object *object) {
  /* OCaml values can cross domains or be finalized on another thread. */
  lean_mark_mt(object);
  handle->object = object;
}

CAMLprim value caml_acuihe_zero(value unit) {
  CAMLparam1(unit);
  CAMLlocal1(result);
  require_runtime();
  result = allocate_handle(TERM);
  store_owned(Handle_val(result), acuihe_v1_zero(lean_box(0)));
  CAMLreturn(result);
}

static value make_symbol(value name, int variable) {
  CAMLparam1(name);
  CAMLlocal1(result);
  size_t id = symbol_id(name);
  require_runtime();
  result = allocate_handle(TERM);
  store_owned(Handle_val(result), variable ? acuihe_v1_variable(id) : acuihe_v1_constant(id));
  CAMLreturn(result);
}

CAMLprim value caml_acuihe_constant(value name) { return make_symbol(name, 0); }
CAMLprim value caml_acuihe_variable(value name) { return make_symbol(name, 1); }

CAMLprim value caml_acuihe_add(value left, value right) {
  CAMLparam2(left, right);
  CAMLlocal1(result);
  require_runtime();
  borrow_handle(left, TERM);
  borrow_handle(right, TERM);
  result = allocate_handle(TERM);
  store_owned(Handle_val(result), acuihe_v1_add(own_handle(left, TERM), own_handle(right, TERM)));
  CAMLreturn(result);
}

CAMLprim value caml_acuihe_hom(value name, value body) {
  CAMLparam2(name, body);
  CAMLlocal1(result);
  size_t id = symbol_id(name);
  require_runtime();
  borrow_handle(body, TERM);
  result = allocate_handle(TERM);
  store_owned(Handle_val(result), acuihe_v1_hom(id, own_handle(body, TERM)));
  CAMLreturn(result);
}

CAMLprim value caml_acuihe_free(value body) {
  CAMLparam1(body);
  CAMLlocal1(result);
  require_runtime();
  borrow_handle(body, TERM);
  result = allocate_handle(TERM);
  store_owned(Handle_val(result), acuihe_v1_free(own_handle(body, TERM)));
  CAMLreturn(result);
}

typedef uint8_t (*binary_predicate)(lean_obj_arg, lean_obj_arg);

static value compare_handles(value left, value right, enum handle_kind kind, binary_predicate f) {
  CAMLparam2(left, right);
  require_runtime();
  borrow_handle(left, kind);
  borrow_handle(right, kind);
  lean_object *a = borrow_handle(left, kind), *b = borrow_handle(right, kind);
  caml_release_runtime_system();
  lean_inc(a);
  lean_inc(b);
  uint8_t answer = f(a, b);
  caml_acquire_runtime_system();
  CAMLreturn(Val_bool(answer));
}

CAMLprim value caml_acuihe_equal(value a, value b) { return compare_handles(a, b, TERM, acuihe_v1_equal); }
CAMLprim value caml_acuihe_below(value a, value b) { return compare_handles(a, b, TERM, acuihe_v1_below); }
CAMLprim value caml_acuihe_graph_equal(value a, value b) { return compare_handles(a, b, GRAPH, acuihe_v1_graph_equal); }
CAMLprim value caml_acuihe_graph_below(value a, value b) { return compare_handles(a, b, GRAPH, acuihe_v1_graph_below); }

CAMLprim value caml_acuihe_normalize(value term) {
  CAMLparam1(term);
  CAMLlocal1(result);
  require_runtime();
  borrow_handle(term, TERM);
  result = allocate_handle(GRAPH);
  struct handle *output = Handle_val(result);
  lean_object *input = borrow_handle(term, TERM);
  caml_release_runtime_system();
  lean_inc(input);
  /* The C-heap holder stays fixed if OCaml compacts while the lock is released.
     Store before reacquiring: pending OCaml exceptions then still release the
     result through the rooted holder's finalizer. */
  store_owned(output, acuihe_v1_normalize(input));
  caml_acquire_runtime_system();
  CAMLreturn(result);
}

static lean_object *make_equations(value equations) {
  if (!Is_block(equations) || Tag_val(equations) != 0)
    caml_invalid_argument("ACUIhE: expected an equation array");
  mlsize_t count = Wosize_val(equations);
  /* Validate before allocating native objects, so invalid arguments cannot
     leak a partially constructed Lean array. */
  for (mlsize_t i = 0; i < count; ++i) {
    value pair = Field(equations, i);
    if (!Is_block(pair) || Tag_val(pair) != 0 || Wosize_val(pair) != 2)
      caml_invalid_argument("ACUIhE: expected a pair of terms");
    borrow_handle(Field(pair, 0), TERM);
    borrow_handle(Field(pair, 1), TERM);
  }
  lean_object *array = lean_mk_empty_array_with_capacity(lean_box(count));
  for (mlsize_t i = 0; i < count; ++i) {
    value pair = Field(equations, i);
    lean_object *entry = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(entry, 0, own_handle(Field(pair, 0), TERM));
    lean_ctor_set(entry, 1, own_handle(Field(pair, 1), TERM));
    array = lean_array_push(array, entry);
  }
  return array;
}

CAMLprim value caml_acuihe_is_unifiable(value equations) {
  CAMLparam1(equations);
  CAMLlocal1(holder);
  require_runtime();
  holder = allocate_handle(TEMPORARY);
  struct handle *request = Handle_val(holder);
  store_owned(request, make_equations(equations));
  caml_release_runtime_system();
  lean_object *input = request->object;
  request->object = NULL;
  uint8_t answer = acuihe_v1_is_unifiable(input);
  caml_acquire_runtime_system();
  CAMLreturn(Val_bool(answer));
}

CAMLprim value caml_acuihe_solve(value equations) {
  CAMLparam1(equations);
  CAMLlocal2(holder, result);
  require_runtime();
  holder = allocate_handle(SOLUTION);
  struct handle *output = Handle_val(holder);
  store_owned(output, make_equations(equations));
  caml_release_runtime_system();
  lean_object *input = output->object;
  output->object = NULL;
  store_owned(output, acuihe_v1_solve(input));
  caml_acquire_runtime_system();
  lean_object *option = output->object;
  if (lean_is_scalar(option)) {
    lean_dec(option);
    output->object = NULL;
    CAMLreturn(Val_int(0));
  }
  lean_object *solution = lean_ctor_get(option, 0);
  lean_inc(solution);
  output->object = solution;
  lean_dec(option);
  result = caml_alloc(1, 0);
  Store_field(result, 0, holder);
  CAMLreturn(result);
}

CAMLprim value caml_acuihe_solution_get(value solution, value name) {
  CAMLparam2(solution, name);
  CAMLlocal1(result);
  size_t id = symbol_id(name);
  require_runtime();
  borrow_handle(solution, SOLUTION);
  result = allocate_handle(GRAPH);
  struct handle *output = Handle_val(result);
  lean_object *input = borrow_handle(solution, SOLUTION);
  caml_release_runtime_system();
  lean_inc(input);
  store_owned(output, acuihe_v1_solution_get(input, id));
  caml_acquire_runtime_system();
  CAMLreturn(result);
}

static mlsize_t list_length(lean_object *list) {
  mlsize_t length = 0;
  while (!lean_is_scalar(list)) {
    if (length == Max_wosize) caml_failwith("ACUIhE: native layer exceeds OCaml array size");
    ++length;
    list = lean_ctor_get(list, 1);
  }
  return length;
}

static value copy_symbol(lean_object *id) {
  if (!lean_is_scalar(id) || lean_unbox(id) > (size_t)Max_long)
    caml_failwith("ACUIhE: returned symbol exceeds OCaml integer range");
  return Val_long(lean_unbox(id));
}

CAMLprim value caml_acuihe_graph_layer(value graph) {
  CAMLparam1(graph);
  CAMLlocal5(holder, result, word, atom, entry);
  CAMLlocal1(child);
  require_runtime();
  borrow_handle(graph, GRAPH);
  holder = allocate_handle(TEMPORARY);
  struct handle *output = Handle_val(holder);
  lean_object *input = borrow_handle(graph, GRAPH);
  caml_release_runtime_system();
  lean_inc(input);
  store_owned(output, acuihe_v1_graph_layer(input));
  caml_acquire_runtime_system();

  /* Finset's proof and quotient wrappers are erased, leaving a Lean List.
     Entries are Prod(word, Sum(Particle, child)); subtype proofs are erased.
     This is the only structural decoding contract beyond standard arrays. */
  lean_object *items = output->object;
  mlsize_t count = list_length(items);
  result = caml_alloc(count, 0);
  /* Later allocations can trigger GC before every entry has been copied. */
  for (mlsize_t i = 0; i < count; ++i) Store_field(result, i, Val_unit);
  for (mlsize_t i = 0; !lean_is_scalar(items); ++i) {
    lean_object *pair = lean_ctor_get(items, 0);
    lean_object *labels = lean_ctor_get(pair, 0);
    lean_object *sum = lean_ctor_get(pair, 1);
    mlsize_t word_length = list_length(labels);
    word = caml_alloc(word_length, 0);
    for (mlsize_t j = 0; j < word_length; ++j) Store_field(word, j, Val_unit);
    for (mlsize_t j = 0; !lean_is_scalar(labels); ++j) {
      Store_field(word, j, copy_symbol(lean_ctor_get(labels, 0)));
      labels = lean_ctor_get(labels, 1);
    }
    if (lean_obj_tag(sum) == 0) {
      lean_object *particle = lean_ctor_get(sum, 0);
      value id = copy_symbol(lean_ctor_get(particle, 0));
      atom = caml_alloc(1, lean_obj_tag(particle)); /* Constant = 0; Variable = 1 */
      Store_field(atom, 0, id);
    } else {
      child = allocate_handle(GRAPH);
      lean_object *native_child = lean_ctor_get(sum, 0);
      lean_inc(native_child);
      store_owned(Handle_val(child), native_child);
      atom = caml_alloc(1, 2); /* Free */
      Store_field(atom, 0, child);
    }
    entry = caml_alloc(2, 0);
    Store_field(entry, 0, word);
    Store_field(entry, 1, atom);
    Store_field(result, i, entry);
    items = lean_ctor_get(items, 1);
  }
  lean_dec(output->object);
  output->object = NULL;
  CAMLreturn(result);
}
