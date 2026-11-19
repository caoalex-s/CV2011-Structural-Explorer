/* Bound the caller's packet before handing it to the source-derived Lean checker. */
#include <stdint.h>
#include <string.h>
#include <lean/lean.h>

extern void lean_initialize_runtime_module(void);
extern lean_object *initialize_InclinedReleaseWire(uint8_t, lean_object *);
extern lean_obj_res inclined_release_report(lean_obj_arg);

static unsigned char input[1048577];
static unsigned char output[262145];
static uint32_t output_length = 0;
uint32_t output_ptr(void) { return (uint32_t)(uintptr_t)output; }
uint32_t output_capacity(void) { return sizeof(output) - 1; }
uint32_t output_size(void) { return output_length; }
static int initialized = 0;
uint32_t input_ptr(void) { return (uint32_t)(uintptr_t)input; }
uint32_t input_capacity(void) { return sizeof(input) - 1; }

uint32_t checker_init(void) {
    if (initialized) return 1;
    lean_initialize_runtime_module();
    lean_object *result = initialize_InclinedReleaseWire(1, lean_io_mk_world());
    if (lean_io_result_is_error(result)) { lean_dec(result); return 0; }
    lean_dec(result);
    lean_io_mark_end_initialization();
    initialized = 1;
    return 1;
}

static uint32_t inclined_packet(void) {
    lean_object *result = inclined_release_report(lean_mk_string((char *)input));
    if (lean_is_scalar(result)) { lean_dec(result); return 0; }
    lean_object *report = lean_ctor_get(result, 0);
    size_t stored_size = lean_string_size(report);
    if (stored_size == 0 || stored_size - 1 > output_capacity()) {
        lean_dec(result);
        return 3;
    }
    memcpy(output, lean_string_cstr(report), stored_size);
    output_length = (uint32_t)(stored_size - 1);
    lean_dec(result);
    return 1;
}

uint32_t checker_check(uint32_t pointer, uint32_t length) {
    output_length = 0;
    output[0] = 0;
    if (!initialized) return 4;
    if (length > input_capacity()) return 3;
    if (pointer != input_ptr() || length == 0) return 2;

    /* Bound line count and individual token size before Lean string/array
     * allocation. IDs are at most 256 UTF-16 code units encoded as hex (1024
     * ASCII bytes). Lean separately bounds numeric tokens before conversion.
     */
    size_t fields = 1;
    size_t token_length = 0;
    for (size_t i = 0; i < length; ++i) {
        unsigned char character = input[i];
        if (character == '\n') {
            if (token_length == 0) return 2;
            if (++fields > 6000) return 3;
            token_length = 0;
        } else {
            if (character < 32 || character > 126) return 2;
            if (++token_length > 1024) return 3;
        }
    }
    if (token_length == 0) return 2;
    input[length] = '\0';
    return inclined_packet();
}
