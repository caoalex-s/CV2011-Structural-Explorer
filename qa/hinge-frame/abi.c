/* Bound the caller's packet before handing it to the source-derived Lean checker. */
#include <stdint.h>
#include <lean/lean.h>

extern void lean_initialize_runtime_module(void);
extern lean_object *initialize_HingeFrameWire(uint8_t, lean_object *);
extern uint32_t hinge_frame_check(lean_object *);

static unsigned char input[1048577];
static int initialized = 0;
uint32_t input_ptr(void) { return (uint32_t)(uintptr_t)input; }
uint32_t input_capacity(void) { return sizeof(input) - 1; }

uint32_t checker_init(void) {
    if (initialized) return 1;
    lean_initialize_runtime_module();
    lean_object *result = initialize_HingeFrameWire(1, lean_io_mk_world());
    if (lean_io_result_is_error(result)) { lean_dec(result); return 0; }
    lean_dec(result);
    lean_io_mark_end_initialization();
    initialized = 1;
    return 1;
}

uint32_t checker_check(uint32_t pointer, uint32_t length) {
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
    return hinge_frame_check(lean_mk_string((char *)input));
}
