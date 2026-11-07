/* Bounded ASCII ABI. Arithmetic and acceptance stay in generated Lean code.
 * This decoder is trusted C, not covered by the Rat acceptance theorem. */
#include <stdint.h>
#include <stddef.h>
#include <lean/lean.h>

extern void lean_initialize_runtime_module(void);
extern lean_object *initialize_SmokeChecker(uint8_t, lean_object *);
extern uint32_t smoke_check(lean_object *, lean_object *, lean_object *, lean_object *);

static unsigned char input[4096];
static int initialized = 0;

uint32_t input_ptr(void) { return (uint32_t)(uintptr_t)input; }
uint32_t input_capacity(void) { return sizeof(input); }

uint32_t checker_init(void) {
    if (initialized) return 1;
    lean_initialize_runtime_module();
    lean_object *result = initialize_SmokeChecker(1, lean_io_mk_world());
    if (lean_io_result_is_error(result)) {
        lean_dec(result);
        return 0;
    }
    lean_dec(result);
    lean_io_mark_end_initialization();
    initialized = 1;
    return 1;
}

/* Four fields: a numerator, a denominator, x numerator, x denominator.
 * No trailing newline. Numerators: 0 or -?[1-9][0-9]*; denominators: [1-9][0-9]*.
 * At most 128 digits per field. No NUL, non-ASCII, whitespace or extra fields.
 * Only the module-owned input buffer is accepted; arbitrary pointers cannot
 * cause a read. Length is checked before touching that buffer. */
uint32_t checker_check(uint32_t pointer, uint32_t length) {
    if (!initialized) return 4;
    if (length > sizeof(input)) return 3;
    if (pointer != input_ptr() || length == 0) return 2;
    char fields[4][130];
    size_t start = 0;
    for (unsigned int field = 0; field < 4; ++field) {
        size_t end = start;
        while (end < length && input[end] != '\n') ++end;
        if ((field < 3 && end == length) || (field == 3 && end != length)) return 2;
        size_t count = end - start;
        if (count == 0) return 2;
        size_t sign = input[start] == '-' ? 1 : 0;
        if ((field % 2 == 1 && sign) || count <= sign) return 2;
        if (count - sign > 128) return 3;
        if (input[start + sign] == '0' && (count != 1 || field % 2 == 1)) return 2;
        for (size_t i = sign; i < count; ++i) {
            if (input[start + i] < '0' || input[start + i] > '9') return 2;
        }
        for (size_t i = 0; i < count; ++i) fields[field][i] = input[start + i];
        fields[field][count] = '\0';
        start = end + 1;
    }
    return smoke_check(lean_mk_string(fields[0]), lean_mk_string(fields[1]),
                       lean_mk_string(fields[2]), lean_mk_string(fields[3]));
}
