/* Bounded trusted ASCII decoder. PortalChecker.checkString performs every
 * exact equation/reaction/recovery check. No C or JavaScript matrix checker. */
#include <stdint.h>
#include <stddef.h>
#include <lean/lean.h>

extern void lean_initialize_runtime_module(void);
extern lean_object *initialize_PortalChecker(uint8_t, lean_object *);
extern uint32_t portal_check(lean_object *);
static unsigned char input[8192];
static int initialized = 0;
uint32_t input_ptr(void) { return (uint32_t)(uintptr_t)input; }
uint32_t input_capacity(void) { return sizeof(input) - 1; }

uint32_t checker_init(void) {
    if (initialized) return 1;
    lean_initialize_runtime_module();
    lean_object *result = initialize_PortalChecker(1, lean_io_mk_world());
    if (lean_io_result_is_error(result)) { lean_dec(result); return 0; }
    lean_dec(result);
    lean_io_mark_end_initialization();
    initialized = 1;
    return 1;
}

/* 21 rationals: alpha, 12 ordered displacements, six A/D reactions, M, uy.
 * Each rational has canonical signed numerator and positive denominator.
 * Final terminator is written only after validated capacity and byte bounds. */
uint32_t checker_check(uint32_t pointer, uint32_t length) {
    if (!initialized) return 4;
    if (length > input_capacity()) return 3;
    if (pointer != input_ptr() || length == 0) return 2;
    size_t start = 0;
    for (unsigned int field = 0; field < 42; ++field) {
        size_t end = start;
        while (end < length && input[end] != '\n') ++end;
        if ((field < 41 && end == length) || (field == 41 && end != length)) return 2;
        size_t count = end - start;
        if (count == 0) return 2;
        size_t sign = input[start] == '-' ? 1 : 0;
        if ((field % 2 == 1 && sign) || count <= sign) return 2;
        if (count - sign > 128) return 3;
        if (input[start + sign] == '0' && (count != 1 || field % 2 == 1)) return 2;
        for (size_t i = sign; i < count; ++i) {
            if (input[start + i] < '0' || input[start + i] > '9') return 2;
        }
        start = end + 1;
    }
    input[length] = '\0';
    return portal_check(lean_mk_string((char *)input));
}
