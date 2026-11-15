/* Draft byte boundary for fixed, exact-cardinal and inclined-frame checks.
 * This layer checks resources and ASCII only. Structural acceptance is always
 * returned by the compiled Lean source-level entries, never by this decoder.
 */
#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include <lean/lean.h>

extern void lean_initialize_runtime_module(void);
extern lean_object *initialize_PortalChecker(uint8_t, lean_object *);
extern lean_object *initialize_RationalFrameWire(uint8_t, lean_object *);
extern lean_object *initialize_InclinedFrameIntervalReport(uint8_t, lean_object *);
extern uint32_t portal_check(lean_object *);
extern uint32_t frame_check(lean_object *);
extern lean_obj_res inclined_report(lean_obj_arg);

static unsigned char input[1048577];
static unsigned char output[262145];
static uint32_t output_length = 0;
static int initialized = 0;

uint32_t input_ptr(void) { return (uint32_t)(uintptr_t)input; }
uint32_t input_capacity(void) { return sizeof(input) - 1; }
uint32_t output_ptr(void) { return (uint32_t)(uintptr_t)output; }
uint32_t output_capacity(void) { return sizeof(output) - 1; }
uint32_t output_size(void) { return output_length; }

uint32_t checker_init(void) {
    if (initialized) return 1;
    lean_initialize_runtime_module();
    lean_object *portal = initialize_PortalChecker(1, lean_io_mk_world());
    if (lean_io_result_is_error(portal)) { lean_dec(portal); return 0; }
    lean_dec(portal);
    lean_object *frame = initialize_RationalFrameWire(1, lean_io_mk_world());
    if (lean_io_result_is_error(frame)) { lean_dec(frame); return 0; }
    lean_dec(frame);
    lean_object *inclined = initialize_InclinedFrameIntervalReport(1, lean_io_mk_world());
    if (lean_io_result_is_error(inclined)) { lean_dec(inclined); return 0; }
    lean_dec(inclined);
    lean_io_mark_end_initialization();
    initialized = 1;
    return 1;
}

/* Preserve the accepted fixed portal's 21-rational canonical wire contract. */
static uint32_t portal_packet(uint32_t length) {
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
        for (size_t i = sign; i < count; ++i)
            if (input[start + i] < '0' || input[start + i] > '9') return 2;
        start = end + 1;
    }
    return portal_check(lean_mk_string((char *)input));
}

/* Option String uses an immediate none or a some constructor owning the string.
 * lean_ctor_get borrows it; copy before releasing the owning Option. The pinned
 * Lean 4.19 header defines string_size to include the terminal NUL:
 * https://github.com/leanprover/lean4/blob/v4.19.0/src/include/lean/lean.h
 */
static uint32_t inclined_packet(void) {
    lean_object *result = inclined_report(lean_mk_string((char *)input));
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
    /* A failed/new call cannot expose the preceding successful report. */
    output_length = 0;
    output[0] = '\0';
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
    const char inclined_prefix[] = "CV2011_INCLINED_1\n";
    if (length >= sizeof(inclined_prefix) - 1 &&
        memcmp(input, inclined_prefix, sizeof(inclined_prefix) - 1) == 0)
        return inclined_packet();
    const char prefix[] = "CV2011_FRAME_1\n";
    if (length >= sizeof(prefix) - 1 && memcmp(input, prefix, sizeof(prefix) - 1) == 0)
        return frame_check(lean_mk_string((char *)input));
    return portal_packet(length);
}
