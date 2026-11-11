/* Trusted byte boundary for the combined fixed-portal/generic-frame artifact.
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
extern uint32_t portal_check(lean_object *);
extern uint32_t frame_check(lean_object *);

static unsigned char input[1048577];
static int initialized = 0;

uint32_t input_ptr(void) { return (uint32_t)(uintptr_t)input; }
uint32_t input_capacity(void) { return sizeof(input) - 1; }

uint32_t checker_init(void) {
    if (initialized) return 1;
    lean_initialize_runtime_module();
    lean_object *portal = initialize_PortalChecker(1, lean_io_mk_world());
    if (lean_io_result_is_error(portal)) { lean_dec(portal); return 0; }
    lean_dec(portal);
    lean_object *frame = initialize_RationalFrameWire(1, lean_io_mk_world());
    if (lean_io_result_is_error(frame)) { lean_dec(frame); return 0; }
    lean_dec(frame);
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
    const char prefix[] = "CV2011_FRAME_1\n";
    if (length >= sizeof(prefix) - 1 && memcmp(input, prefix, sizeof(prefix) - 1) == 0)
        return frame_check(lean_mk_string((char *)input));
    return portal_packet(length);
}
