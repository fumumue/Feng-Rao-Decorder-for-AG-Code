#ifndef AG_FRVOTE_H
#define AG_FRVOTE_H
#include <stddef.h>
#include <stdint.h>
#ifdef __cplusplus
extern "C" {
#endif

/* Run the legacy command-line experiment as an embedded function. */
int ag_frvote_run(int argc, char **argv);

/*
 * Decode a caller-supplied received word with the existing Newton/FR-VOTE
 * decoder. `received_len` must equal the number of evaluation positions after
 * --len/curve selection. `--errors T` specifies the designed correction
 * radius parameter (not the actual number of errors), and `-frvote` must be
 * selected without -fr/-bms/-vote.
 *
 * On success, returns 0 and writes the recovered error positions and error
 * values. `output_capacity` bounds both output arrays; `error_count` receives
 * the actual number found. Field elements are uint16_t encodings used by the
 * implementation (polynomial-basis bit representation).
 *
 * Return codes: -1 invalid arguments; -10 no API decode completed; 1 setup or
 * option error; 2 decoder failure/unresolved values; 3 output buffer too small.
 * The current engine uses global working arrays: one call per process only;
 * not reentrant and not thread-safe. Only the one-point Newton FR-VOTE path is
 * exposed by this first API version.
 */
int ag_frvote_decode(int argc, char **argv, const uint16_t *received,
                     size_t received_len, size_t *error_positions,
                     uint16_t *error_values, size_t output_capacity,
                     size_t *error_count);

#ifdef __cplusplus
}
#endif
#endif
