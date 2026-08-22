#include <stdint.h>

/*
 * Deliberately ABI-incompatible fixture.  Phil declares this accessor as
 * ptr -> i64; this definition lowers to ptr -> i32 and must not link into the
 * recognized-record LLVM module.
 */
uint32_t phil_record_Begin_get_length(void *record) {
  (void) record;
  return 0;
}
