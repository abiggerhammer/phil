#include <stdint.h>

struct phil_exact_receive_result {
  uint8_t status;
  void *payload;
};

/* Deliberately omits the explicit transport operand. */
struct phil_exact_receive_result phil_runtime_receive_exact_u64(uint64_t length) {
  struct phil_exact_receive_result result = { 0, 0 };
  (void) length;
  return result;
}
