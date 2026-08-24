#include <stdint.h>

static void *current_payload;
static void *current_upload_id;
static void *current_storage_error;
static void *current_transport;

uint8_t phil_runtime_store_with_error(void) {
  current_upload_id = current_payload;
  return current_storage_error == 0 ? 1 : 0;
}

void phil_runtime_fail_storage(void) {
  (void)current_transport;
  (void)current_storage_error;
}
