#include <stdbool.h>
#include <stdint.h>

void phil_runtime_select_payload_cancel(uint8_t choice) { (void) choice; }
bool phil_runtime_receive_payload_cancel(void) { return false; }
