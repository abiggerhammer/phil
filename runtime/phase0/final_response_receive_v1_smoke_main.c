#include "final_response_receive_v1.h"

#include <signal.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

int UploadClient(void *transport);

static bool malformed_aborts(const uint8_t *bytes, size_t length) {
  pid_t child;
  int status = 0;
  void *transport = phil_smoke_configure_final_response(bytes, length);
  child = fork();
  if (child < 0) abort();
  if (child == 0) {
    (void) UploadClient(transport);
    _exit(0);
  }
  if (waitpid(child, &status, 0) != child) abort();
  return WIFSIGNALED(status) && WTERMSIG(status) == SIGABRT;
}

int main(void) {
  uint8_t accepted[17];
  uint8_t rejected[2] = {0x00u, 0x01u};
  uint8_t reserved_reason[2] = {0x00u, 0x02u};
  uint8_t truncated_accepted[1] = {0x01u};
  uint8_t token[16];
  size_t index;
  void *transport;

  accepted[0] = 0x01u;
  for (index = 0; index < 16u; ++index) {
    token[index] = (uint8_t) (0xb0u + index);
    accepted[index + 1u] = token[index];
  }

  transport = phil_smoke_configure_final_response(accepted, sizeof(accepted));
  (void) UploadClient(transport);
  if (!phil_smoke_accepted_observed(token)) return 1;

  transport = phil_smoke_configure_final_response(rejected, sizeof(rejected));
  (void) UploadClient(transport);
  if (!phil_smoke_rejected_observed()) return 2;

  if (!malformed_aborts(reserved_reason, sizeof(reserved_reason))) return 3;
  if (!malformed_aborts(truncated_accepted, sizeof(truncated_accepted))) return 4;
  return 0;
}
