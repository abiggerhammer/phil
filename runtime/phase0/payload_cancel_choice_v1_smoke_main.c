#include "payload_cancel_choice_v1.h"

#include <signal.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

int UploadClient(void *transport);
int UploadServer(void *transport);

static bool malformed_server_aborts(bool empty, uint8_t choice) {
  pid_t child;
  int status = 0;
  void *transport = empty
      ? phil_smoke_configure_server_empty()
      : phil_smoke_configure_server(choice);
  child = fork();
  if (child < 0) abort();
  if (child == 0) {
    (void) UploadServer(transport);
    _exit(0);
  }
  if (waitpid(child, &status, 0) != child) abort();
  return WIFSIGNALED(status) && WTERMSIG(status) == SIGABRT;
}

int main(void) {
  uint8_t accepted[17];
  size_t index;
  void *transport;

  accepted[0] = 0x01u;
  for (index = 0; index < 16u; ++index) {
    accepted[index + 1u] = (uint8_t) (0x80u + index);
  }

  transport = phil_smoke_configure_client(false, accepted, sizeof(accepted));
  (void) UploadClient(transport);
  if (!phil_smoke_client_choice_observed(0x01u)) return 1;

  transport = phil_smoke_configure_client(true, NULL, 0u);
  (void) UploadClient(transport);
  if (!phil_smoke_client_choice_observed(0x00u)) return 2;

  transport = phil_smoke_configure_server(0x01u);
  (void) UploadServer(transport);
  if (!phil_smoke_server_choice_observed(0x01u)) return 3;

  transport = phil_smoke_configure_server(0x00u);
  (void) UploadServer(transport);
  if (!phil_smoke_server_choice_observed(0x00u)) return 4;

  if (!malformed_server_aborts(false, 0x02u)) return 5;
  if (!malformed_server_aborts(true, 0x00u)) return 6;

  return 0;
}
