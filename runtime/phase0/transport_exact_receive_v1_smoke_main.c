#include "transport_exact_receive_v1.h"

#include <stdio.h>

extern int UploadServer(void *transport);

static int run_exact_success(void) {
  static const uint8_t bytes[] = {
    0x10, 0x21, 0x32, 0x43, 0x54, 0x65, 0x76, 0x87,
  };
  void *transport = phil_smoke_configure_transport(bytes, sizeof(bytes), sizeof(bytes));
  (void) UploadServer(transport);
  if (!phil_smoke_exact_success_observed(sizeof(bytes))) {
    fputs("transport exact-receive success path did not preserve owner/dataflow\n", stderr);
    return 1;
  }
  puts("PASS: explicit transport exact receive copies the requested payload and releases its owner by identity");
  return 0;
}

static int run_early_eof(void) {
  static const uint8_t bytes[] = { 0xaa, 0xbb, 0xcc };
  void *transport = phil_smoke_configure_transport(bytes, sizeof(bytes), 8);
  (void) UploadServer(transport);
  if (!phil_smoke_early_eof_observed(sizeof(bytes))) {
    fputs("transport early-EOF path did not release the returned partial owner\n", stderr);
    return 1;
  }
  puts("PASS: early EOF returns a partial payload owner and the generated failure path releases that exact handle");
  return 0;
}

int main(void) {
  if (run_exact_success() != 0) {
    return 1;
  }
  if (run_early_eof() != 0) {
    return 1;
  }
  return 0;
}
