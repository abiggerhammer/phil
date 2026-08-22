#include "storage_v1.h"

#include <stdio.h>

int UploadServer(void *server_transport);

static const uint8_t payload[] = { 'a', 'b', 'c' };
static const uint8_t sha256_abc[32] = {
  0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea,
  0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
  0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c,
  0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad,
};

int main(void) {
  void *transport;

  transport = phil_smoke_configure_storage(
    payload, sizeof(payload), sizeof(payload), sha256_abc, 1);
  (void) UploadServer(transport);
  if (!phil_smoke_storage_success_observed(payload, sizeof(payload))) {
    fputs("storage success smoke assertion failed\n", stderr);
    return 1;
  }
  puts("PASS: storage persists the exact received payload, consumes its owner, and reaches accepted");

  transport = phil_smoke_configure_storage(
    payload, sizeof(payload), sizeof(payload), sha256_abc, 0);
  (void) UploadServer(transport);
  if (!phil_smoke_storage_failure_observed(sizeof(payload))) {
    fputs("storage failure ownership assertion failed\n", stderr);
    return 1;
  }
  puts("PASS: storage failure consumes the exact payload owner without a generated double release");

  transport = phil_smoke_configure_storage(
    payload, sizeof(payload), sizeof(payload), sha256_abc, 2);
  (void) UploadServer(transport);
  if (!phil_smoke_storage_reserved_status_observed(sizeof(payload))) {
    fputs("reserved storage status fail-closed assertion failed\n", stderr);
    return 1;
  }
  puts("PASS: reserved storage status fails closed even when fault injection supplies a non-null UploadId");

  return 0;
}
