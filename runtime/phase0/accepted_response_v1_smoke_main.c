#include "accepted_response_v1.h"

#include <stdio.h>

int UploadServer(void *server_transport);

static const uint8_t payload[] = { 'a', 'b', 'c' };
static const uint8_t sha256_abc[32] = {
  0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea,
  0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
  0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c,
  0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad,
};
static const uint8_t accepted_response[17] = {
  0x01,
  0xa0, 0xa1, 0xa2, 0xa3, 0xa4, 0xa5, 0xa6, 0xa7,
  0xa8, 0xa9, 0xaa, 0xab, 0xac, 0xad, 0xae, 0xaf,
};

int main(void) {
  void *transport;

  transport = phil_smoke_configure_accepted_response(
    payload, sizeof(payload), sizeof(payload), sha256_abc, 1);
  (void) UploadServer(transport);
  if (!phil_smoke_accepted_response_success_observed(
      payload,
      sizeof(payload),
      accepted_response,
      sizeof(accepted_response))) {
    fputs("accepted response success assertion failed\n", stderr);
    return 1;
  }
  puts("PASS: select accepted(id) encodes exactly 0x01 followed by the 16-octet UploadId token on the exact transport");

  transport = phil_smoke_configure_accepted_response(
    payload, sizeof(payload), sizeof(payload), sha256_abc, 0);
  (void) UploadServer(transport);
  if (!phil_smoke_accepted_response_failure_observed(sizeof(payload))) {
    fputs("storage failure accepted-response assertion failed\n", stderr);
    return 1;
  }
  puts("PASS: conforming storage failure returns null UploadId and emits no accepted response");

  transport = phil_smoke_configure_accepted_response(
    payload, sizeof(payload), sizeof(payload), sha256_abc, 2);
  (void) UploadServer(transport);
  if (!phil_smoke_accepted_response_reserved_status_observed(sizeof(payload))) {
    fputs("reserved storage status accepted-response assertion failed\n", stderr);
    return 1;
  }
  puts("PASS: reserved storage status with a non-null UploadId still emits no accepted response");

  return 0;
}
