#include "rejected_response_v1.h"

#include <openssl/sha.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern int UploadServer(void *transport);

int main(void) {
  static const uint8_t payload[] = { 'a', 'b', 'c' };
  uint8_t digest[SHA256_DIGEST_LENGTH];
  const uint8_t expected_response[] = { 0x00u, 0x01u };
  void *transport;
  int result;

  if (SHA256(payload, sizeof(payload), digest) == NULL) {
    fputs("FAIL: SHA256 fixture setup failed\n", stderr);
    return 1;
  }
  digest[0] ^= 0x80u;

  transport = phil_smoke_configure_rejected_response(
    payload,
    sizeof(payload),
    sizeof(payload),
    digest);
  result = UploadServer(transport);
  if (result != 0) {
    fprintf(stderr, "FAIL: UploadServer returned %d\n", result);
    return 1;
  }
  if (!phil_smoke_rejected_response_observed(
        sizeof(payload),
        expected_response,
        sizeof(expected_response))) {
    fputs("FAIL: rejected-response runtime observation mismatch\n", stderr);
    return 1;
  }

  puts("PASS: digest mismatch releases the exact payload owner then emits 00 01 on the exact transport");
  return 0;
}
