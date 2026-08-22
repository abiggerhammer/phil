#include "digest_validation_v1.h"

#include <stdio.h>
#include <string.h>

extern int UploadServer(void *transport);

static const uint8_t SHA256_ABC[32] = {
  0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea,
  0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
  0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c,
  0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad,
};

int main(void) {
  const uint8_t payload[] = { 'a', 'b', 'c' };
  uint8_t wrong_digest[32];
  void *transport;

  transport = phil_smoke_configure_digest_transport(
    payload, sizeof(payload), sizeof(payload), SHA256_ABC);
  (void) UploadServer(transport);
  if (!phil_smoke_digest_match_observed(sizeof(payload))) {
    fputs("FAIL: SHA-256 match did not use the exact Begin and payload subjects\n", stderr);
    return 1;
  }
  puts("PASS: SHA-256 DigestMatches accepts the exact recognized Begin and received payload");

  memcpy(wrong_digest, SHA256_ABC, sizeof(wrong_digest));
  wrong_digest[0] ^= 1u;
  transport = phil_smoke_configure_digest_transport(
    payload, sizeof(payload), sizeof(payload), wrong_digest);
  (void) UploadServer(transport);
  if (!phil_smoke_digest_mismatch_observed(sizeof(payload))) {
    fputs("FAIL: SHA-256 mismatch did not preserve the payload for generated rejection cleanup\n", stderr);
    return 1;
  }
  puts("PASS: SHA-256 mismatch leaves the exact payload owner for generated rejection cleanup");

  return 0;
}
