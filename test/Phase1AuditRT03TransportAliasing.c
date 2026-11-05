#include "control_codec_v1.h"

#include <stdint.h>
#include <stdio.h>
#include <string.h>

static int check(int ok, const char *message) {
  if (!ok) {
    fprintf(stderr, "FAIL: RT-03 %s\n", message);
    return 0;
  }
  return 1;
}

int main(void) {
  uint8_t seed[60];
  uint8_t expected[170];
  void *transport = phil_codec_v1_transport_new();
  size_t i;

  for (i = 0u; i < sizeof(seed); ++i) {
    seed[i] = (uint8_t)(i + 1u);
  }
  if (!check(transport != NULL, "new transport")
      || !check(phil_codec_v1_transport_append(transport, seed, sizeof(seed)) == 0,
                "append independent initial bytes")) {
    return 1;
  }
  memcpy(expected, seed, 60u);
  if (!check(phil_codec_v1_transport_size(transport) == 60u,
             "initial logical length")) {
    return 1;
  }

  /* 60 -> 120 forces the first capacity growth from the 64-byte allocation. */
  {
    const uint8_t *self = phil_codec_v1_transport_bytes(transport);
    if (!check(phil_codec_v1_transport_append(transport, self, 60u) == 0,
               "whole-buffer self-append")) {
      return 1;
    }
  }
  memcpy(expected + 60u, expected, 60u);
  if (!check(phil_codec_v1_transport_size(transport) == 120u,
             "whole-buffer logical length")
      || !check(memcmp(phil_codec_v1_transport_bytes(transport), expected, 120u) == 0,
                "whole-buffer bytes preserved after realloc")) {
    return 1;
  }

  /* 120 -> 170 forces the next growth from 128 to 256; source is interior. */
  {
    const uint8_t *inside = phil_codec_v1_transport_bytes(transport) + 30u;
    if (!check(phil_codec_v1_transport_append(transport, inside, 50u) == 0,
               "interior self-append")) {
      return 1;
    }
  }
  memcpy(expected + 120u, expected + 30u, 50u);
  if (!check(phil_codec_v1_transport_size(transport) == 170u,
             "interior logical length")
      || !check(memcmp(phil_codec_v1_transport_bytes(transport), expected, 170u) == 0,
                "interior bytes preserved after realloc")
      || !check(phil_codec_v1_transport_read_offset(transport) == 0u,
                "append cannot advance receive offset")) {
    return 1;
  }

  /* Independent external input still retains ordinary append semantics. */
  if (!check(phil_codec_v1_transport_append(transport, seed, 1u) == 0,
             "independent append unchanged")
      || !check(phil_codec_v1_transport_size(transport) == 171u,
                "independent final size")
      || !check(phil_codec_v1_transport_bytes(transport)[170] == seed[0],
                "independent final byte")) {
    return 1;
  }
  phil_codec_v1_transport_free(transport);
  puts("PASS: RT-03 whole/interior self-append growth and independent controls");
  return 0;
}
