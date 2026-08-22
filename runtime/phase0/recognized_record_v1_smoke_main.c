#include "recognized_record_v1.h"

#include <inttypes.h>
#include <stdio.h>
#include <stdint.h>

extern int UploadServer(void);

void phil_smoke_configure(uint8_t begin_status, uint64_t begin_length);
bool phil_smoke_success_observed(uint64_t expected_length);
bool phil_smoke_fail_closed_observed(void);

static int run_success_case(void) {
  const uint64_t expected_length = UINT64_C(0x0102030405060708);
  phil_smoke_configure(1, expected_length);
  (void) UploadServer();
  if (!phil_smoke_success_observed(expected_length)) {
    fprintf(stderr,
      "recognized-record success path did not preserve Begin.length=%" PRIu64 "\n",
      expected_length);
    return 1;
  }
  puts("PASS: recognized Begin.length reaches receive_exact_u64 as the same i64 value");
  return 0;
}

static int run_fail_closed_case(void) {
  phil_smoke_configure(2, UINT64_C(0x8877665544332211));
  (void) UploadServer();
  if (!phil_smoke_fail_closed_observed()) {
    fputs("malformed Begin recognition status did not fail closed before field access\n", stderr);
    return 1;
  }
  puts("PASS: malformed Begin recognition status fails closed before projection/receive");
  return 0;
}

int main(void) {
  if (run_success_case() != 0) {
    return 1;
  }
  if (run_fail_closed_case() != 0) {
    return 1;
  }
  return 0;
}
