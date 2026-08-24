#include "storage_failure_detail_v1.h"

#include <stddef.h>

static int payload_token;
static int upload_token;
static int error_token;
static int transport_token;

static int store_should_fail;
static int fail_calls;
static void *observed_fail_transport;
static void *observed_fail_error;

uint8_t phil_runtime_store_with_error(
    void *payload,
    void **upload_id_out,
    void **storage_error_out) {
  if (payload != &payload_token || upload_id_out == NULL || storage_error_out == NULL) {
    return 0;
  }

  if (store_should_fail) {
    *upload_id_out = NULL;
    *storage_error_out = &error_token;
    return 0;
  }

  *upload_id_out = &upload_token;
  *storage_error_out = NULL;
  return 1;
}

void phil_runtime_fail_storage(void *transport, void *storage_error) {
  fail_calls += 1;
  observed_fail_transport = transport;
  observed_fail_error = storage_error;
}

static int success_case(void) {
  void *upload_id = NULL;
  void *storage_error = NULL;
  store_should_fail = 0;
  uint8_t status = phil_runtime_store_with_error(
      &payload_token,
      &upload_id,
      &storage_error);

  return status == 1
      && upload_id == &upload_token
      && storage_error == NULL
      && fail_calls == 0;
}

static int failure_case(void) {
  void *upload_id = NULL;
  void *storage_error = NULL;
  store_should_fail = 1;
  uint8_t status = phil_runtime_store_with_error(
      &payload_token,
      &upload_id,
      &storage_error);

  if (status == 1 || upload_id != NULL || storage_error != &error_token) {
    return 0;
  }

  phil_runtime_fail_storage(&transport_token, storage_error);
  return fail_calls == 1
      && observed_fail_transport == &transport_token
      && observed_fail_error == &error_token;
}

int phil_storage_failure_detail_v1_smoke(void) {
  store_should_fail = 0;
  fail_calls = 0;
  observed_fail_transport = NULL;
  observed_fail_error = NULL;
  return success_case() && failure_case() ? 0 : 1;
}
