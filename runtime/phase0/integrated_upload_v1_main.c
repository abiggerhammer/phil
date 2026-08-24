#include "integrated_upload_v1.h"

#include <pthread.h>
#include <stdint.h>
#include <stdio.h>

extern int32_t UploadClient(void *client_transport, void *client_payload_owner);
extern int32_t UploadServer(
    void *server_policy_context,
    void *server_supported_versions,
    void *server_transport);

struct thread_result {
  int32_t result;
};

static void *run_client(void *argument) {
  struct thread_result *result = argument;
  phil_integrated_v1_enter_client();
  result->result = UploadClient(
      phil_integrated_v1_transport(),
      phil_integrated_v1_client_payload());
  return NULL;
}

static void *run_server(void *argument) {
  struct thread_result *result = argument;
  phil_integrated_v1_enter_server();
  result->result = UploadServer(
      phil_integrated_v1_policy_context(),
      phil_integrated_v1_server_supported_versions(),
      phil_integrated_v1_transport());
  return NULL;
}

static const char *scenario_name(enum phil_integrated_v1_scenario scenario) {
  switch (scenario) {
    case PHIL_INTEGRATED_V1_ACCEPT:
      return "accepted upload";
    case PHIL_INTEGRATED_V1_DIGEST_REJECT:
      return "digest rejection";
    case PHIL_INTEGRATED_V1_CANCEL:
      return "client cancellation";
  }
  return "unknown";
}

static int run_scenario(enum phil_integrated_v1_scenario scenario) {
  static const uint8_t payload[] = {
    0x70u, 0x68u, 0x69u, 0x6cu, 0x2du, 0x70u, 0x68u, 0x61u,
    0x73u, 0x65u, 0x30u, 0x2du, 0x6eu, 0x61u, 0x74u, 0x69u,
    0x76u, 0x65u, 0x2du, 0x75u, 0x70u, 0x6cu, 0x6fu, 0x61u, 0x64u
  };
  pthread_t client_thread;
  pthread_t server_thread;
  struct thread_result client_result = { .result = -1 };
  struct thread_result server_result = { .result = -1 };
  int client_started = 0;
  int server_started = 0;
  int ok = 0;

  if (phil_integrated_v1_prepare(scenario, payload, sizeof(payload)) != 0) {
    fprintf(stderr, "FAIL: %s fixture setup\n", scenario_name(scenario));
    return 0;
  }

  if (pthread_create(&client_thread, NULL, run_client, &client_result) != 0) {
    fprintf(stderr, "FAIL: %s client thread creation\n", scenario_name(scenario));
    goto cleanup;
  }
  client_started = 1;

  phil_integrated_v1_wait_client_version_receive();

  if (pthread_create(&server_thread, NULL, run_server, &server_result) != 0) {
    fprintf(stderr, "FAIL: %s server thread creation\n", scenario_name(scenario));
    goto cleanup;
  }
  server_started = 1;

  if (pthread_join(server_thread, NULL) != 0) {
    fprintf(stderr, "FAIL: %s server thread join\n", scenario_name(scenario));
    goto cleanup;
  }
  server_started = 0;
  if (pthread_join(client_thread, NULL) != 0) {
    fprintf(stderr, "FAIL: %s client thread join\n", scenario_name(scenario));
    goto cleanup;
  }
  client_started = 0;

  ok = client_result.result == 0
      && server_result.result == 0
      && phil_integrated_v1_observed(scenario);
  if (ok) {
    printf("PASS: %s\n", scenario_name(scenario));
  } else {
    fprintf(
        stderr,
        "FAIL: %s (client=%d server=%d observed=%d)\n",
        scenario_name(scenario),
        (int)client_result.result,
        (int)server_result.result,
        phil_integrated_v1_observed(scenario) ? 1 : 0);
  }

cleanup:
  if (server_started) {
    (void)pthread_cancel(server_thread);
    (void)pthread_join(server_thread, NULL);
  }
  if (client_started) {
    (void)pthread_cancel(client_thread);
    (void)pthread_join(client_thread, NULL);
  }
  phil_integrated_v1_destroy();
  return ok;
}

int main(void) {
  return run_scenario(PHIL_INTEGRATED_V1_ACCEPT)
      && run_scenario(PHIL_INTEGRATED_V1_DIGEST_REJECT)
      && run_scenario(PHIL_INTEGRATED_V1_CANCEL)
    ? 0
    : 1;
}
