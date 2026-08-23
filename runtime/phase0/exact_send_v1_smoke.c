#include "exact_send_v1.h"

#include <stdbool.h>
#include <stddef.h>

static void *seen_transport;
static void *seen_payload;
static unsigned send_count;

void phil_runtime_send_exact(void *transport, void *payload) {
    seen_transport = transport;
    seen_payload = payload;
    send_count += 1U;
}

bool phil_exact_send_smoke(void) {
    int transport_token = 11;
    int payload_token = 29;

    seen_transport = NULL;
    seen_payload = NULL;
    send_count = 0U;

    phil_runtime_send_exact(&transport_token, &payload_token);

    return send_count == 1U
        && seen_transport == &transport_token
        && seen_payload == &payload_token;
}
