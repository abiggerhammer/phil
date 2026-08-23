#include "begin_policy_choice_v1.h"
#include "begin_policy_choice_v1_smoke_fixture.h"

#include <signal.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

static void reset_transport(struct phil_test_begin_policy_transport *transport) {
    memset(transport, 0, sizeof(*transport));
    transport->output_capacity = PHIL_TEST_BEGIN_POLICY_WIRE_CAPACITY;
}

static bool expect_abort(void (*action)(void)) {
    pid_t child = fork();
    int status = 0;
    if (child < 0) {
        return false;
    }
    if (child == 0) {
        action();
        _exit(0);
    }
    if (waitpid(child, &status, 0) != child) {
        return false;
    }
    return WIFSIGNALED(status) && WTERMSIG(status) == SIGABRT;
}

static void reserved_tag(void) {
    struct phil_test_begin_policy_transport transport;
    uint8_t reason = 0;
    reset_transport(&transport);
    transport.input[0] = 0x02u;
    transport.input_length = 1;
    (void) phil_runtime_receive_begin_policy_choice(&transport, &reason);
}

static void tag_eof(void) {
    struct phil_test_begin_policy_transport transport;
    uint8_t reason = 0;
    reset_transport(&transport);
    (void) phil_runtime_receive_begin_policy_choice(&transport, &reason);
}

static void truncated_reject(void) {
    struct phil_test_begin_policy_transport transport;
    uint8_t reason = 0;
    reset_transport(&transport);
    transport.input[0] = 0x00u;
    transport.input_length = 1;
    (void) phil_runtime_receive_begin_policy_choice(&transport, &reason);
}

static void reserved_reason(void) {
    struct phil_test_begin_policy_transport transport;
    uint8_t reason = 0;
    reset_transport(&transport);
    transport.input[0] = 0x00u;
    transport.input[1] = 0x02u;
    transport.input_length = 2;
    (void) phil_runtime_receive_begin_policy_choice(&transport, &reason);
}

static void proceed_write_failure(void) {
    struct phil_test_begin_policy_transport transport;
    reset_transport(&transport);
    transport.output_capacity = 0;
    phil_runtime_select_begin_policy_proceed(&transport);
}

static void reject_write_failure(void) {
    struct phil_test_begin_policy_transport transport;
    reset_transport(&transport);
    transport.output_capacity = 1;
    phil_runtime_select_begin_policy_reject(&transport, 0x01u);
}

static void reject_reserved_reason(void) {
    struct phil_test_begin_policy_transport transport;
    reset_transport(&transport);
    phil_runtime_select_begin_policy_reject(&transport, 0x02u);
}

int main(void) {
    struct phil_test_policy_context policy_context;
    struct phil_test_begin_record begin_record;
    struct phil_test_begin_policy_transport transport;
    uint8_t reason;

    policy_context.max_length = 4096u;
    begin_record.length = 1024u;
    reason = 0x55u;
    if (!phil_runtime_validate_begin_policy(&policy_context, &begin_record, &reason)
        || reason != 0x55u) {
        fputs("BeginPolicy accepted validation mismatch\n", stderr);
        return 1;
    }

    begin_record.length = 8192u;
    reason = 0;
    if (phil_runtime_validate_begin_policy(&policy_context, &begin_record, &reason)
        || reason != 0x01u) {
        fputs("BeginPolicy rejected validation mismatch\n", stderr);
        return 1;
    }

    reset_transport(&transport);
    phil_runtime_select_begin_policy_proceed(&transport);
    if (transport.output_length != 1 || transport.output[0] != 0x01u) {
        fputs("BeginPolicy proceed encoding mismatch\n", stderr);
        return 1;
    }

    reset_transport(&transport);
    phil_runtime_select_begin_policy_reject(&transport, 0x01u);
    if (transport.output_length != 2
        || transport.output[0] != 0x00u
        || transport.output[1] != 0x01u) {
        fputs("BeginPolicy reject encoding mismatch\n", stderr);
        return 1;
    }

    reset_transport(&transport);
    transport.input[0] = 0x01u;
    transport.input_length = 1;
    reason = 0x55u;
    if (!phil_runtime_receive_begin_policy_choice(&transport, &reason)
        || reason != 0x55u
        || transport.input_offset != 1) {
        fputs("BeginPolicy proceed decoding mismatch\n", stderr);
        return 1;
    }

    reset_transport(&transport);
    transport.input[0] = 0x00u;
    transport.input[1] = 0x01u;
    transport.input_length = 2;
    reason = 0;
    if (phil_runtime_receive_begin_policy_choice(&transport, &reason)
        || reason != 0x01u
        || transport.input_offset != 2) {
        fputs("BeginPolicy reject decoding mismatch\n", stderr);
        return 1;
    }

    if (!expect_abort(reserved_tag)
        || !expect_abort(tag_eof)
        || !expect_abort(truncated_reject)
        || !expect_abort(reserved_reason)
        || !expect_abort(proceed_write_failure)
        || !expect_abort(reject_write_failure)
        || !expect_abort(reject_reserved_reason)) {
        fputs("BeginPolicy fail-closed malformed/write behavior mismatch\n", stderr);
        return 1;
    }

    puts("PASS: begin-policy-choice-v1 native smoke");
    return 0;
}
