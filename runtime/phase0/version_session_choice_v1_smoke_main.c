#include "version_session_choice_v1.h"
#include "version_session_choice_v1_smoke_fixture.h"

#include <signal.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

static bool contains(const struct phil_test_version_set *set, uint16_t value) {
    size_t i;
    for (i = 0; i < set->length; ++i) {
        if (set->values[i] == value) {
            return true;
        }
    }
    return false;
}

static void reset_transport(struct phil_test_choice_transport *transport) {
    memset(transport, 0, sizeof(*transport));
    transport->output_capacity = PHIL_TEST_WIRE_CAPACITY;
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
    struct phil_test_choice_transport transport;
    uint16_t selected = 0;
    reset_transport(&transport);
    transport.input[0] = 0x02u;
    transport.input_length = 1;
    (void) phil_runtime_receive_version_choice(&transport, &selected);
}

static void tag_eof(void) {
    struct phil_test_choice_transport transport;
    uint16_t selected = 0;
    reset_transport(&transport);
    (void) phil_runtime_receive_version_choice(&transport, &selected);
}

static void truncated_version(void) {
    struct phil_test_choice_transport transport;
    uint16_t selected = 0;
    reset_transport(&transport);
    transport.input[0] = 0x01u;
    transport.input[1] = 0x12u;
    transport.input_length = 2;
    (void) phil_runtime_receive_version_choice(&transport, &selected);
}

static void unsupported_write_failure(void) {
    struct phil_test_choice_transport transport;
    reset_transport(&transport);
    transport.output_capacity = 0;
    phil_runtime_select_unsupported(&transport);
}

static void version_write_failure(void) {
    struct phil_test_choice_transport transport;
    reset_transport(&transport);
    transport.output_capacity = 2;
    phil_runtime_select_version(&transport, 0x1234u);
}

int main(void) {
    struct phil_test_hello_record hello;
    struct phil_test_version_set supported;
    struct phil_test_version_set disjoint;
    struct phil_test_choice_transport transport;
    uint16_t selected;
    void *projected;

    memset(&hello, 0, sizeof(hello));
    memset(&supported, 0, sizeof(supported));
    memset(&disjoint, 0, sizeof(disjoint));

    hello.versions.values[0] = 1;
    hello.versions.values[1] = 2;
    hello.versions.length = 2;
    supported.values[0] = 3;
    supported.values[1] = 2;
    supported.length = 2;
    disjoint.values[0] = 9;
    disjoint.length = 1;

    projected = phil_record_Hello_get_versions(&hello);
    if (projected != &hello.versions) {
        fputs("Hello.versions projection mismatch\n", stderr);
        return 1;
    }

    selected = 0xffffu;
    if (!phil_runtime_choose_supported(&supported, projected, &selected)
        || !contains(&supported, selected)
        || !contains(&hello.versions, selected)) {
        fputs("choose_supported some-case mismatch\n", stderr);
        return 1;
    }

    selected = 0x55aau;
    if (phil_runtime_choose_supported(&disjoint, projected, &selected)
        || selected != 0x55aau) {
        fputs("choose_supported none-case mismatch\n", stderr);
        return 1;
    }

    reset_transport(&transport);
    phil_runtime_select_unsupported(&transport);
    if (transport.output_length != 1 || transport.output[0] != 0x00u) {
        fputs("unsupported encoding mismatch\n", stderr);
        return 1;
    }

    reset_transport(&transport);
    phil_runtime_select_version(&transport, 0x1234u);
    if (transport.output_length != 3
        || transport.output[0] != 0x01u
        || transport.output[1] != 0x12u
        || transport.output[2] != 0x34u) {
        fputs("version encoding mismatch\n", stderr);
        return 1;
    }

    reset_transport(&transport);
    transport.input[0] = 0x00u;
    transport.input_length = 1;
    selected = 0x55aau;
    if (phil_runtime_receive_version_choice(&transport, &selected)
        || selected != 0x55aau
        || transport.input_offset != 1) {
        fputs("unsupported decoding mismatch\n", stderr);
        return 1;
    }

    reset_transport(&transport);
    transport.input[0] = 0x01u;
    transport.input[1] = 0xabu;
    transport.input[2] = 0xcdu;
    transport.input_length = 3;
    selected = 0;
    if (!phil_runtime_receive_version_choice(&transport, &selected)
        || selected != 0xabcdu
        || transport.input_offset != 3) {
        fputs("version decoding mismatch\n", stderr);
        return 1;
    }

    if (!expect_abort(reserved_tag)
        || !expect_abort(tag_eof)
        || !expect_abort(truncated_version)
        || !expect_abort(unsupported_write_failure)
        || !expect_abort(version_write_failure)) {
        fputs("fail-closed malformed/write-failure behavior mismatch\n", stderr);
        return 1;
    }

    puts("PASS: version-session-choice-v1 native smoke");
    return 0;
}
