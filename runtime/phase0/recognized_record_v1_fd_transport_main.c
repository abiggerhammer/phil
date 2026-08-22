#include "recognized_record_v1.h"

#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

extern int UploadServer(void);

void phil_transport_configure(int input_fd, uint8_t begin_status, uint64_t begin_length);
bool phil_transport_success_observed(uint64_t expected_length);
bool phil_transport_short_read_observed(uint64_t expected_length, uint64_t expected_bytes_read);

static int write_all(int fd, const unsigned char *bytes, size_t length) {
  size_t written = 0;

  while (written < length) {
    ssize_t result;
    do {
      result = write(fd, bytes + written, length - written);
    } while (result < 0 && errno == EINTR);

    if (result <= 0) {
      return -1;
    }
    written += (size_t) result;
  }

  return 0;
}

static int run_exact_success_case(void) {
  static const unsigned char payload[] = {
    0x50, 0x68, 0x69, 0x6c, 0x20, 0x70, 0x61, 0x79,
    0x6c, 0x6f, 0x61, 0x64, 0x21
  };
  static const unsigned char tail[] = {0xa5, 0x5a, 0xc3, 0x3c};
  unsigned char input[sizeof(payload) + sizeof(tail)];
  unsigned char leftover[sizeof(tail)];
  int descriptors[2];
  ssize_t leftover_count;

  memcpy(input, payload, sizeof(payload));
  memcpy(input + sizeof(payload), tail, sizeof(tail));

  if (pipe(descriptors) != 0) {
    perror("pipe");
    return 1;
  }
  if (write_all(descriptors[1], input, sizeof(input)) != 0) {
    perror("write");
    close(descriptors[0]);
    close(descriptors[1]);
    return 1;
  }
  if (close(descriptors[1]) != 0) {
    perror("close");
    close(descriptors[0]);
    return 1;
  }

  phil_transport_configure(descriptors[0], 1, (uint64_t) sizeof(payload));
  (void) UploadServer();

  if (!phil_transport_success_observed((uint64_t) sizeof(payload))) {
    fputs("exact payload transport did not consume the declared byte count\n", stderr);
    close(descriptors[0]);
    return 1;
  }

  do {
    leftover_count = read(descriptors[0], leftover, sizeof(leftover));
  } while (leftover_count < 0 && errno == EINTR);

  if (leftover_count != (ssize_t) sizeof(tail)
      || memcmp(leftover, tail, sizeof(tail)) != 0) {
    fputs("exact payload transport over-read or corrupted trailing bytes\n", stderr);
    close(descriptors[0]);
    return 1;
  }

  if (close(descriptors[0]) != 0) {
    perror("close");
    return 1;
  }

  puts("PASS: receive_exact_u64 reads exactly Begin.length bytes and leaves trailing bytes untouched");
  return 0;
}

static int run_short_read_case(void) {
  static const unsigned char short_payload[] = {0xde, 0xad, 0xbe, 0xef, 0x01};
  const uint64_t declared_length = UINT64_C(11);
  int descriptors[2];

  if (pipe(descriptors) != 0) {
    perror("pipe");
    return 1;
  }
  if (write_all(descriptors[1], short_payload, sizeof(short_payload)) != 0) {
    perror("write");
    close(descriptors[0]);
    close(descriptors[1]);
    return 1;
  }
  if (close(descriptors[1]) != 0) {
    perror("close");
    close(descriptors[0]);
    return 1;
  }

  phil_transport_configure(descriptors[0], 1, declared_length);
  (void) UploadServer();

  if (!phil_transport_short_read_observed(
        declared_length,
        (uint64_t) sizeof(short_payload))) {
    fputs("short payload input did not fail closed after EOF\n", stderr);
    close(descriptors[0]);
    return 1;
  }

  if (close(descriptors[0]) != 0) {
    perror("close");
    return 1;
  }

  puts("PASS: receive_exact_u64 fails closed when EOF arrives before Begin.length bytes");
  return 0;
}

int main(void) {
  if (run_exact_success_case() != 0) {
    return 1;
  }
  if (run_short_read_case() != 0) {
    return 1;
  }
  return 0;
}
