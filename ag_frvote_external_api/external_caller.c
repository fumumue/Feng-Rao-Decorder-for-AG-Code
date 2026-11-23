#include "ag_frvote.h"
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv) {
  int injected = argc > 1 ? atoi(argv[1]) : 1;
  if (injected < 0 || injected > 2) return 2;
  uint16_t received[1009] = {0};
  const size_t want_pos[2] = {5, 99};
  const uint16_t want_val[2] = {7, 31};
  size_t positions[8] = {0};
  uint16_t values[8] = {0};
  size_t count = 0;
  for (int i = 0; i < injected; ++i)
    received[want_pos[i]] = want_val[i];

  char a0[] = "external_caller";
  char a1[] = "--m", a2[] = "6";
  char a3[] = "--q", a4[] = "4";
  char a5[] = "--errors", a6[] = "2";
  char a7[] = "--M", a8[] = "250";
  char a9[] = "-frvote";
  char *opts[] = {a0,a1,a2,a3,a4,a5,a6,a7,a8,a9};

  int rc = ag_frvote_decode((int)(sizeof opts / sizeof opts[0]), opts,
                           received, 1009, positions, values, 8, &count);
  printf("API return=%d, recovered=%zu, expected=%d\n", rc, count, injected);
  if (rc != 0 || count != (size_t)injected) return 1;
  for (int i = 0; i < injected; ++i) {
    printf("error[%d]: position=%zu value=%u\n", i, positions[i], values[i]);
    if (positions[i] != want_pos[i] || values[i] != want_val[i]) return 1;
  }
  return 0;
}
