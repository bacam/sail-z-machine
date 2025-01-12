#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>

#include "sail.h"

void string_hd(sail_int *r, const_sail_string s) {
  mpz_set_ui(*r, s[0]);
}

void read_command_plain(sail_string *s, sail_int smax) {
  sail_free(*s);
  mach_int max = CREATE_OF(mach_int, sail_int)(smax);
  *s = malloc(max + 1);
  ssize_t r = read(0, *s, max);
  if (r == -1) {
    perror("read failed");
    exit(1);
  }
  (*s)[r] = 0;
}
