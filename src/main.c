#include <stdio.h>

#include "sail.h"
#include "rts.h"

// From generated model
void model_init(void);
unit zmain(unit);
void model_fini(void);
void model_pre_exit();
extern int64_t zversion;

int main(int argc, char *argv[]) {
  if (argc != 2) {
    fprintf(stderr, "Usage: zmachine <file>\n");
    return 1;
  }
  model_init();
  load_raw(0, argv[1]);
  zversion = read_mem(0);
  zmain(UNIT);
  model_fini();
  model_pre_exit();

  return 0;
}
