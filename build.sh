#!/bin/bash

set -ex

(cd src; sail -c --c-no-main -o ../zmachine prelude.sail base.sail list.sail memory.sail zstring.sail routine.sail instructions.sail fetch_decode.sail init.sail main.sail memory_interface.sail -c_include extralib.h)
SAIL_DIR=`sail --dir`
gcc -g src/extralib.c zmachine.c -I src "$SAIL_DIR"/lib/*.c -lgmp -lz -I "$SAIL_DIR"/lib/ src/main.c -o zmachine
