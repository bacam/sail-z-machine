#!/bin/bash

set -ex

(cd src; sail -c --c-no-main -o ../zmachine prelude.sail base.sail list.sail memory.sail zstring.sail instructions.sail fetch_decode.sail init.sail main.sail memory_interface.sail)
SAIL_DIR=`sail --dir`
gcc -g zmachine.c "$SAIL_DIR"/lib/*.c -lgmp -lz -I "$SAIL_DIR"/lib/ src/main.c -o zmachine
