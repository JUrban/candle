#!/bin/bash
# Set up "strict mode" for bash
set -euo pipefail

# Create (if needed) + Change into the build directory
mkdir -p candle/build
cd candle/build

# Get the 64-bit CakeML compiler from here:
curl -OL https://cakeml.org/regression/artefacts/3286/cake-x64-64.tar.gz
tar xvzf cake-x64-64.tar.gz --strip-components=1

# By default, the CakeML compiler reserves a few kilobytes for constants and
# code produced by the dynamic compiler. Using Candle requires setting these
# to some megabytes (or hundreds of megabytes for some of the more heavier
# files in HOL Light, such as make_complex.ml).
patch cake.S ../cake.S.patch

# Build the compiler binary
make

# Create the types.txt file necessary for candle_insulate.py
./cake --types < /dev/null > types.txt 2>&1

# Generate candle_insulate.ml
python3 ../insulate.py types.txt insulate.ml

# The CakeML bootstrap reads these two files from its current directory.  Use
# relative links so candle.sh can launch from CANDLE_ROOT without a custom
# chdir FFI, and so moving the complete checkout preserves the links.
ln -sfn candle/build/config_enc_str.txt ../../config_enc_str.txt
ln -sfn candle/build/candle_boot.ml ../../candle_boot.ml

# You can now run Candle by writing:
#   $ ./candle.sh
# (without the $) at your prompt. Load the HOL Light sources by writing:
#   > #use "hol.ml";;
# (without > and with double semicolons) in the REPL.
#
