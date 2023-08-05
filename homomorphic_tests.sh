#!/bin/bash

OUTPUT_FOLDER="homomorphic-tests-results"
FILES="examples/homomorphism/*"

make default

if [ ! -d $OUTPUT_FOLDER ]; then
  mkdir $OUTPUT_FOLDER
fi

rm -r $OUTPUT_FOLDER/*

for f in $FILES
do
    if [ ! -d $f ]; then
        echo -e "\n\n\n\n\n\n\n"
        echo "--- Processing $f ---"
        /home/$USER/.local/bin/tamarin-prover $f --prove --derivcheck-timeout=0 --Output=$OUTPUT_FOLDER
    fi
done