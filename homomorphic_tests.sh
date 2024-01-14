#!/bin/bash

OUTPUT_FOLDER="homomorphic-tests-results"
INPUT_FOLDER="examples/homomorphism"
INPUT_FOLDER2="examples/homomorphism-fixinpost"

function all_homomorphic () {
	if [ ! -d $OUTPUT_FOLDER ]; then
    mkdir $OUTPUT_FOLDER
  fi

  rm -r $OUTPUT_FOLDER/*

  if [ $1 ]; then
    /home/$USER/.local/bin/tamarin-prover $1
    /home/$USER/.local/bin/tamarin-prover $1 --prove --Output=$OUTPUT_FOLDER
  fi

  for f in $INPUT_FOLDER/*
  do
    if [ ! -d $f ] && [ ! $1 ]; then
      echo -e "\n\n\n\n\n\n\n"
      echo "--- Processing $f ---"
      /home/$USER/.local/bin/tamarin-prover $f --prove --Output=$OUTPUT_FOLDER
    fi
  done
}

make default

while getopts ":ictp" flag; do
  case $flag in
    t)
      /home/$USER/.local/bin/tamarin-prover test
      ;;
    i)
      /home/$USER/.local/bin/tamarin-prover interactive $INPUT_FOLDER
      ;;
    p)
      /home/$USER/.local/bin/tamarin-prover interactive $INPUT_FOLDER2
      ;;
    c)
      all_homomorphic $2
      ;;
  esac
done