#! /bin/bash

B=target/release/bench

function run() {
  KIND="$1"
  TYP="$2"
  SIZE="$3"
  for k in 1 2 3; do
      $B $KIND $TYP $SIZE
  done
}

echo "testing $j $2"
for i in 1000 10000 100000 1000000 10000000; do
    run $1 $2 $i
done
