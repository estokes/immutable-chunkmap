#! /bin/bash

B=target/release/bench

function run() {
  KIND="$1"
  SIZE="$2"
  for k in 1 2 3; do
    if ! test "$KIND" == "ls" -a "$SIZE" -gt 100000; then
      $B $KIND $SIZE
    fi
  done
}

#for j in avl rc btm hm bs ls vec; do
for j in cm; do
  echo "testing $j"
  for i in 1000 10000 100000 1000000 10000000; do
    run $j $i
  done
done
