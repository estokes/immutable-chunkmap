#! /bin/bash

B=target/release/bench

function run() {
  KIND="$1"
  SIZE="$2"
  echo "$KIND at $SIZE"
  for k in 1 2 3; do
    if ! test "$KIND" == "ls" -a "$SIZE" -gt 100000; then
      $B $KIND $SIZE
    fi
  done
}

# std avl
for i in 1000 10000 100000 1000000 10000000; do
  for j in avl rc btm hm bs ls; do
    run $j $i
  done
done
