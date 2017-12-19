#! /bin/bash

B=target/release/bench

function run() {
  KIND="$1"
  SIZE="$2"
  echo "$KIND at $SIZE"
  for i in 1 2 3; do
    $B $KIND $SIZE
  done
}

# std avl
for i in 1000 10000 100000 1000000 10000000; do
  for j in avl rc btm hm bs ls; do
    run $j $i
  done
done
