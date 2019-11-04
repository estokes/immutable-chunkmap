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

for j in $@; do
  echo "testing $j ptr"
  for i in 1000 10000 100000 1000000 10000000; do
    run $j ptr $i
  done
  echo "testing $j str"
  for i in 1000 10000 100000 1000000 10000000; do
    run $j str $i
  done
done
