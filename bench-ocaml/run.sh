#! /bin/bash

for i in 1000 10000 100000 1000000 10000000; do
  echo "size $i"
  for j in 1 2 3; do
    ./test $i
  done
done
