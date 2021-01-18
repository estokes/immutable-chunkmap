#! /bin/bash

ocamlfind ocamlopt -package base -linkpkg -thread -o test test.ml
