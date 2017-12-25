#! /bin/bash

ocamlfind ocamlopt -package core -linkpkg -thread -o test test.ml
