#!/bin/bash

rm ./plugins/$1.redlog.out
rm ./plugins/$1.redlog.out.final
redpsl < ./plugins/$1.redlog.in
sed '/^$/d' ./plugins/$1.redlog.out > ./plugins/$1.redlog.out.final

# Redlog output will be written by Redlog
#  into $1.redlog.out.

