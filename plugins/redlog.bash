#!/bin/bash

rm ~/.rahd/plugins/$1.redlog.out
rm ~/.rahd/plugins/$1.redlog.out.final
redpsl < ~/.rahd/plugins/$1.redlog.in
sed '/^$/d' ~/.rahd/plugins/$1.redlog.out > ~/.rahd/plugins/$1.redlog.out.final

# Redlog output will be written by Redlog
#  into $1.redlog.out.

