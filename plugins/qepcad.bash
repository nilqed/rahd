#!/bin/bash
#
# Needs spawning RAHD process's PID as a parameter ($1).
#

# remove any old output files from previous runs
rm ~/.rahd/plugins/$1.qepcad.out.*

# convert AND symbols to QEPCAD-B format and remove quotes

sed -e 's/"//g' ~/.rahd/plugins/$1.qepcad.in.raw > ~/.rahd/plugins/$1.qepcad.in.final

# send goal to QEPCAD-B and convert its response to a file
# containing either "TRUE" or "FALSE"

qepcad +N8000000 < ~/.rahd/plugins/$1.qepcad.in.final > ~/.rahd/plugins/$1.qepcad.out.raw

cat ~/.rahd/plugins/$1.qepcad.out.raw | grep TRUE > ~/.rahd/plugins/$1.qepcad.out.1
cat ~/.rahd/plugins/$1.qepcad.out.raw | grep FALSE >> ~/.rahd/plugins/$1.qepcad.out.1
sed -e 's/TRUE/"TRUE"/g' ~/.rahd/plugins/$1.qepcad.out.1 > ~/.rahd/plugins/$1.qepcad.out.2
sed -e 's/FALSE/"FALSE"/g' ~/.rahd/plugins/$1.qepcad.out.2 > ~/.rahd/plugins/$1.qepcad.out
