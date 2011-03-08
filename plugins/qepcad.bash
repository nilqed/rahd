#!/bin/bash

# remove any old output files from previous runs
rm ~/.rahd/plugins/proofobl.out.*

# convert AND symbols to QEPCAD-B format and remove quotes

sed -e 's/"//g' ~/.rahd/plugins/proofobl.in.raw > ~/.rahd/plugins/proofobl.in.final

# send goal to QEPCAD-B and convert its response to a file
# containing either "TRUE" or "FALSE"

qepcad +N8000000 < ~/.rahd/plugins/proofobl.in.final > ~/.rahd/plugins/proofobl.out.raw

cat ~/.rahd/plugins/proofobl.out.raw | grep TRUE > ~/.rahd/plugins/proofobl.out.1
cat ~/.rahd/plugins/proofobl.out.raw | grep FALSE >> ~/.rahd/plugins/proofobl.out.1
sed -e 's/TRUE/"TRUE"/g' ~/.rahd/plugins/proofobl.out.1 > ~/.rahd/plugins/proofobl.out.2
sed -e 's/FALSE/"FALSE"/g' ~/.rahd/plugins/proofobl.out.2 > ~/.rahd/plugins/proofobl.out
