#!/bin/bash

# remove any old output files from previous runs
rm ./plugins/proofobl.out.*

# convert AND symbols to QEPCAD-B format and remove quotes

sed -e 's/"//g' ./plugins/proofobl.in.raw > ./plugins/proofobl.in.final

# send goal to QEPCAD-B and convert its response to a file
# containing either "TRUE" or "FALSE"

qepcad +N8000000 < ./plugins/proofobl.in.final > ./plugins/proofobl.out.raw

cat ./plugins/proofobl.out.raw | grep TRUE > ./plugins/proofobl.out.1
cat ./plugins/proofobl.out.raw | grep FALSE >> ./plugins/proofobl.out.1
sed -e 's/TRUE/"TRUE"/g' ./plugins/proofobl.out.1 > ./plugins/proofobl.out.2
sed -e 's/FALSE/"FALSE"/g' ./plugins/proofobl.out.2 > ./plugins/proofobl.out
