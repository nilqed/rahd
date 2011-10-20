#!/bin/bash

export COCOA_PACKAGES=~/AlgebraSystems/CoCoA/cocoa-4.7/packages
rm cocoa-gb.out
cocoa_text < cocoa-gb.in > cocoa-gb.log
