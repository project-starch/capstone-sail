#!/bin/bash

set -e

# Build the C emulator
make csim SAIL_DIR="$SAIL_DIR" # TODO: containerise

# Build package
apptainer/build-package.sh

if [ -z "$TARGET_DIR" ]; then
    TARGET_DIR=./packages
fi
    
FILE_NAME=$(date -Iseconds).sif
mkdir -p $TARGET_DIR
mv apptainer/package.sif $TARGET_DIR/$FILE_NAME
ln -sfnr $TARGET_DIR/$FILE_NAME $TARGET_DIR/latest.sif
