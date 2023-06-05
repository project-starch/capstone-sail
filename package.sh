#!/bin/bash

set -e

# Build the C emulator
make csim # TODO: containerise

# Build package
apptainer/build-package.sh

TARGET_DIR=./packages
FILE_NAME=$(date -Iseconds).sif
mkdir -p $TARGET_DIR
mv apptainer/package.sif $TARGET_DIR/$FILE_NAME
ln -sfnr $TARGET_DIR/$FILE_NAME $TARGET_DIR/latest.sif


