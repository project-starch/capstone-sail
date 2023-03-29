SHELL:=/bin/bash

TESTSUITE_SOURCE_PATH=./testsuite/capstone
PREAMBLE_FILE=./preamble.S
EPILOGUE_FILE=./epilogue.S
TRANSFORM_CMD=gawk -f ./transform-testcase.awk
ASM_SOURCES=$(filter-out $(TESTSUITE_SOURCE_PATH)/exit.S,$(wildcard $(TESTSUITE_SOURCE_PATH)/*.S))
TARGETS=$(patsubst $(TESTSUITE_SOURCE_PATH)/%.S,build/%,$(ASM_SOURCES))
RUN_OCAML=$(patsubst $(TESTSUITE_SOURCE_PATH)/%.S,run-ocaml-%,$(ASM_SOURCES))
RUN_C=$(patsubst $(TESTSUITE_SOURCE_PATH)/%.S,run-c-%,$(ASM_SOURCES))
CFLAGS=-nostdlib -static -I env/p -I macros -I $(TESTSUITE_SOURCE_PATH) -T env/p/link.ld
CC=riscv64-unknown-elf-gcc

OCAML_SIM=../ocaml_emulator/riscv_ocaml_sim_RV64
C_SIM=../c_emulator/riscv_sim_RV64

.PHONY: all clean run-c run-ocaml $(RUN_C) $(RUN_OCAML)

all: $(TARGETS)

run-c: $(RUN_C)

run-ocaml: $(RUN_OCAML)

$(RUN_C):run-c-%:build/%
	$(C_SIM) $^

$(RUN_OCAML):run-ocaml-%:build/%
	$(OCAML_SIM) $^

$(TARGETS):build/%:$(TESTSUITE_SOURCE_PATH)/%.S
	mkdir -p build
	$(TRANSFORM_CMD) $^ | cat $(PREAMBLE_FILE) /dev/stdin $(EPILOGUE_FILE) | $(CC) $(CFLAGS) -o $@ -xassembler-with-cpp /dev/stdin

clean:
	rm -rf build
