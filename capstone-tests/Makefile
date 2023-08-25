SHELL:=/bin/bash

# by default, start in secure world
START_IN_NORMAL?=0

ifeq ($(START_IN_NORMAL),0)
TESTSUITE_SOURCE_PATH=./testsuite/secure-world
PREAMBLE_FILE=./preamble-secure.S
EPILOGUE_FILE=./epilogue-secure.S
else
TESTSUITE_SOURCE_PATH=./testsuite/normal-world
PREAMBLE_FILE=./preamble-normal.S
EPILOGUE_FILE=./epilogue-normal.S
endif

TRANSFORM_CMD=gawk -f ./transform-testcase.awk
ASM_SOURCES=$(filter-out $(TESTSUITE_SOURCE_PATH)/exit.S,$(wildcard $(TESTSUITE_SOURCE_PATH)/*.S))
TARGETS=$(patsubst $(TESTSUITE_SOURCE_PATH)/%.S,build/%,$(ASM_SOURCES))
RUN_OCAML=$(patsubst $(TESTSUITE_SOURCE_PATH)/%.S,run-ocaml-%,$(ASM_SOURCES))
RUN_C=$(patsubst $(TESTSUITE_SOURCE_PATH)/%.S,run-c-%,$(ASM_SOURCES))
DEBUG_TARGETS=$(patsubst $(TESTSUITE_SOURCE_PATH)/%.S,debug-%,$(ASM_SOURCES))

USE_GCC?=0 # by default, clang is used
ifeq ($(USE_GCC),1)
CC?=riscv64-unknown-elf-gcc
EXTRA_CFLAGS?=
else
CC?=clang
EXTRA_CFLAGS?=--target=riscv64 -march=rv64imxcheri_xcapstone -mabi=l64pc128 -O0 -mno-relax
endif

SHOW_TRACE?=0
ifeq ($(SHOW_TRACE),1)
C_SIM_FLAGS?=
else
C_SIM_FLAGS?=-V
endif

LINKER_SCRIPT?=-T env/p/link.ld 
CFLAGS=-nostdlib -static -I env/p -I macros -I testsuite -I $(TESTSUITE_SOURCE_PATH) $(LINKER_SCRIPT) $(EXTRA_CFLAGS)

OCAML_SIM=../ocaml_emulator/riscv_ocaml_sim_RV64
C_SIM=../c_emulator/riscv_sim_RV64
TIMEOUT?=10

VIEW_HEAD?=0

.PHONY: all clean run-c run-ocaml $(RUN_C) $(RUN_OCAML) $(DEBUG_TARGETS) list

all: $(TARGETS)

run-c: $(RUN_C)

run-ocaml: $(RUN_OCAML)

$(RUN_C):run-c-%:build/%
ifneq ($(VIEW_HEAD),0)
	timeout $(TIMEOUT) $(C_SIM) $(C_SIM_FLAGS) $^ 2>&1 | head -n $(VIEW_HEAD)
else
	timeout $(TIMEOUT) $(C_SIM) $(C_SIM_FLAGS) $^
endif

$(RUN_OCAML):run-ocaml-%:build/%
	$(OCAML_SIM) $^

$(TARGETS):build/%:$(TESTSUITE_SOURCE_PATH)/%.S
	mkdir -p build
	$(TRANSFORM_CMD) $^ | cat $(PREAMBLE_FILE) /dev/stdin $(EPILOGUE_FILE) | $(CC) $(CFLAGS) -o $@ -xassembler-with-cpp /dev/stdin

$(DEBUG_TARGETS):debug-%:build/%
	gdb --args $(C_SIM) $^

clean:
	rm -rf build

list:
	@echo "Included test cases:"
	@$(foreach testcase,$(patsubst build/%,%,$(TARGETS)),echo "  $(testcase)";)
