ASM_SOURCES=$(wildcard *.S)
TARGETS=$(patsubst %.S,build/%,$(ASM_SOURCES))
RUN_OCAML=$(patsubst %.S,run-ocaml-%,$(ASM_SOURCES))
RUN_C=$(patsubst %.S,run-c-%,$(ASM_SOURCES))
CFLAGS=-nostdlib -static -I env/p -I macros -T env/p/link.ld
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

$(TARGETS):build/%:%.S
	mkdir -p build
	$(CC) $(CFLAGS) -o $@ $^

clean:
	rm -rf build
