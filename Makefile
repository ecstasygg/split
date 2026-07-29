SDK ?= $(HOME)/.cache/split/microkit-sdk-2.3.1
TOOL ?= $(HOME)/.cache/split/microkit-2.3.1/target/release/microkit
BOARD := $(SDK)/board/qemu_virt_aarch64/debug
CC := aarch64-linux-gnu-gcc
LD := aarch64-linux-gnu-ld
CFLAGS := -std=gnu11 -O2 -g -Wall -Wextra -Werror -Wno-unused-function -ffreestanding -nostdlib -mstrict-align -I$(BOARD)/include
QEMU := qemu-system-aarch64 -machine virt,virtualization=on -cpu cortex-a53 -m 2G -nographic -monitor none -serial stdio

.PHONY: all proof clean
all: build/loader.img

build:
	mkdir -p build

build/pager.o: pager.c split.h | build
	$(CC) $(CFLAGS) -c $< -o $@

build/alpha.o: client.c split.h | build
	$(CC) $(CFLAGS) -DCLIENT=0 -c $< -o $@

build/beta.o: client.c split.h | build
	$(CC) $(CFLAGS) -DCLIENT=1 -c $< -o $@

build/unsafe.o: pager.c split.h | build
	$(CC) $(CFLAGS) -DSHARED_WRITE=1 -c $< -o $@

build/%.elf: build/%.o
	$(LD) -L$(BOARD)/lib $< -lmicrokit -Tmicrokit.ld -o $@

build/loader.img: build/pager.elf build/alpha.elf build/beta.elf split.system
	MICROKIT_SDK=$(SDK) $(TOOL) --board qemu_virt_aarch64 --config debug --search-path build -o $@ -r build/report.txt split.system

build/unsafe.img: build/unsafe.elf build/alpha.elf build/beta.elf split.system
	sed 's/pager.elf/unsafe.elf/' split.system > build/unsafe.system
	MICROKIT_SDK=$(SDK) $(TOOL) --board qemu_virt_aarch64 --config debug --search-path build -o $@ -r build/unsafe.txt build/unsafe.system

proof:
	isabelle build -D .

build/split.ml: Export.thy Reuse.thy Snapshot.thy Execution.thy Protocol.thy Isolation.thy Model.thy ROOT | build
	isabelle build -D .
	isabelle export -n -d . -O build/generated -x 'Split.Export:code/**' Split
	cp build/generated/Split.Export/code/split.ocaml $@

clean:
	rm -rf build
