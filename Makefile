
default_target: all

.PHONY: update_all clone_all bbv riscv-coq

clone_all:
	git submodule update --init --recursive

update_all:
	git submodule update --recursive --remote

REL_PATH_OF_THIS_MAKEFILE:=$(lastword $(MAKEFILE_LIST))
ABS_ROOT_DIR:=$(abspath $(dir $(REL_PATH_OF_THIS_MAKEFILE)))

DEPS_DIR ?= $(ABS_ROOT_DIR)/deps
export DEPS_DIR

bbv:
	$(MAKE) -C $(DEPS_DIR)/bbv

riscv-coq: bbv
	$(MAKE) -C $(DEPS_DIR)/riscv-coq

convert: bbv riscv-coq
	$(MAKE) -C theories

run: convert
	sbt -no-colors run

all: run
