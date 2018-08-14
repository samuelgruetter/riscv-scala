
default_target: all

COQC=$(COQBIN)coqc
COQTOP=$(COQBIN)coqtop
COQDEP=$(COQBIN)coqdep
COQDOC=$(COQBIN)coqdoc

DEPS_DIR ?= ../deps

# Note: make does not interpret "\n", and this is intended
DEPFLAGS_NL=-Q . riscvscala\n-Q $(DEPS_DIR)/bbv/theories bbv \n-Q $(DEPS_DIR)/riscv-coq/src riscv
DEPFLAGS=$(subst \n, ,$(DEPFLAGS_NL))

_CoqProject:
	echo -e '$(DEPFLAGS_NL)' > _CoqProject

COQFLAGS=$(DEPFLAGS)

Tools.vo: Tools.v
	$(COQC) $(COQFLAGS) Tools.v 

SCALA_DIR ?= ../src/main/scala/riscv

$(SCALA_DIR)/Decode.scala Decode.vo: Decode.v Tools.vo
	$(COQC) $(COQFLAGS) Decode.v > $(SCALA_DIR)/Decode.scala

all: _CoqProject $(SCALA_DIR)/Decode.scala

.depend depend:
	$(COQDEP) $(DEPFLAGS) >.depend `find $(DIRS) -name "*.v"`

clean:
	find . -type f \( -name '*.glob' -o -name '*.vo' -o -name '*.aux' \) -delete
	rm $(SCALA_DIR)/Decode.scala
	rm .depend

include .depend

