# This Makefile uses ocamlbuild but does not rely on ocamlfind or the Opam
# package manager to build.
#
# See README.me for instructions.


# Configuration

NAME =		wln

WASMBASE = ../../../interpreter
WASMDIRS =	util syntax binary script text valid runtime exec host main unittest jslib
WASMFILES = Makefile dune dune-project $(shell cd $(WASMBASE); ls $(foreach DIR,$(WASMDIRS),$(DIR)/*))

WASMDIR =		_wasm
WASMDEPS =	$(WASMFILES:%=$(WASMDIR)/%)
WASMTESTDIR =	$(WASMBASE)/../test/core

BUILDDIR =     _build/default


# Main targets

.PHONY:		default all ci

default:	$(NAME)
all:		default
ci:		all test


# Mirroring Wasm

.PHONY: wasm-deps
wasm-deps: $(WASMDEPS)
	@echo $(WASMDEPS)

$(WASMDIR):
		mkdir -p $@
		touch $@/dune-workspace

$(WASMDIRS:%=$(WASMDIR)/%): $(WASMDIR)/%:
		mkdir -p $@

$(WASMFILES:%=$(WASMDIR)/%): $(WASMDIR)/%: $(WASMBASE)/% $(WASMDIR) $(WASMDIRS:%=$(WASMDIR)/%)
		cp $< $@

$(WASMDIR)/_build/wasm.cmx $(WASMDIR)/_build/wasm.cmxa: $(WASMDEPS)
		make -C $(WASMDIR) TESTDIR=$(WASMTESTDIR) install
		touch $@
		dune clean


# Building executable

# Building executable

.PHONY:                $(NAME)

$(NAME):
	@rm -f $@
	dune build $@.exe
	ln $(BUILDDIR)/$@.exe $@


# Executing test suite

TESTDIR =	test
TESTFILES =	$(shell cd $(TESTDIR); ls *.$(EXT))
TESTS =		$(TESTFILES:%.$(EXT)=%)

.PHONY:		test

test:	$(NAME)
	(cd $(TESTDIR); ../$(NAME) a.wat d/b.wat c.wat -o o.wat -v)


# Miscellaneous targets

.PHONY:		clean

clean: cleantest
		rm -rf $(WASMDIR) $(RUNTIME).wasm _tags
		dune clean

cleantest:
		rm -f test/*.wasm test/*.wat
