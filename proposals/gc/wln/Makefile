# This Makefile uses ocamlbuild but does not rely on ocamlfind or the Opam
# package manager to build.
#
# See README.me for instructions.


# Configuration

NAME =		wln
UNOPT = 	$(NAME).debug
OPT =   	$(NAME)

WASMBASE = ../../../interpreter
WASMDIRS =	util syntax binary script text valid runtime exec host main tests
WASMFILES = Makefile $(shell cd $(WASMBASE); ls $(foreach DIR,$(WASMDIRS),$(DIR)/*))

WASMDIR =		_wasm
WASMDEPS =	$(WASMFILES:%=$(WASMDIR)/%)
WASMTESTDIR =	$(WASMBASE)/../test

DIRS =		src
LIBS =		bigarray wasm
INCLS =		$(PWD)/_wasm/_build
FLAGS = 	-lexflags -ml -cflags '-w +a-4-27-37-42-44-45-70 -warn-error +a-3'
OCB =		ocamlbuild -verbose 8 $(FLAGS) $(DIRS:%=-I %) $(LIBS:%=-lib %) -cflags '$(INCLS:%=-I %)' -lflags '$(INCLS:%=-I %)'


# Main targets

.PHONY:		default debug opt unopt

default:	opt
debug:		unopt
opt:		$(OPT)
unopt:		$(UNOPT)
all:		unopt opt test


# Mirroring Wasm

.PHONY: wasm-deps
wasm-deps: $(WASMDEPS)
	@echo $(WASMDEPS)

$(WASMDIR):
		mkdir -p $@

$(WASMDIRS:%=$(WASMDIR)/%): $(WASMDIR)/%:
		mkdir -p $@

$(WASMFILES:%=$(WASMDIR)/%): $(WASMDIR)/%: $(WASMBASE)/% $(WASMDIRS:%=$(WASMDIR)/%)
		cp $< $@

$(WASMDIR)/_build/wasm.cmx $(WASMDIR)/_build/wasm.cmxa: $(WASMDEPS)
		make -C $(WASMDIR) TESTDIR=$(WASMTESTDIR) libopt
		touch $@
		$(OCB) -clean

$(WASMDIR)/_build/wasm.cmo $(WASMDIR)/_build/wasm.cma: $(WASMDEPS)
		make -C $(WASMDIR) TESTDIR=$(WASMTESTDIR) libunopt
		touch $@
		$(OCB) -clean


# Building executable

.INTERMEDIATE:	_tags
_tags:
		echo >$@ "true: bin_annot"
		echo >>$@ "true: debug"

$(UNOPT): main.byte
		mv $< $@

$(OPT):		main.native
		mv $< $@

.PHONY:		main.byte main.native
main.byte: _tags $(WASMDIR)/_build/wasm.cma
		$(OCB) -quiet $@

main.native: _tags $(WASMDIR)/_build/wasm.cmxa
		$(OCB) -quiet $@


# Executing test suite

TESTDIR =	test
TESTFILES =	$(shell cd $(TESTDIR); ls *.$(EXT))
TESTS =		$(TESTFILES:%.$(EXT)=%)

.PHONY:		test

test:	$(OPT)
	(cd $(TESTDIR); ../$(NAME) a.wat d/b.wat c.wat -o o.wat -v)


# Miscellaneous targets

.PHONY:		clean

clean: cleantest
		rm -rf $(WASMDIR) $(RUNTIME).wasm _tags
		$(OCB) -clean

cleantest:
		rm -f test/*.wasm test/*.wat
