# This Makefile uses ocamlbuild but does not rely on ocamlfind or the Opam
# package manager to build.
#
# See README.me for instructions.


# Configuration

NAME =		wob
UNOPT = 	$(NAME).debug
OPT =   	$(NAME)

WASMBASE = ../../../interpreter
WASMDIRS =	util syntax binary script text valid runtime exec host main
WASMFILES = Makefile $(shell cd $(WASMBASE); ls $(foreach DIR,$(WASMDIRS),$(DIR)/*))

WASMDIR =		_wasm
WASMDEPS =	$(WASMFILES:%=$(WASMDIR)/%)

DIRS =		src
LIBS =		bigarray wasm
INCLS =		$(PWD)/_wasm/_build
FLAGS = 	-lexflags -ml -cflags '-w +a-4-27-37-42-44-45 -warn-error +a-3'
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

$(WASMDIR):
		mkdir -p $@

$(WASMDIRS:%=$(WASMDIR)/%): $(WASMDIR)/%:
		mkdir -p $@

$(WASMFILES:%=$(WASMDIR)/%): $(WASMDIR)/%: $(WASMBASE)/% $(WASMDIRS:%=$(WASMDIR)/%)
		cp $< $@

$(WASMDIR)/_build/wasm.cmx $(WASMDIR)/_build/wasm.cmxa: $(WASMDEPS)
		make -C $(WASMDIR) libopt

$(WASMDIR)/_build/wasm.cmo $(WASMDIR)/_build/wasm.cma: $(WASMDEPS)
		make -C $(WASMDIR) libunopt



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
TESTFILES =	$(shell cd $(TESTDIR); ls *.wob)
TESTS =		$(TESTFILES:%.wob=%)

.PHONY:		test debugtest partest

test:		$(TESTFILES:%.wob=test/%)
wasmtest:		cleantest $(TESTFILES:%.wob=wasmtest/%)
debugtest:	$(TESTFILES:%.wob=debugtest/%)

test/%:		$(OPT)
		@ ./$(NAME) -r $(TESTDIR)/$(@F).wob
wasmtest/%:		$(OPT)
	  @ if ! grep -q "@FAIL-WASM" $(TESTDIR)/$(@F).wob; \
		  then ./$(NAME) -r -c -v $(TESTDIR)/$(@F).wob; \
		  else echo Skipping $(@F).wob; \
		fi
debugtest/%:	$(UNOPT)
		@ ./$(NAME) -r $(TESTDIR)/$(@F).wob


# Miscellaneous targets

.PHONY:		clean

clean:
		rm -rf $(WASMDIR) _tags
		$(OCB) -clean

cleantest:
		rm -f test/*.wasm test/*.wos
