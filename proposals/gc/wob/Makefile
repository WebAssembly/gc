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
FLAGS = 	-lexflags -ml -cflags '-w +a-4-27-42-44-45 -warn-error +a-3'
OCB =		ocamlbuild -verbose 8 $(FLAGS) $(DIRS:%=-I %) $(LIBS:%=-lib %) -cflags '$(INCLS:%=-I %)' -lflags '$(INCLS:%=-I %)'


# Main targets

.PHONY:		default debug opt unopt

default:	opt
debug:		unopt
opt:		$(OPT)
unopt:		$(UNOPT)
all:		unopt opt test


# Mirroring Wasm

#_build/wasm.%: $(WASMDIR)/_build/wasm.%
#		mkdir -p _build
#		cp $(WASMDIR)/_build/wasm.* _build/

$(WASMDIR)/_build/wasm.cmx $(WASMDIR)/_build/wasm.cmxa: $(WASMDEPS)
		make -C _wasm libopt

$(WASMDIR)/_build/wasm.cmo $(WASMDIR)/_build/wasm.cma: $(WASMDEPS)
		make -C _wasm libunopt

$(WASMDIRS:%=$(WASMDIR)/%): $(WASMDIR)/%:
		mkdir -p $@

$(WASMFILES:%=$(WASMDIR)/%): $(WASMDIR)/%: $(WASMBASE)/% $(WASMDIRS:%=$(WASMDIR)/%)
		cp $< $@


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
main.byte: _tags $(INCLS)/wasm.cma
		$(OCB) -quiet $@

main.native: _tags $(INCLS)/wasm.cmxa
		$(OCB) -quiet $@


# Executing test suite

TESTDIR =	test
TESTFILES =	$(shell cd $(TESTDIR); ls *.wob)
TESTS =		$(TESTFILES:%.wob=%)

.PHONY:		test debugtest partest

test:		$(OPT)
		$(TESTDIR)/run.py --wasm `pwd`/$(OPT) $(if $(JS),--js '$(JS)',)
debugtest:	$(UNOPT)
		$(TESTDIR)/run.py --wasm `pwd`/$(UNOPT) $(if $(JS),--js '$(JS)',)

test/%:		$(OPT)
		$(TESTDIR)/run.py --wasm `pwd`/$(OPT) $(if $(JS),--js '$(JS)',) $(TESTDIR)/$(@F).wast
debugtest/%:	$(UNOPT)
		$(TESTDIR)/run.py --wasm `pwd`/$(UNOPT) $(if $(JS),--js '$(JS)',) $(TESTDIR)/$(@F).wast

run/%:		$(OPT)
		./$(OPT) $(TESTDIR)/$(@F).wast
debug/%:	$(UNOPT)
		./$(UNOPT) $(TESTDIR)/$(@F).wast

partest: 	$(TESTS:%=quiettest/%)
		@echo All tests passed.

quiettest/%:	$(OPT)
		@ ( \
		  $(TESTDIR)/run.py 2>$(@F).out --wasm `pwd`/$(OPT) $(if $(JS),--js '$(JS)',) $(@F:%=$(TESTDIR)/%.wast) && \
		  rm $(@F).out \
		) || \
		cat $(@F).out || rm $(@F).out || exit 1


# Miscellaneous targets

.PHONY:		clean

clean:
		rm -rf $(WASMDIR) _tags
		$(OCB) -clean
