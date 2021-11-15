# This Makefile uses ocamlbuild but does not rely on ocamlfind or the Opam
# package manager to build.
#
# See README.me for instructions.


# Configuration

NAME =		waml
EXT =			$(NAME)
UNOPT = 	$(NAME).debug
OPT =   	$(NAME)
RUNTIME =	$(NAME)-runtime

WASMBASE = ../../../interpreter
WASMDIRS =	util syntax binary script text valid runtime exec host main
WASMFILES = Makefile $(shell cd $(WASMBASE); ls $(foreach DIR,$(WASMDIRS),$(DIR)/*))

WASMDIR =		_wasm
WASMDEPS =	$(WASMFILES:%=$(WASMDIR)/%)

WASMLINK =	wln
WASMLINKDIR =	../$(WASMLINK)

DIRS =		src
LIBS =		bigarray wasm
INCLS =		$(PWD)/_wasm/_build
FLAGS = 	-lexflags -ml -cflags '-w +a-4-27-37-42-44-45 -warn-error +a-3'
OCB =		ocamlbuild -verbose 8 $(FLAGS) $(DIRS:%=-I %) $(LIBS:%=-lib %) -cflags '$(INCLS:%=-I %)' -lflags '$(INCLS:%=-I %)'

NODE =		node --experimental-wasm-gc


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
		make -C $(WASMDIR) libopt
		touch $@
		$(OCB) -clean

$(WASMDIR)/_build/wasm.cmo $(WASMDIR)/_build/wasm.cma: $(WASMDEPS)
		make -C $(WASMDIR) libunopt
		touch $@
		$(OCB) -clean

$(WASMDIR)/wasm:	$(WASMDEPS)
		make -C $(WASMDIR)


# Building linker

.PHONY:	$(WASMLINK)

$(WASMLINK):
		make -C $(WASMLINKDIR)


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
LINKFILES =	$(shell cd $(TESTDIR); ls *.$(WASMLINK))
TESTS =		$(TESTFILES:%.$(EXT)=%)

.PHONY:		test runtimetest evaltest debugtest wasmtest wasmntest nodetest linktest

test:	runtimetest evaltest wasmtest wasmntest linktest # nodetest

evaltest:		titletest/Test-eval $(TESTFILES:%.$(EXT)=evaltest/%)
debugtest:	titletest/Test-debug $(TESTFILES:%.$(EXT)=debugtest/%)
wasmtest:		cleantest titletest/Test-wasm $(TESTFILES:%.$(EXT)=wasmtest/%)
		@make cleantest
wasmntest:		cleantest titletest/Test-wasm-headless $(TESTFILES:%.$(EXT)=wasmntest/%)
		@make cleantest
nodetest:		cleantest titletest/Test-node $(RUNTIME).wasm $(TESTFILES:%.$(EXT)=nodetest/%)
		@make cleantest
linktest:		titletest/Test-link $(LINKFILES:%.$(WASMLINK)=linktest/%)
		@make cleantest

titletest/%:	$(OPT)
		@echo ==== $(@F) ====

evaltest/%:		$(OPT)
		@echo -n '$(@F).$(EXT)> '
		@ ./$(NAME) -r $(shell grep "@FLAGS" $(TESTDIR)/$(@F).$(EXT) | sed 's/.*@FLAGS//g') $(TESTDIR)/$(@F).$(EXT)

debugtest/%:	$(UNOPT)
		@echo -n '$(@F).$(EXT)> '
		@ ./$(NAME) -r $(shell grep "@FLAGS" $(TESTDIR)/$(@F).$(EXT) | sed 's/.*@FLAGS//g') $(TESTDIR)/$(@F).$(EXT)

runtimetest:	$(OPT) titletest/Test-runtime
		@./$(NAME) -v -g $(TESTDIR)/$(RUNTIME).wasm -g $(TESTDIR)/$(RUNTIME).wat
		@make cleantest

wasmtest/%:		$(OPT)
	  @ if ! grep -q "@FAIL-WASM" $(TESTDIR)/$(@F).$(EXT); \
		  then \
		    /bin/echo -n '$(@F).$(EXT)> '; \
		    ./$(NAME) -r -c -v $(shell grep "@FLAGS" $(TESTDIR)/$(@F).$(EXT) | sed 's/.*@FLAGS//g') $(TESTDIR)/$(@F).$(EXT); \
		  else echo '**' Skipping $(@F).$(EXT); \
		fi

wasmntest/%:	$(OPT)
	  @ if ! grep -q "@FAIL-WASM" $(TESTDIR)/$(@F).$(EXT); \
		  then \
		    /bin/echo -n '$(@F).$(EXT)> '; \
		    ./$(NAME) -r -c -v -n $(shell grep "@FLAGS" $(TESTDIR)/$(@F).$(EXT) | sed 's/.*@FLAGS//g') $(TESTDIR)/$(@F).$(EXT); \
		  else echo '**' Skipping $(@F).$(EXT); \
		fi

nodetest/%:		$(OPT)
		@ if ! grep -q "@FAIL-WASM\|@FAIL-V8" $(TESTDIR)/$(@F).$(EXT); \
		  then \
		    echo $(@F).$(EXT); \
		    ./$(NAME) -c -v $(shell grep "@FLAGS" $(TESTDIR)/$(@F).$(EXT) | sed 's/.*@FLAGS//g') $(TESTDIR)/$(@F).$(EXT); \
		    $(NODE) js/$(NAME).js $(TESTDIR)/$(@F); \
		  else echo '**' Skipping $(@F).$(EXT); \
		fi

linktest/%:		$(WASMDIR)/wasm $(WASMLINK) $(RUNTIME).wasm
		@ if ! grep -q "@FAIL-LINK" $(TESTDIR)/$(@F).$(WASMLINK); \
		  then \
		    echo $(@F).$(WASMLINK); \
		    for file in $$(cat $(TESTDIR)/$(@F).$(WASMLINK)); \
		    do \
		      ./$(NAME) -c -v $$file.$(EXT); \
		    done; \
		    $(WASMLINKDIR)/$(WASMLINK) -v $(RUNTIME).wasm $$(cat $(TESTDIR)/$(@F).$(WASMLINK) | sed s/$$/.wasm/g) -o $(TESTDIR)/$(@F).wasm; \
		    $(WASMDIR)/wasm $(TESTDIR)/$(@F).wasm; \
		  else echo '**' Skipping $(@F).$(WASMLINK); \
		fi; \
		# $(NODE) js/$(NAME).js $(TESTDIR)/$(@F)

$(RUNTIME).wasm:	$(OPT)
		@./$(NAME) -g $@


# Miscellaneous targets

.PHONY:		clean

clean: cleantest
		rm -rf $(WASMDIR) $(RUNTIME).wasm _tags
		$(OCB) -clean

cleantest:
		rm -f test/*.wasm test/*.wat
