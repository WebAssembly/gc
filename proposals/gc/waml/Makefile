# This Makefile uses ocamlbuild but does not rely on ocamlfind or the Opam
# package manager to build.
#
# See README.me for instructions.


# Configuration

NAME =		waml
EXT =			$(NAME)
RUNTIME =	$(NAME)-runtime

WASMBASE =	$(PWD)/../../../interpreter
WASMDIRS =	util syntax binary script text valid runtime exec host main unittest jslib
WASMFILES = Makefile dune dune-project $(shell cd $(WASMBASE); ls $(foreach DIR,$(WASMDIRS),$(DIR)/*))

WASMDIR =		_wasm
WASMDEPS =	$(WASMFILES:%=$(WASMDIR)/%)
WASMTESTDIR =	$(WASMBASE)/../test/corel


WASMLINK =	wln
WASMLINKDIR =	$(PWD)/../$(WASMLINK)

NODE =		node --experimental-wasm-gc

BUILDDIR =	_build/default


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

$(WASMDIR)/wasm:	$(WASMDEPS)
		@echo ==== Building Wasm ====
		make -C $(WASMDIR) TESTDIR=$(WASMTESTDIR)
		@echo ==== Done building Wasm ====


# Building linker

.PHONY:	$(WASMLINK)

$(WASMLINK):
		make -C $(WASMLINKDIR)


# Building executable

.PHONY:                $(NAME)

$(NAME):
	@rm -f $@
	dune build $@.exe
	ln $(BUILDDIR)/$@.exe $@


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

titletest/%:	$(NAME)
		@echo ==== $(@F) ====

evaltest/%:		$(NAME)
		@echo -n '$(@F).$(EXT)> '
		@ ./$(NAME) -r $(shell grep "@FLAGS" $(TESTDIR)/$(@F).$(EXT) | sed 's/.*@FLAGS//g') $(TESTDIR)/$(@F).$(EXT)

runtimetest:	$(NAME) titletest/Test-runtime
		@./$(NAME) -v -g $(TESTDIR)/$(RUNTIME).wasm -g $(TESTDIR)/$(RUNTIME).wat
		@make cleantest

wasmgen/%:		$(NAME)
	    /bin/echo -n '$(@F).$(EXT)> '; \
	    ./$(NAME) -c $(shell grep "@FLAGS" $(TESTDIR)/$(@F).$(EXT) | sed 's/.*@FLAGS//g') $(TESTDIR)/$(@F).$(EXT); \
	    $(WASMBASE)/wasm -d -u $(TESTDIR)/$(@F).wasm -o $(TESTDIR)/$(@F).wast; \
	    rm $(TESTDIR)/$(@F).wasm; \
	    $(WASMBASE)/wasm -d $(TESTDIR)/$(@F).wast; \

wasmtest/%:		$(NAME)
	  @ if ! grep -q "@FAIL-WASM" $(TESTDIR)/$(@F).$(EXT); \
		  then \
		    /bin/echo -n '$(@F).$(EXT)> '; \
		    ./$(NAME) -r -c -v $(shell grep "@FLAGS" $(TESTDIR)/$(@F).$(EXT) | sed 's/.*@FLAGS//g') $(TESTDIR)/$(@F).$(EXT); \
		  else echo '**' Skipping $(@F).$(EXT); \
		fi

wasmntest/%:	$(NAME)
	  @ if ! grep -q "@FAIL-WASM" $(TESTDIR)/$(@F).$(EXT); \
		  then \
		    /bin/echo -n '$(@F).$(EXT)> '; \
		    ./$(NAME) -r -c -v -n $(shell grep "@FLAGS" $(TESTDIR)/$(@F).$(EXT) | sed 's/.*@FLAGS//g') $(TESTDIR)/$(@F).$(EXT); \
		  else echo '**' Skipping $(@F).$(EXT); \
		fi

nodetest/%:		$(NAME)
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

$(RUNTIME).wasm:	$(NAME)
		@./$(NAME) -g $@


# Miscellaneous targets

.PHONY:		clean

clean: cleantest
		rm -rf $(WASMDIR) $(RUNTIME).wasm _tags
		dune clean

cleantest:
		rm -f test/*.wasm test/*.wat
