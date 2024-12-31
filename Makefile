# Steel's `Makefile`s rely on recent GNU Make's "shortest stem" rule,
# so we need to rule out older `make`s.

ifeq (3.81,$(MAKE_VERSION))
  $(error You seem to be using the OSX antiquated Make version. Hint: brew \
    install make, then invoke gmake instead of make)
endif

# Define the Steel root directory. We need to fix it to use the Windows path convention on Windows+Cygwin.
export STEEL_HOME := $(CURDIR)

include $(STEEL_HOME)/mk/locate_fstar.mk

all: lib verify

.PHONY: .force
.force:

plugin: plugin.src
	cd src/ocaml && $(FSTAR_EXE) --ocamlenv dune build
	cd src/ocaml && dune install --prefix=$(STEEL_HOME)

plugin.src: .force
	@# NOTE: I would have preferred to separate the cache dir
	@# into something like build/plugin.checked, but this
	@# means every client now has to point there too, and we have
	@# to install that directory. So I'm just placing them in lib/steel
	@# as the Makefile there does. This should be fine really.
	$(MAKE) -f mk/plugin.mk \
	  CACHE_DIR=lib/steel \
	  OUTPUT_DIR=build/plugin.ml \
	  CODEGEN=Plugin \
	  SRC=lib/steel \
	  TAG=plugin \
	  EXTRACT="--extract '+Steel.Effect.Common +Steel.ST.GenElim.Base +Steel.ST.GenElim1.Base'" \
	  ROOTS="Steel.Effect.Common.fst Steel.ST.GenElim.Base.fst Steel.ST.GenElim1.Base.fst"

.PHONY: lib
lib:
	+$(MAKE) -C src/c

.PHONY: verify-steel
verify-steel: plugin
	+$(MAKE) -C lib/steel steel

.PHONY: verify-steelc
verify-steelc: verify-steel
	+$(MAKE) -C lib/steel/c steelc

.PHONY: verify
verify: verify-steel verify-steelc

clean: clean_ocaml
	+$(MAKE) -C lib/steel clean ; true
	rm -rf build/plugin.checked
	rm -rf build/plugin.ml

clean_ocaml:
	cd src/ocaml && { dune uninstall --prefix=$(STEEL_HOME) ; dune clean ; true ; }

.PHONY: test
test: all
	+$(MAKE) -C share/steel

PREFIX ?= /usr/local
override PREFIX:=$(abspath $(PREFIX))
ifeq ($(OS),Windows_NT)
  STEEL_INSTALL_PREFIX=$(shell cygpath -m $(PREFIX))
else
  STEEL_INSTALL_PREFIX=$(PREFIX)
endif
export STEEL_INSTALL_PREFIX

INSTALL := $(shell ginstall --version 2>/dev/null | cut -c -8 | head -n 1)
ifdef INSTALL
   INSTALL := ginstall
else
   INSTALL := install
endif
export INSTALL

.PHONY: install install-ocaml install-lib install-include install-share

install-ocaml:
	cd src/ocaml && dune install --prefix=$(STEEL_INSTALL_PREFIX)

install-src-c:
	+$(MAKE) -C src/c install

install-lib:
	+$(MAKE) -C lib/steel install

install-include:
	+$(MAKE) -C include/steel install

install-share:
	+$(MAKE) -C share/steel install

install: install-ocaml install-lib install-include install-share install-src-c

.PHONY: ci
ci:
	+$(MAKE) all
	+$(MAKE) test
