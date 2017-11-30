include Makefile.detect-coq-version

ifeq (,$(filter $(COQVERSION),8.6 8.7 trunk))
$(error "only compatible with Coq version 8.6 or later")
endif

COQPROJECT_EXISTS = $(wildcard _CoqProject)
ifeq "$(COQPROJECT_EXISTS)" ""
$(error "Run ./configure before running make")
endif

OCAMLBUILD = ocamlbuild -use-ocamlfind -tag safe_string -syntax camlp4o -pkgs 'camlp4.lib camlp4.extend' -cflag -g
OTT = ott
PDFLATEX = pdflatex

OTTFILES = fitch.ott
VFILES = $(OTTFILES:.ott=.v)
MLFILES = fitch.ml fitch.mli

default: checker.native

checker.native: $(MLFILES) util.ml checker.ml
	$(OCAMLBUILD) checker.native

prolog.native: $(MLFILES) util.ml prolog.ml
	$(OCAMLBUILD) prolog.native

Makefile.coq: $(VFILES)
	coq_makefile -f _CoqProject -o Makefile.coq -install none \
          -extra '$(MLFILES)' \
	    'fitch_program_extrocaml.v fitch_program.vo' \
	    '$$(COQC) $$(COQDEBUG) $$(COQFLAGS) fitch_program_extrocaml.v'

$(VFILES): %.v: %.ott
	$(OTT) -o $@ -coq_expand_list_types false $<

fitchScript.sml: fitch.ott
	$(OTT) -o fitchScript.sml fitch.ott

$(MLFILES): Makefile.coq
	$(MAKE) -f Makefile.coq $@

fitch_defs.tex: fitch.ott
	$(OTT) -o fitch_defs.tex -tex_wrap false fitch.ott

fitch.tex: fitch.mng fitch.ott
	$(OTT) -tex_filter fitch.mng fitch.tex fitch.ott

fitch.pdf: fitch_defs.tex fitch.tex
	$(PDFLATEX) fitch.tex
	$(PDFLATEX) fitch.tex

clean:
	if [ -f Makefile.coq ]; then \
	  $(MAKE) -f Makefile.coq cleanall; fi
	rm -f Makefile.coq $(VFILES)
	$(OCAMLBUILD) -clean

.PHONY: default clean
.NOTPARALLEL: $(MLFILES)
