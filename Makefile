COQVERSION = $(shell coqc --version|grep "version 8.5")
ifeq "$(COQVERSION)" ""
$(error "fitch is only compatible with Coq version 8.5")
endif

COQPROJECT_EXISTS = $(wildcard _CoqProject)
ifeq "$(COQPROJECT_EXISTS)" ""
$(error "Run ./configure before running make")
endif

OCAMLBUILD = ocamlbuild -use-ocamlfind -syntax camlp4o -package camlp4.lib -package camlp4.extend -cflag -g
OTT = ott
OTTFILES = fitch.ott
VFILES = $(OTTFILES:.ott=.v)
MLFILES = fitch.ml fitch.mli
MLFILES_DEPS = 'fitch_program_extrocaml.v fitch_program.vo'
MLFILES_COMMAND = '$$(COQC) $$(COQDEBUG) $$(COQFLAGS) fitch_program_extrocaml.v'

default: checker.native

checker.native: $(MLFILES) explode.ml checker.ml
	$(OCAMLBUILD) checker.native

prolog.native: $(MLFILES) explode.ml prolog.ml
	$(OCAMLBUILD) prolog.native

Makefile.coq: $(VFILES)
	coq_makefile -f _CoqProject -o Makefile.coq \
          -extra 'fitch.ml' $(MLFILES_DEPS) $(MLFILES_COMMAND) \
          -extra 'fitch.mli' $(MLFILES_DEPS) $(MLFILES_COMMAND)

$(VFILES): %.v: %.ott
	$(OTT) -o $@ -coq_expand_list_types false $<

$(MLFILES): Makefile.coq
	$(MAKE) -f Makefile.coq $@

fitch_defs.tex: fitch.ott
	ott -o fitch_defs.tex -tex_wrap false fitch.ott

fitch.tex: fitch.mng fitch.ott
	ott -tex_filter fitch.mng fitch.tex fitch.ott

fitch.pdf: fitch_defs.tex fitch.tex
	pdflatex fitch.tex
	pdflatex fitch.tex

clean:
	if [ -f Makefile.coq ]; then \
	  $(MAKE) -f Makefile.coq cleanall; fi
	rm -f Makefile.coq $(VFILES)
	$(OCAMLBUILD) checker.native -clean
	$(OCAMLBUILD) prolog.native -clean

.PHONY: default clean
