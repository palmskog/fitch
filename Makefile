OCAMLBUILD = ocamlbuild -use-menhir -tag safe_string -cflag -g -I ocaml

include Makefile.ml-files

default: Makefile.coq
	$(MAKE) -f Makefile.coq

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

checker: checker.native

prolog: prolog.native

checker.native: $(FITCHML) ocaml/util.ml ocaml/checker.ml
	$(OCAMLBUILD) checker.native

prolog.native: $(FITCHML) ocaml/util.ml ocaml/prolog.ml
	$(OCAMLBUILD) prolog.native

Makefile.coq:
	coq_makefile -f _CoqProject -o Makefile.coq

hol/fitchScript.sml: ott/fitch.ott
	cd hol && ott -o fitchScript.sml ../ott/fitch.ott

hol: hol/fitchMetaScript.sml hol/fitchScript.sml hol/ottScript.sml hol/ottLib.sig hol/ottLib.sml
	Holmake -I hol

$(FITCHML): Makefile.coq
	$(MAKE) -f Makefile.coq $@

doc/fitch_defs.tex: ott/fitch.ott
	ott -o $@ -tex_wrap false $<

doc/fitch.tex: doc/fitch.mng ott/fitch.ott
	ott -tex_filter doc/fitch.mng doc/fitch.tex ott/fitch.ott

fitch.pdf: doc/fitch_defs.tex doc/fitch.tex
	pdflatex doc/fitch.tex
	pdflatex doc/fitch.tex

clean: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall
	$(OCAMLBUILD) -clean
	Holmake clean
	rm -f Makefile.coq Makefile.coq.conf
	rm -f hol/fitchScript.sml
	rm -f doc/fitch_defs.tex doc/fitch.tex

.PHONY: default clean checker prolog hol $(FITCHML)
.NOTPARALLEL: $(FITCHML)
