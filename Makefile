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

hol: hol/fitchScript.sml
	Holmake -r -I hol

cakeml: hol/fitchScript.sml
	Holmake -r -I cakeml

$(FITCHML): Makefile.coq
	$(MAKE) -f Makefile.coq $@

doc/fitch_defs.tex: ott/fitch.ott
	ott -o $@ -tex_wrap false $<

doc/fitch_listing.tex: ott/fitch.ott
	ott -o $@ $<

fitch_listing.pdf: doc/fitch_listing.tex
	pdflatex doc/fitch_listing.tex
	pdflatex doc/fitch_listing.tex

doc/fitch.tex: doc/fitch.mng ott/fitch.ott
	ott -tex_filter doc/fitch.mng doc/fitch.tex ott/fitch.ott

fitch.pdf: doc/fitch_defs.tex doc/fitch.tex
	pdflatex doc/fitch.tex
	pdflatex doc/fitch.tex

clean: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall
	$(OCAMLBUILD) -clean
	rm -f Makefile.coq Makefile.coq.conf
	rm -f doc/fitch_defs.tex doc/fitch.tex
	cd hol && Holmake clean

.PHONY: default clean checker prolog hol cakeml $(FITCHML)
.NOTPARALLEL: $(FITCHML)
