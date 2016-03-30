default: fitch

fitch: fitch.ml fitch.mli explode.ml parser.ml
	ocamlfind ocamlc -w x \
		-linkpkg -syntax camlp4o \
		-package camlp4.extend -package camlp4.lib \
		fitch.mli fitch.ml explode.ml parser.ml -o fitch

fitch.prolog: fitch.ml fitch.mli explode.ml prolog.ml
	ocamlfind ocamlc -w x \
		-linkpkg -syntax camlp4o \
		-package camlp4.extend -package camlp4.lib \
		fitch.mli fitch.ml explode.ml prolog.ml -o fitch.prolog

fitch.ml: fitch.v Makefile.coq
	$(MAKE) -f Makefile.coq

fitch.v: fitch.ott
	ott -o fitch.v -coq_expand_list_types false fitch.ott

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

fitch_defs.tex: fitch.ott
	ott -o fitch_defs.tex -tex_wrap false fitch.ott

fitch.tex: fitch.mng fitch.ott
	ott -tex_filter fitch.mng fitch.tex fitch.ott

fitch.pdf: fitch_defs.tex fitch.tex
	pdflatex fitch.tex
	pdflatex fitch.tex

clean:
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq fitch.ml fitch.mli fitch fitch.prolog *.cmi *.cmo fitch.pdf fitch.log fitch.tex fitch_defs.tex fitch.aux fitch_defs.aux

.PHONY: default clean
