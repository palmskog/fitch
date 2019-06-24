Fitch
=====

A certified proof checker for Fitch-style propositional logic proofs as defined in the book [Logic for Computer Science](http://www.cambridge.org/gb/academic/subjects/computer-science/programming-languages-and-applied-logic/logic-computer-science-modelling-and-reasoning-about-systems-2nd-edition) by Huth and Ryan.

Requirements
------------

Definitions and proofs:

- [`Coq 8.9`](https://coq.inria.fr)
- [`Mathematical Components 1.7.0`](http://math-comp.github.io/math-comp/) (`ssreflect`)
- [`Ott`](https://github.com/ott-lang/ott) (and its Coq library)

Executable checker:

- [`OCaml 4.02.3`](https://ocaml.org) (or later)
- [`camlp4`](https://ocaml.org)
- [`OCamlbuild`](https://github.com/ocaml/ocamlbuild)
- [`ocamlfind`](https://ocaml.org)

Building
--------

Make sure the `ott` program is in the `PATH`, and Ott's Coq auxiliary library has been installed under Coq's `user-contrib` directory (default) or set the `Ott_PATH` environment variable to an alternative location. One easy way to install Ott and its Coq library is via [OPAM](http://opam.ocaml.org/doc/Install.html):
```
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
opam install ott coq-ott
```

Then, run `./configure`, followed by `make`. This will compile the Coq syntax and relation definitions along with the proofs and functions, and extract OCaml code.

To build an executable checker program, run `make checker`. Example proofs (`.nd` files) can then be checked as follows:

    $ ./checker.native examples/imp.nd

To generate an OCaml program with the alternative Prolog file format parser, run `make prolog` in the root directory. Example proofs (`.pl` files) can then be checked as follows:

    $ ./prolog.native examples/imp_perm.pl

To generate a document (`fitch.pdf`) describing the proof system and proofs, run `make fitch.pdf` (requires LaTeX).
