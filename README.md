Fitch
=====

Certified proof checker for Fitch-style propositional logic proofs as defined in the book _Logic for Computer Science_ by Huth and Ryan.

Requirements
------------

Definitions and proofs:

- [`Coq 8.6.1`](https://coq.inria.fr/coq-86) or [`Coq 8.7`](https://coq.inria.fr/coq-87)
- [`Mathematical Components 1.6.4`](http://math-comp.github.io/math-comp/) (`ssreflect`)
- [`Ott 0.27`](https://github.com/ott-lang/ott) (and its Coq library)

Executable checker:

- [`OCaml 4.02.3`](https://ocaml.org) (or later)
- [`camlp4`](https://ocaml.org)
- [`OCamlbuild`](https://github.com/ocaml/ocamlbuild)
- [`ocamlfind`](https://ocaml.org)

Building
--------

Make sure Ott's Coq auxiliary libraries have been installed under Coq's `user-contrib` directory (default) or set the `Ott_PATH` environment variable to an alternative location. Then run `./configure`, followed by `make`. This will compile the Coq syntax and relation definitions along with the proofs and functions, and extract OCaml code.

To build an executable checker program, run `make checker`. Example proofs (`.nd` files) can then be checked as follows:

    $ ./checker.native examples/imp.nd

To generate an OCaml program with the alternative Prolog file format parser, run `make prolog` in the root directory. Example proofs (`.pl` files) can then be checked as follows:

    $ ./prolog.native examples/imp_perm.pl

To generate a document (`fitch.pdf`) describing the proof system and proofs, run `make fitch.pdf` (requires LaTeX).
