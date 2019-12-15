Fitch
=====

A certified proof checker for Fitch-style propositional logic proofs as defined in the book [Logic for Computer Science](http://www.cambridge.org/gb/academic/subjects/computer-science/programming-languages-and-applied-logic/logic-computer-science-modelling-and-reasoning-about-systems-2nd-edition) by Huth and Ryan.

Requirements
------------

Coq definitions and proofs:

- [`Coq 8.9`](https://coq.inria.fr) (or later)
- [`Ott 0.30`](https://github.com/ott-lang/ott) (and its auxiliary Coq library)

HOL4 definitions and proofs:

- [`HOL4 Kananaskis-13`](https://hol-theorem-prover.org)
- [`Ott 0.30`](https://github.com/ott-lang/ott)

Executable OCaml checkers:

- [`OCaml 4.02.3`](https://ocaml.org) (or later)
- [`menhir`](http://gallium.inria.fr/~fpottier/menhir/)
- [`OCamlbuild`](https://github.com/ocaml/ocamlbuild)
- [`ocamlfind`](https://ocaml.org)

Building Coq definitions and proofs
-----------------------------------

Make sure the `ott` program is in the `PATH`, and Ott's Coq auxiliary library has been installed in Coq's `user-contrib` library directory. One easy way to install Ott and its Coq library is via [OPAM](http://opam.ocaml.org/doc/Install.html):
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install ott coq-ott
```
Then, run `make`. This will compile the Coq syntax and relational definitions and check all proofs.

Building HOL4 definitions and proofs
------------------------------------

Make sure the `ott` program is in the `PATH`. Then, run `make hol`. This will compile the HOL4 syntax and relational definitions and check all proofs.

Building the OCaml checkers
---------------------------

To build the default executable checker program, run `make checker`. Example proofs (`.nd` files) can then be checked as follows:

    $ ./checker.native examples/imp.nd

To generate an OCaml program with the alternative Prolog file format parser, run `make prolog` in the root directory. Example proofs (`.pl` files) can then be checked as follows:

    $ ./prolog.native examples/imp_perm.pl

Documentation
-------------

To generate a document (`fitch.pdf`) describing the proof system and proofs, run `make fitch.pdf` (requires LaTeX).
