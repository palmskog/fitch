Fitch
=====

A certified proof checker for Fitch-style propositional logic proofs as defined in the book [Logic for Computer Science](http://www.cambridge.org/gb/academic/subjects/computer-science/programming-languages-and-applied-logic/logic-computer-science-modelling-and-reasoning-about-systems-2nd-edition) by Huth and Ryan.

Requirements
------------

Coq definitions and proofs:

- [Coq](https://coq.inria.fr) (8.16 or later)
- [Coq Ott library](https://github.com/ott-lang/ott) (0.33 or later)

HOL4 definitions and proofs:

- [`HOL4 Kananaskis-13`](https://hol-theorem-prover.org)

Executable OCaml checkers:

- [`OCaml 4.05`](https://ocaml.org) (or later)
- [`menhir`](http://gallium.inria.fr/~fpottier/menhir/)
- [`OCamlbuild`](https://github.com/ocaml/ocamlbuild)
- [`ocamlfind`](https://ocaml.org)

Executable CakeML checker:

- [`HOL4 Kananaskis-13`](https://hol-theorem-prover.org)
- [`CakeML 1009`](https://github.com/CakeML/cakeml/releases/tag/v1009)

Building Coq definitions and proofs
-----------------------------------

Make sure Ott's Coq auxiliary library has been installed in Coq's `user-contrib` library directory. One easy way to install Ott and its Coq library is via [opam](http://opam.ocaml.org/doc/Install.html):
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-ott
```
Then, run `make`. This will compile the Coq syntax and relational definitions and check all proofs.

Building HOL4 definitions and proofs
------------------------------------

Run `make hol`. This will compile the HOL4 syntax and relational definitions and check all proofs.

Building the OCaml checkers
---------------------------

To build the default executable checker program, run `make checker`. Example proofs (`.nd` files) can then be checked as follows:

    $ ./checker.native examples/imp.nd

To generate an OCaml program with the alternative Prolog file format parser, run `make prolog` in the root directory. Example proofs (`.pl` files) can then be checked as follows:

    $ ./prolog.native examples/imp_perm.pl

Building the CakeML checker
--------------------------

A verified executable checker in [CakeML](https://cakeml.org) can be obtained using the CakeML proof-producing synthesis tool ("compiler frontend 1"). To generate it, go to the `cakeml` directory and adjust the `CAKEMLDIR` variable in the `Holmake` file to point to the directory with CakeML release 1009. Then, run `Holmake`.

For convenience, a pretty-printed [version](https://gist.github.com/palmskog/a988783a000ae6319eed15819eeb60ac) of the verified CakeML code is available; note that the pretty-printing itself has not been verified. Moreover, there is currently no parser for for the surface syntax.

Documentation
-------------

To generate a document (`fitch.pdf`) describing the proof system and proofs, run `make fitch.pdf` (requires LaTeX and Ott).
