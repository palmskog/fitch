Fitch
=====

Certified proof checker for Fitch-style propositional logic proofs as defined in the book Logic for Computer Science by Huth and Ryan

Requirements:

- [`OCaml 4.02.3`](https://ocaml.org) (or later)
- [`camlp4`](https://ocaml.org)
- [`OCamlbuild`](https://ocaml.org)
- [`ocamlfind`](https://ocaml.org)
- [`Coq 8.5`](https://coq.inria.fr/coq-85) or [`Coq 8.6`](https://coq.inria.fr/coq-86)
- [`Mathematical Components 1.6`](http://math-comp.github.io/math-comp/)
- [`Ott`](https://www.cl.cam.ac.uk/~pes20/ott/)

Make sure Ott's Coq auxiliary libraries have been installed in Coq' `user-contrib` (default) or set the `Ott_PATH` parameter in `configure` appropriately. Then run `./configure`, followed by `make`. This will compile the Coq syntax and relation definitions, compile them along with the proofs, extract an OCaml program, and link the program with the default parser. Example proofs (`.nd` files) can then be checked as follows:

    $ ./checker.native examples/imp.nd

To generate an OCaml program with the alternative Prolog file format parser, run `make fitch.prolog` in the root directory. Example proofs (`.pl` files) can then be checked as follows:

    $ ./prolog.native examples/imp_perm.pl

To generate a document (`fitch.pdf`) describing the proof system and proofs, run `make fitch.pdf` (requires LaTeX).
