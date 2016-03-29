Fitch
=====

Certified proof checker for Fitch-style propositional logic proofs

Requirements:

 - [`Coq 8.5`](https://coq.inria.fr/download)
 - [`Mathematical Components 1.6`](http://math-comp.github.io/math-comp/)
 - [`Ott 0.25`](https://www.cl.cam.ac.uk/~pes20/ott/)

Run `make` in the root directory. This will compile generate the Coq syntax and relation definitions, compile them along with the proofs, extract an OCaml program and link it with the default parser. Example proofs (`.nd` files) can then be checked as follows:

    $ fitch examples/imp.nd

To generate an OCaml program with the alternative Prolog file format parser, run `make fitch.prolog` in the root directory. Example proofs (`.pl` files) can then be checked as follows:

    $ fitch.prolog examples/imp_perm.pl
