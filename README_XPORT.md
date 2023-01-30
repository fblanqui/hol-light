Export to Dedukti and Lambdapi proof formats
============================================

The branch dk of this fork of HOL-Light provides functions for
exporting HOL-Light proofs in the
[Dedukti](https://github.com/Deducteam/Dedukti/) and
[Lambdapi](https://github.com/Deducteam/lambdapi) proof formats.

Dedukti is a proof format based on the λΠ-calculus modulo rewriting
(λ-calculus + simple types + dependent types + implicit type
equivalence modulo user-defined rewriting rules).

Lambdapi is a proof assistant based on the λΠ-calculus modulo
rewriting that can read and generate Dedukti proofs.

Requirements
------------

- ocaml 4.02.3
- camlp5 6.17
- dedukti 2.7
- lambdapi 2.3
- ledit 2.03 (optional, to ease the use of ocaml toplevel)

Usage
-----

Run the OCaml toplevel:
```
ocaml -I `camlp5 -where` camlp5o.cma
```

If you want to use ledit, write:
```
ledit -x -h ~/.ocaml_history ocaml -I `camlp5 -where` camlp5o.cma
```

You can add an alias in your `~/.bashrc` to save time.

Inside the OCaml toplevel, write:
```
#use "xprelude.ml";;
#use "hol.ml";; (* or part of it *)
(* load any other HOL-Light file here *)
#use "xlib.ml";;
update_map_const_type_vars_pos();;
```

To export to Dedukti:
```
#use "xdk.ml";;
export_to_dk "myfile.dk" All;;
```

To export to Lambdapi:
```
#use "xlp.ml";;
export_to_lp "myfile.lp" All;;
```

To get the list of HOL-Light files and named theorems:
```
#use "xnames.ml";;
files;;
update_map_file_thms();;
!map_file_thms;;
update_map_thm_id_name();;
!map_thm_id_name;;
```

Experiments:
------------

On `hol.ml` until `arith.ml` (by commenting from `loads "wf.ml"` to the end):
- generation time for dk: 1m50s, 395 Mo
- checking time with dk check: 1m10s 
- generation time for lp: 1m13s, 216 Mo
- checking time with lambdapi: 1m42s

Implementation
--------------

For extracting proofs out of HOL-Light, the implementation reuses
parts of
[ProofTrace](https://github.com/fblanqui/hol-light/tree/master/ProofTrace)
developed by Stanislas Polu in 2019.

Modified HOL-Light files:
- `fusion.ml`: file defining the theorem and proof types

Added files:
- `xprelude.ml`: provides a few global references
- `xlib.ml`: functions on types and terms
- `xnames.ml`: compute the list of HOL-Light files and a map associating the list of theorems proved in each file (following ProofTrace/proofs.ml)
- `xdk.ml`: function exporting HOL-Light proofs to Dedukti
- `xlp.ml`: function exporting HOL-Light proofs to Lambdapi
