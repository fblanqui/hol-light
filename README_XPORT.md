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

- ocaml 4.02.3 and camlp5 6.17
or ocaml 4.14.1 and camlp5.8.00.03
- dedukti 2.7
- lambdapi 2.3
- ledit (optional, to ease the use of ocaml toplevel)

Installation
------------

Get the sources of hol-light:
```
git clone https://github.com/jrh13/hol-light.git
```

In the following, we assume that we are in the `hol-light` directory
created by the previous `git clone` command:
```
cd hol-light
```

To setup hol-light, do the first time you clone hol-light, or if you
change the version of ocaml or the version of camlp5:

```
make
```

Get the sources of the dk branch:
```
git remote add deducteam https://github.com/Deducteam/hol-light.git
fetch deducteam
git checkout deducteam/dk
```

Usage
-----

Run the OCaml toplevel:
```
ocaml
```

If you want to use ledit, write:
```
ledit -x -h ~/.ocaml_history ocaml
```

You can add an alias in your `~/.bashrc` to save time.

In the OCaml toplevel, write:
```
#use "xprelude.ml";;
#use "hol.ml";;
(* load any other HOL-Light file here *)
#use "xlib.ml";;
update_map_const_type_vars_pos();;
```

To export to Dedukti, write then:
```
#use "xdk.ml";;
export_to_dk "myfile.dk" All;;
```

To export to Lambdapi, write thn:
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

Checking the generated dk/lp files:
-----------------------------------

In case hol-light and dkcheck/lambdapi do not use the same ocaml
versions, it is convenient to put generated files in a subdirectory
and tell opam to use different switches in each directory:

Xterm 1 (for HOL-Light):
```
cd $hol_light_directory
opam switch link 4.02.3
eval `opam env`
```

Xterm 2 (for checking dk/lp files):
```
cd $hol_light_directory
mkdir xport
cd xport
opam switch link 4.14.1
eval `opam env`
```

To check the generated dk file, write in Xterm2:
```
dk check myfile.dk
```

To check the generated lp file, write in Xterm2:
```
lambdapi check --map-dir hol-light:. myfile.lp
```

or create a file `lambdapi.pkg`:
```
package_name = hol-light
root_path = hol-light
```

and simply write in a shell:

```
lambdapi check myfile.lp
```

Experiments:
------------

On `hol.ml` until `arith.ml` (by commenting from `loads "wf.ml"` to the end):
- generation time for dk: 1m52s, 395 Mo
- checking time with dk check: 1m12s 
- generation time for lp: 1m08s, 217 Mo
- checking time with lambdapi: 5m46s

Implementation
--------------

For extracting proofs out of HOL-Light, the implementation reuses
parts of
[ProofTrace](https://github.com/fblanqui/hol-light/tree/master/ProofTrace)
developed by Stanislas Polu in 2019.

Modified HOL-Light files:
- `fusion.ml`: file defining the theorem and proof types

Added files:
- `xprelude.ml`: load the necessary modules and provides a few global references
- `xlib.ml`: functions on types and terms
- `xnames.ml`: compute the list of HOL-Light files and a map associating the list of theorems proved in each file (following ProofTrace/proofs.ml)
- `xdk.ml`: function exporting HOL-Light proofs to Dedukti
- `xlp.ml`: function exporting HOL-Light proofs to Lambdapi
