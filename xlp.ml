(****************************************************************************)
(* Export HOL-Light proofs to Lambdapi. *)
(****************************************************************************)

unset_jrh_lexer;;

(****************************************************************************)
(* Translation of types and terms. *)
(****************************************************************************)

let name oc n =
  out oc "%s"
    (match n with
     | "," -> "̦‚" (* low single comma quotation mark
                     https://unicode-table.com/en/201A/ *)
     | "@" -> "ε" (* Hilbert choice operator *)
     | "\\/" -> "∨"
     | "/\\" -> "∧"
     | "==>" -> "⇒"
     | "!" -> "∀"
     | "?" -> "∃"
     | "?!" -> "∃!"
     | "~" -> "¬"
     | _ -> n);;

let rec typ oc b =
  match b with
  | Tyvar n -> out oc "%a" name n
  | Tyapp(c,[]) -> out oc "%a" name c
  | Tyapp(c,bs) -> out oc "(%a%a)" name c (list_prefix " " typ) bs
;;

let raw_var oc t =
  match t with
  | Var(n,_) -> out oc "%a" name n
  | _ -> assert false
;;

let var rmap oc t =
  try name oc (List.assoc t rmap)
  with Not_found ->
    match t with
    | Var(n,_) -> out oc "%a /*not found*/" name n
    | _ -> assert false
;;

let decl_var rmap oc t =
  match t with
  | Var(_,b) -> out oc "%a : El %a" (var rmap) t typ b
  | _ -> assert false
;;

let decl_param rmap oc v = out oc " (%a)" (decl_var rmap) v;;

(* [term rmap oc t] prints on [oc] the term [t] with term variable
   renaming map [rmap]. A variable of type b not in [rmap] is replaced
   by [el b]. *)
let rec term rmap oc t =
  match t with
  | Var(n,b) ->
     begin
       try name oc (List.assoc t rmap)
       with Not_found -> out oc "/*%a*/(el %a)" name n typ b
     end
  | Const(c,b) ->
     begin match List.map (subtype b) (const_type_vars_pos c) with
     | [] -> out oc "%a" name c
     | bs -> out oc "(@%a%a)" name c (list_prefix " " typ) bs
     end
  | Comb(_,_) -> (*out oc "(%a %a)" (term rmap) t1 (term rmap) t2*)
     let h, ts = head_args t in
     out oc "(%a%a)" (term rmap) h (list_prefix " " (term rmap)) ts
  | Abs(t,u) ->
     let rmap' = add_var rmap t in
     out oc "(λ %a, %a)" (decl_var rmap') t (term rmap') u
;;

let subst_type =
  list_sep "; " (fun oc (b,v) -> out oc "%a -> %a" typ v typ b);;

let subst_term rmap =
  list_sep "; "
    (fun oc (t,v) -> out oc "%a -> %a" raw_var v (term rmap) t);;

(****************************************************************************)
(* Proof translation. *)
(****************************************************************************)

(* In a theorem, the hypotheses [t1;..;tn] are given the names
   ["h1";..;"hn"]. *)

(* Printing on the output channel [oc] of the subproof [p2] given:
- tvs: list of type variables of the theorem
- rmap: renaming map for term variables
- ty_su: type substitution that needs to be applied
- tm_su: term substitution that needs to be applied
- ts1: hypotheses of the theorem *)
let subproof tvs rmap ty_su tm_su ts1 i2 oc p2 =
  let term = term rmap in
  let Proof(th2,_) = p2 in
  let ts2,t2 = dest_thm th2 in
  (* vs2 is the list of free term variables of th2 *)
  let vs2 = freesl (t2::ts2) in
  (* vs2 is now the application of tm_su on vs2 *)
  let vs2 = vsubstl tm_su vs2 in
  (* ts2 is now the application of tm_su on ts2 *)
  let ts2 = vsubstl tm_su ts2 in
  (* tvs2 are the lst of type variables of th2 *)
  let tvs2 = type_vars_in_thm th2 in
  (* bs2 is the application of ty_su on tvs2 *)
  let bs2 = List.map (type_subst ty_su) tvs2 in
  (* tvbs2 is the type variables of bs2 *)
  let tvbs2 = type_vars bs2 in
  (* we remove from tvbs2 the variables of tvs *)
  let tvbs2 =
    List.fold_left
      (fun tvbs2 tv -> if List.mem tv tvs then tvbs2 else tv::tvbs2)
      [] tvbs2
  in
  (* we extend ty_su by mapping every type variable of tvbs2 to bool *)
  let ty_su =
    List.fold_left
      (fun su tv -> (bool_ty,tv)::su)
      ty_su tvbs2
  in
  let hyp oc t = out oc "h%d" (try 1 + index t ts1 with _ -> 0) in
  match ty_su with
  | [] ->
     out oc "(thm_%d%a%a)" i2
       (list_prefix " " term) vs2 (list_prefix " " hyp) ts2
  | _ ->
     (* vs2 is now the application of ty_su on vs2 *)
     let vs2 = List.map (inst ty_su) vs2 in
     (* ts2 is now the application of ty_su on ts2 *)
     let ts2 = List.map (inst ty_su) ts2 in
     (* bs is the list of types obtained by applying ty_su on tvs2 *)
     let bs = List.map (type_subst ty_su) tvs2 in
     out oc "(@thm_%d%a%a%a)" i2 (list_prefix " " typ) bs
       (list_prefix " " term) vs2 (list_prefix " " hyp) ts2
;;

(* [proof tvs rmap oc p] prints on [oc] the proof [p] for a theorem
   with type variables [tvs] and free variables renaming map [rmap]. *)
let proof tvs rmap =
  let term = term rmap in
  let rec proof oc p =
    let Proof(thm,content) = p in
    let ts = hyp thm in
    let sub = subproof tvs rmap [] [] ts in
    match content with
    | Prefl(t) ->
       out oc "REFL %a" term t
    | Ptrans(k1,k2) ->
       let p1 = proof_at k1 and p2 = proof_at k2 in
       out oc "TRANS %a %a" (sub k1) p1 (sub k2) p2
    | Pmkcomb(k1,k2) ->
       let p1 = proof_at k1 and p2 = proof_at k2 in
       out oc "MK_COMB %a %a" (sub k1) p1 (sub k2) p2
    | Pabs(k,t) ->
       let rmap' = add_var rmap t in
       out oc "fun_ext (λ %a, %a)" (decl_var rmap') t
         (subproof tvs rmap' [] [] ts k) (proof_at k)
    | Pbeta(Comb(Abs(x,t),y)) when x = y ->
       out oc "REFL %a" term t
    | Pbeta(t) ->
       out oc "REFL %a" term t
    | Passume(t) ->
       out oc "h%d" (1 + index t (hyp thm))
    | Peqmp(k1,k2) ->
       let p1 = proof_at k1 and p2 = proof_at k2 in
       out oc "EQ_MP %a %a" (sub k1) p1 (sub k2) p2
    | Pdeduct(k1,k2) ->
       let p1 = proof_at k1 and p2 = proof_at k2 in
       let Proof(th1,_) = p1 and Proof(th2,_) = p2 in
       let t1 = concl th1 and t2 = concl th2 in
       let n = 1 + List.length ts in
       out oc "prop_ext (λ h%d : Prf %a, %a) (λ h%d : Prf %a, %a)"
         n term t1 (subproof tvs rmap [] [] (ts @ [t1]) k2) p2
         n term t2 (subproof tvs rmap [] [] (ts @ [t2]) k1) p1
    | Pinst(k,[]) -> proof oc (proof_at k)
    | Pinst(k,s) ->
       out oc "%a" (subproof tvs rmap [] s ts k) (proof_at k)
    | Pinstt(k,[]) -> proof oc (proof_at k)
    | Pinstt(k,s) ->
       out oc "%a" (subproof tvs rmap s [] ts k) (proof_at k)
    | Paxiom(t) ->
       out oc "axiom_%d%a"
         (pos_first (fun th -> concl th = t) (axioms()))
         (list_prefix " " term) (frees t)
    | Pdef(_,n,_) ->
       out oc "%a_def" name n
    | Pdeft(_,t,_,_) ->
       out oc "axiom_%d%a"
         (pos_first (fun th -> concl th = t) (axioms()))
         (list_prefix " " term) (frees t)
  in proof
;;

(****************************************************************************)
(* Functions translating type declarations and axioms. *)
(****************************************************************************)

let typ_arity oc k = for i = 1 to k do out oc "Set → " done; out oc "Set";;

let decl_typ oc (n,k) =
  out oc "constant symbol %a : %a;\n" name n typ_arity k;;

let typ_vars oc ts =
  match ts with
  | [] -> ()
  | ts -> out oc " [%a]" (list_sep " " typ) ts
;;

let decl_sym oc (n,b) =
  out oc "constant symbol %a%a : El %a;\n" name n typ_vars (tyvars b) typ b;;

let decl_def oc th =
  let t = concl th in
  let rmap = renaming_map [] in (* definitions are closed *)
  match t with
  | Comb(Comb(Const("=",_),Const(n,_)),_) ->
     out oc "symbol %a_def%a : Prf %a;\n"
       name n typ_vars (type_vars_in_term t) (term rmap) t
  | _ -> assert false
;;

let decl_axioms oc ths =
  let axiom i th =
    let t = concl th in
    let xs = frees t in
    let rmap = renaming_map xs in
    out oc "symbol axiom_%d%a%a : Prf %a;\n"
      i typ_vars (type_vars_in_term t) (list (decl_param rmap)) xs
      (term rmap) t
  in
  List.iteri axiom ths
;;

(****************************************************************************)
(* Lambdapi file generation. *)
(****************************************************************************)

let prelude = "/* Encoding of simple type theory */
constant symbol Set : TYPE;
constant symbol bool : Set;
constant symbol fun : Set → Set → Set;
injective symbol El : Set → TYPE;
rule El (fun $a $b) ↪ El $a → El $b;
injective symbol Prf : El bool → TYPE;

/* HOL-Light axioms and rules */
injective symbol el a : El a;
constant symbol = [a] : El a → El a → El bool;
symbol fun_ext [a b] [f g : El (fun a b)] :
  (Π x, Prf (= (f x) (g x))) → Prf (= f g);
symbol prop_ext [p q] : (Prf p → Prf q) → (Prf q → Prf p) → Prf (= p q);
symbol REFL [a] (t:El a) : Prf (= t t);
symbol MK_COMB [a b] [s t : El (fun a b)] [u v : El a] :
  Prf (= s t) → Prf (= u v) → Prf (= (s u) (t v));
symbol EQ_MP [p q : El bool] : Prf (= p q) → Prf p → Prf q;
symbol TRANS [a] [x y z : El a] :
  Prf (= x y) → Prf (= y z) → Prf (= x z) ≔
  λ xy: Prf (@= a x y), λ yz: Prf (@= a y z),
    @EQ_MP (@= a x y) (@= a x z)
      (@MK_COMB a bool (@= a x) (@= a x) y z (@REFL (fun a bool) (@= a x)) yz)
      xy;
/*begin
  assume a x y z xy yz; apply EQ_MP _ xy; apply MK_COMB (REFL (= x)) yz;
  flag \"print_implicits\" on; flag \"print_domains\" on; proofterm;
end;*/
";;

(* [theorem_as_axiom oc k] outputs on [oc] the proof of index [k]. *)
let theory oc =
  let no_bool_fun (n,_) = match n with "bool" | "fun" -> false | _ -> true in
  let types = List.filter no_bool_fun (types()) in
  let no_eq (n,_) = match n with "=" -> false | _ -> true in
  let constants = List.filter no_eq (constants()) in
  out oc
"%s
/* types */
%a
/* constants */
%a
/* axioms */
%a
/* definitions */
%a\n"
    prelude (list decl_typ) types (list decl_sym) constants
    decl_axioms (axioms()) (list decl_def) (definitions())
;;

(* [theorem oc k p] outputs on [oc] the proof [p] of index [k]. *)
let theorem oc k p =
  let Proof(thm,content) = p in
  (*log "theorem %d ...\n%!" k;*)
  let ts,t = dest_thm thm in
  let xs = freesl (t::ts) in
  let rmap = renaming_map xs in
  let tvs = type_vars_in_thm thm in
  (*out oc "/* rmap: %a */" (list_sep "; " (pair raw_var string)) rmap;*)
  let term = term rmap in
  let decl_hyps oc ts =
    List.iteri (fun i t -> out oc " (h%d : Prf %a)" (i+1) term t) ts in
  out oc "opaque symbol thm_%d%a%a%a : Prf %a ≔ %a;\n"
    k typ_vars tvs (list (decl_param rmap)) xs decl_hyps ts term t
    (proof tvs rmap) p
;;

(* [theorem_as_axiom oc k p] outputs on [oc] the proof [p] of index
   [k] as an axiom. *)
let theorem_as_axiom oc k p =
  let Proof(thm,content) = p in
  (*log "theorem %d as axiom ...\n%!" k;*)
  let ts,t = dest_thm thm in
  let xs = freesl (t::ts) in
  let rmap = renaming_map xs in
  let tvs = type_vars_in_thm thm in
  (*out oc "/* rmap: %a */" (list_sep "; " (pair raw_var string)) rmap;*)
  let term = term rmap in
  let decl_hyps oc ts =
    List.iteri (fun i t -> out oc " (h%d : Prf %a)" (i+1) term t) ts in
  out oc "symbol thm_%d%a%a%a : Prf %a;\n"
    k typ_vars tvs (list (decl_param rmap)) xs decl_hyps ts term t
;;

(* [proofs_in_range oc r] outputs on [oc] the proofs in range [r]. *)
let proofs_in_range oc = function
  | Only x ->
     let p = proof_at x in
     List.iter (fun k -> theorem_as_axiom oc k (proof_at k)) (deps p);
     theorem oc x p(*;
     out oc
"flag \"print_implicits\" on;
flag \"print_domains\" on;
print thm_%d;\n" x*)
  | Upto y -> for k = 0 to y do theorem oc k (proof_at k) done
  | All -> iter_proofs (theorem oc)
  | Inter(x,y) -> for k = x to y do theorem oc k (proof_at k) done
;;

(* [export_to_lp_file f r] creates a file of name [f] and outputs to this
   file the proofs in range [r]. *)
let export_to_lp_file filename r =
  print_time();
  log "generate %s ...\n%!" filename;
  let oc = open_out filename in
  theory oc;
  out oc "/* theorems */\n";
  proofs_in_range oc r;
  close_out oc;
  print_time()
;;

(* [export_to_lp_dir d r] creates in directory [d] a file for each
   proof in range [r]. *)
let export_to_lp_dir dirname r =
  print_time();
  if not (Sys.is_directory dirname) then
    failwith (Printf.sprintf "\"%s\" is not a directory\n" dirname);
  let filename = Filename.concat dirname in
  (* Generate the prelude with the encoding and the axioms. *)
  let fname = filename "lambdapi.pkg" in
  log "generate %s ...\n" fname;
  let oc = open_out fname in
  out oc "package_name = hol-light\nroot_path = hol-light\n";
  close_out oc;
  (* Generate the prelude with the encoding and the axioms. *)
  let fname = filename "prelude.lp" in
  log "generate %s ...\n" fname;
  let oc = open_out fname in
  theory oc;
  close_out oc;
  (* Generate shell script to check lp files. *)
  let fname = filename "check-lp.sh" in
  log "generate %s ...\n" fname;
  let oc = open_out_gen [Open_wronly;Open_creat;Open_trunc] 0o755 fname in
  let n =
    match r with
    | Only _ -> invalid_arg "export_to_lp_dir"
    | Upto x -> x
    | All -> nb_proofs()
  in
  out oc "#!/bin/bash\n
for i in prelude {0..%d}
do
  echo $i ...
  lambdapi check -c --verbose 0 $i.lp
done\n" n;
  close_out oc;
  (* Generate a lp file for each proof. *)
  let theorem_file k p =
    let fname = filename (string_of_int k ^ ".lp") in
    log "generate %s ...\n%!" fname;
    let oc = open_out fname in
    let dep oc k = out oc " hol-light.%d" k in
    out oc "require open hol-light.prelude%a;\n" (list dep) (deps p);
    theorem oc k p;
    close_out oc
  in
  begin match r with
  | All -> iter_proofs theorem_file
  | Upto x -> for k=0 to x do theorem_file k (proof_at k) done
  | Only _ -> invalid_arg "export_to_lp_dir"
  end;
  print_time()
;;

set_jrh_lexer;;
