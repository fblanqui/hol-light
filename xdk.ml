(****************************************************************************)
(* Export HOL-Light proofs to Dedukti. *)
(****************************************************************************)

unset_jrh_lexer;;

(****************************************************************************)
(* Translation of types and terms. *)
(****************************************************************************)

let is_valid_id =
  let re = Str.regexp "[a-zA-Z0-9][a-zA-Z0-9_']*" in
  fun s -> Str.string_match re s 0
;;

(* We use String.escaped because of a bug in Dedukti 2.7. This can be
   removed once the fix is merged in the next release. *)
let valid_name n = if is_valid_id n then n else "{|" ^ String.escaped n ^ "|}"

let name oc n = string oc (valid_name n);;

let suffix s oc n = name oc (n ^ s);;

let rec raw_typ oc b =
  match b with
  | Tyvar n -> out oc "%a" name n
  | Tyapp(c,[]) -> out oc "%a" name c
  | Tyapp(c,bs) -> out oc "(%a%a)" name c (list_prefix " " raw_typ) bs
;;

let typ tvs =
  let rec typ oc b =
    match b with
    | Tyvar n ->
       if List.mem b tvs then out oc "%a" name n else string oc "bool"
    | Tyapp(c,[]) -> out oc "%a" name c
    | Tyapp(c,bs) -> out oc "(%a%a)" name c (list_prefix " " typ) bs
  in typ
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
    | Var(n,_) -> out oc "%a (;not found;)" name n
    | _ -> assert false
;;

let decl_var tvs rmap oc t =
  match t with
  | Var(_,b) -> out oc "%a : El %a" (var rmap) t (typ tvs) b
  | _ -> assert false
;;

let decl_param tvs rmap oc v = out oc "%a -> " (decl_var tvs rmap) v;;

let param tvs rmap oc v = out oc "%a => " (decl_var tvs rmap) v;;

let term tvs =
  let typ = typ tvs in
  let rec term rmap oc t =
    match t with
    | Var(n,b) ->
       begin
         try name oc (List.assoc t rmap)
         with Not_found -> out oc "(;%a;)(el %a)" name n typ b
       end
    | Const(n,b) ->
       begin match List.map (subtype b) (const_type_vars_pos n) with
       | [] -> out oc "%a" name n
       | bs -> out oc "(%a%a)" name n (list_prefix " " typ) bs
       end
    | Comb(_,_) ->
       let h, ts = head_args t in
       out oc "(%a%a)" (term rmap) h (list_prefix " " (term rmap)) ts
    | Abs(t,u) ->
       let rmap' = add_var rmap t in
       out oc "(%a => %a)" (decl_var tvs rmap') t (term rmap') u
  in term
;;

(* for debug *)
let subst_type tvs =
  let typ = typ tvs in
  list_sep "; " (fun oc (b,v) -> out oc "%a -> %a" typ v typ b);;

let subst_term tvs rmap =
  list_sep "; "
    (fun oc (t,v) -> out oc "%a -> %a" raw_var v (term tvs rmap) t);;

(****************************************************************************)
(* Proof translation. *)
(****************************************************************************)

(* Printing on the output channel [oc] of the subproof [p2] given:
- tvs: list of type variables of the theorem
- rmap: renaming map for term variables
- ty_su: type substitution that needs to be applied
- tm_su: term substitution that needs to be applied
- ts1: hypotheses of the theorem *)
let subproof tvs rmap ty_su tm_su ts1 oc p2 =
  let typ = typ tvs in
  let term = term tvs rmap in
  let Proof(i2,th2,_) = p2 in
  let ts2,t2 = dest_thm th2 in
  (* vs2 is the list of free term variables of th2 *)
  let vs2 = freesl (t2::ts2) in
  (* vs2 is now the application of tm_su on vs2 *)
  let vs2 = vsubstl tm_su vs2 in
  (* ts2 is now the application of tm_su on ts2 *)
  let ts2 = vsubstl tm_su ts2 in
  (* tvs2 is the list of type variables of th2 *)
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
  (* vs2 is now the application of ty_su on vs2 *)
  let vs2 = List.map (inst ty_su) vs2 in
  (* ts2 is now the application of ty_su on ts2 *)
  let ts2 = List.map (inst ty_su) ts2 in
  (* bs is the list of types obtained by applying ty_su on tvs2 *)
  let bs = List.map (type_subst ty_su) tvs2 in
  let hyp oc t = out oc "h%d" (try 1 + index t ts1 with _ -> 0) in
  out oc "(thm_%d%a%a%a)" i2 (list_prefix " " typ) bs
    (list_prefix " " term) vs2 (list_prefix " " hyp) ts2
;;

(* In a theorem, the hypotheses [t1;..;tn] are given the names
   ["v1";..;"vn"]. *)
let proof tvs rmap =
  let typ = typ tvs in
  let term = term tvs rmap in
  let rec proof oc p =
    let Proof(_,thm,content) = p in
    let ts = hyp thm in
    let sub = subproof tvs rmap [] [] ts in
    match content with
    | Prefl(t) ->
       out oc "REFL %a %a" typ (type_of t) term t
    | Ptrans(p1,p2) ->
       let a,x,y = get_eq_type_args p1 in
       let _,z = get_eq_args p2 in
       out oc "TRANS %a %a %a %a %a %a"
         typ (get_eq_type p1) term x term y term z sub p1 sub p2
    | Pmkcomb(p1,p2) ->
       let a,b,s,t =
         let Proof(_,th,_) = p1 in
         match concl th with
         | Comb(Comb(Const("=",Tyapp("fun",[b1;b2])),s),t) ->
            begin match b1 with
            | Tyapp("fun",[a;b]) -> a,b,s,t
            | _ -> assert false
            end
         | _ -> assert false
       in
       let u,v = get_eq_args p2 in
       out oc "MK_COMB %a %a %a %a %a %a %a %a"
         typ a typ b term s term t term u term v sub p1 sub p2
    | Pabs(p',t) ->
       let ab,f,g = get_eq_type_args p in
       let a,b = match ab with Tyapp("fun",[a;b]) -> a,b | _ -> assert false in
       let rmap' = add_var rmap t in
       out oc "fun_ext %a %a %a %a (%a => %a)"
         typ a typ b term f term g (decl_var tvs rmap') t
         (subproof tvs rmap' [] [] ts) p'
    | Pbeta(Comb(Abs(x,t),y)) when x = y ->
       out oc "REFL %a %a" typ (type_of t) term t
    | Pbeta(t) ->
       out oc "REFL %a %a" typ (type_of t) term t
    | Passume(t) ->
       out oc "h%d" (1 + index t (hyp thm))
    | Peqmp(p1,p2) ->
       let p,q = get_eq_args p1 in
       out oc "EQ_MP %a %a %a %a" term p term q sub p1 sub p2
    | Pdeduct(p1,p2) ->
       let Proof(_,th1,_) = p1 and Proof(_,th2,_) = p2 in
       let t1 = concl th1 and t2 = concl th2 in
       let n = 1 + List.length ts in
       out oc "prop_ext %a %a (h%d : Prf %a => %a) (h%d : Prf %a => %a)"
         term t1 term t2
         n term t1 (subproof tvs rmap [] [] (ts @ [t1])) p2
         n term t2 (subproof tvs rmap [] [] (ts @ [t2])) p1
    | Pinst(p,[]) -> proof oc p
    | Pinst(p,s) ->
       out oc "%a" (subproof tvs rmap [] s ts) p
    | Pinstt(p,[]) -> proof oc p
    | Pinstt(p,s) ->
       out oc "%a" (subproof tvs rmap s [] ts) p
    | Pdef(t,n,b) ->
       let ps = const_type_vars_pos n in
       (*out oc "(;t=%a; b=%a; ps=%a;)" term t typ b type_var_pos_list ps;*)
       begin match List.map (subtype b) ps with
       | [] -> out oc "%a" (suffix "_def") n
       | bs -> out oc "(%a%a)" (suffix "_def") n (list_prefix " " typ) bs
       end
    | Paxiom(t) ->
       let k =
         try pos_first (fun th -> concl th = t) (axioms())
         with Not_found -> assert false
       in
       out oc "axiom_%d%a%a" k
         (list_prefix " " typ) (type_vars_in_term t)
         (list_prefix " " term) (frees t)
    | Pdeft(p,t,n,b) ->
       let k =
         try pos_first (fun th -> concl th = t) (axioms())
         with Not_found -> assert false
       in
       out oc "axiom_%d%a%a" k
         (list_prefix " " typ) (type_vars_in_term t)
         (list_prefix " " term) (frees t)
  in proof
;;

(****************************************************************************)
(* Functions translating type declarations and axioms. *)
(****************************************************************************)

let typ_arity oc k = for i = 1 to k do out oc "Set -> " done; out oc "Set";;

let decl_typ oc (n,k) =
  out oc "%a : %a.\n" name n typ_arity k;;

let decl_typ_param tvs oc b = out oc "%a : Set -> " (typ tvs) b;;

let typ_param tvs oc b = out oc "%a : Set => " (typ tvs) b;;

let decl_sym oc (n,b) =
  let tvs = tyvars b in
  out oc "%a : %aEl %a.\n" name n (list (decl_typ_param tvs)) tvs (typ tvs) b
;;

let decl_def oc th =
  let rmap = renaming_map_thm th in
  match concl th with
  | Comb(Comb(Const("=",_),Const(n,_)),_) as c ->
     let tvs = type_vars_in_term c in
     out oc "%a : %aPrf %a.\n"
       (suffix "_def") n (list (decl_typ_param tvs)) tvs (term tvs rmap) c
  | _ -> assert false
;;

let decl_axioms oc ths =
  let axiom i th =
    let rmap = renaming_map_thm th in
    let c = concl th in
    let tvs = type_vars_in_term c in
    out oc "def axiom_%d : %a%aPrf %a.\n"
      i (list (decl_typ_param tvs)) tvs
      (list (decl_param tvs rmap)) (frees c) (term tvs rmap) c
  in
  List.iteri axiom ths
;;

(****************************************************************************)
(* Lambdapi file generation. *)
(****************************************************************************)

let prelude = "(; Encoding of simple type theory ;)
Set : Type.
bool : Set.
fun : Set -> Set -> Set.
injective El : Set -> Type.
[a, b] El (fun a b) --> El a -> El b.
injective Prf : El bool -> Type.

(; HOL-Light axioms and rules ;)
el : a : Set -> El a.
{|=|} : a : Set -> El a -> El a -> El bool.
def fun_ext : a : Set -> b : Set -> f : El (fun a b) -> g : El (fun a b) ->
  (x : El a -> Prf ({|=|} b (f x) (g x))) -> Prf ({|=|} (fun a b) f g).
def prop_ext : p : El bool -> q : El bool ->
  (Prf p -> Prf q) -> (Prf q -> Prf p) -> Prf ({|=|} bool p q).
def REFL : a : Set -> t : El a -> Prf ({|=|} a t t).
def MK_COMB : a : Set -> b : Set -> s : El (fun a b) -> t : El (fun a b) ->
  u : El a -> v : El a -> Prf({|=|} (fun a b) s t) -> Prf({|=|} a u v) ->
  Prf ({|=|} b (s u) (t v)).
def EQ_MP : p : El bool -> q : El bool -> Prf({|=|} bool p q) -> Prf p -> Prf q.
thm TRANS : a : Set -> x : El a -> y : El a -> z : El a ->
  Prf ({|=|} a x y) -> Prf ({|=|} a y z) -> Prf ({|=|} a x z) :=
  a: Set => x: El a => y: El a => z: El a =>
  xy: Prf ({|=|} a x y) => yz: Prf ({|=|} a y z) =>
  EQ_MP ({|=|} a x y) ({|=|} a x z)
    (MK_COMB a bool ({|=|} a x) ({|=|} a x) y z
       (REFL (fun a bool) ({|=|} a x)) yz) xy.
";;

let theory oc =
  let no_bool_fun (n,_) = match n with "bool" | "fun" -> false | _ -> true in
  let types = List.filter no_bool_fun (types()) in
  let no_eq (n,_) = match n with "=" -> false | _ -> true in
  let constants = List.filter no_eq (constants()) in
  out oc
"%s
(; types ;)
%a
(; constants ;)
%a
(; axioms ;)
%a
(; definitions ;)
%a
(; theorems ;)\n"
    prelude (list decl_typ) types (list decl_sym) constants
    decl_axioms (axioms()) (list decl_def) (definitions())
;;

(* [theorem_as_axiom oc k] outputs on [oc] the proof of index [k]. *)
let theorem oc k =
  (*log "theorem %d ...@." k;*)
  let p = proof_at k in
  let Proof(_,thm,content) = p in
  let ts,t = dest_thm thm in
  let xs = freesl (t::ts) in
  let rmap = renaming_map xs in
  let tvs = type_vars_in_thm thm in
  (*out oc "(;rmap: %a;)" (list_sep "; " (pair raw_var string)) rmap;*)
  let term = term tvs rmap in
  let hyps_typ oc ts =
    List.iteri (fun i t -> out oc "h%d : Prf %a -> " (i+1) term t) ts in
  let hyps oc ts =
    List.iteri (fun i t -> out oc "h%d : Prf %a => " (i+1) term t) ts in
  out oc "thm thm_%d : %a%a%aPrf %a := %a%a%a%a.\n"
    k (list (decl_typ_param tvs)) tvs
    (list (decl_param tvs rmap)) xs hyps_typ ts term t
    (list (typ_param tvs)) tvs (list (param tvs rmap)) xs hyps ts
    (proof tvs rmap) p
;;

(* [theorem_as_axiom oc k] outputs on [oc] the theorem of index [k] as
   an axiom. *)
let theorem_as_axiom oc k =
  (*log "theorem %d as axiom ...@." k;*)
  let p = proof_at k in
  let Proof(_,thm,content) = p in
  let ts,t = dest_thm thm in
  let xs = freesl (t::ts) in
  let rmap = renaming_map xs in
  let tvs = type_vars_in_thm thm in
  (*out oc "(;rmap: %a;)" (list_sep "; " (pair raw_var string)) rmap;*)
  let term = term tvs rmap in
  let hyps_typ oc ts =
    List.iteri (fun i t -> out oc "h%d : Prf %a -> " (i+1) term t) ts in
  out oc "thm_%d : %a%a%aPrf %a.\n"
    k (list (decl_typ_param tvs)) tvs
    (list (decl_param tvs rmap)) xs hyps_typ ts term t
;;

(* [proofs_in_range oc r] outputs on [oc] the theorems in range [r]. *)
let proofs_in_range oc = function
  | Only x ->
     let p = proof_at x in
     List.iter (theorem_as_axiom oc) (deps p);
     theorem oc x
  | Upto y -> for k = 0 to y do theorem oc k done
  | All -> List.iter (fun p -> theorem oc (index_of p)) (proofs())
;;

(* [export_to_lp f r] creates a file of name [f] and outputs to this
   file the proofs in range [r]. *)
let export_to_dk filename r =
  print_time();
  log "generate %s ...@." filename;
  let oc = open_out filename in
  theory oc;
  proofs_in_range oc r;
  close_out oc;
  print_time()
;;

set_jrh_lexer;;
