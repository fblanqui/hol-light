unset_jrh_lexer;;

(****************************************************************************)
(* Ranges of proof indexes. *)
(****************************************************************************)

type range = Only of int | Upto of int | All;;

let in_range = function
  | Only x -> fun k -> k = x
  | Upto x -> fun k -> k <= x
  | All -> fun _ -> true
;;

(****************************************************************************)
(* Functions on basic data structures. *)
(****************************************************************************)

(* [pos_first f l] returns the position (counting from 0) of the first
   element of [l] satisfying [f]. Raises Not_found if there is no such
   element. *)
let pos_first f =
  let rec aux k l =
    match l with
    | [] -> raise Not_found
    | y::l -> if f y then k else aux (k+1) l
  in aux 0
;;

(****************************************************************************)
(* Printing functions. *)
(****************************************************************************)

let int oc k = out oc "%d" k;;

let string oc s = out oc "%s" s;;

let pair f g oc (x, y) = out oc "%a, %a" f x g y;;

let prefix p elt oc x = out oc "%s%a" p elt x;;

let list_sep sep elt oc xs =
  match xs with
  | [] -> ()
  | x::xs -> elt oc x; List.iter (prefix sep elt oc) xs
;;

let list elt oc xs = list_sep "" elt oc xs;;

let list_prefix p elt oc xs = list (prefix p elt) oc xs;;

let olist elt oc xs = out oc "[%a]" (list_sep "; " elt) xs;;

let hstats oc ht =
  let open Hashtbl in let s = stats ht in
  out oc "{ num_bindings = %d; num_buckets = %d; max_bucket_length = %d }\n"
    s.num_bindings s.num_buckets s.max_bucket_length
;;

(****************************************************************************)
(* Functions on types and terms. *)
(****************************************************************************)

(* Sets and maps on terms. *)
module OrdTrm = struct type t = string let compare = compare end;;
module MapTrm = Map.Make(OrdTrm);;
module SetTrm = Set.Make(OrdTrm);;

(* [head_args t] returns the pair [h,ts] such that [t] is of the t is
   the Comb application of [h] to [ts]. *)
let head_args =
  let rec aux acc t =
    match t with
    | Comb(t1,t2) -> aux (t2::acc) t1
    | _ -> t, acc
  in aux []
;;

(* [get_eq_type p] returns the type [b] of the terms t and u of the
   conclusion of the proof [p] assumed of the form [= t u]. *)
let get_eq_type p =
  let Proof(th,_) = p in
  match concl th with
  | Comb(Comb(Const("=",Tyapp("fun",[b;_])),_),_) -> b
  | _ -> assert false
;;

(* [get_eq_args p] returns the terms t and u of the conclusion of the
   proof [p] assumed of the form [= t u]. *)
let get_eq_args p =
  let Proof(th,_) = p in
  match concl th with
  | Comb(Comb(Const("=",_),t),u) -> t,u
  | _ -> let t = mk_var("error",bool_ty) in t,t (*assert false*)
;;

(* [get_eq_type_args p] returns the type of the terms t and u, and the
   terms t and u, of the conclusion of the proof [p] assumed of the
   form [= t u]. *)
let get_eq_type_args p =
  let Proof(th,_) = p in
  match concl th with
  | Comb(Comb(Const("=",Tyapp("fun",[b;_])),t),u) -> b,t,u
  | _ -> assert false
;;

(* [index t ts] returns the position (counting from 0) of the first
   element of [ts] alpha-equivalent to [t]. Raises Not_found if there
   is no such term. *)
let index t =
  try pos_first (fun u -> alphaorder t u = 0)
  with Not_found -> assert false;;

(* [vsubstl s ts] applies the substitution [s] to each term of [ts]. *)
let vsubstl s ts = if s = [] then ts else List.map (vsubst s) ts;;

(* It is important for the export that list of type variables and term
   free variables are always ordered and have no duplicate. *)

(* [type_vars bs] returns the ordered list with no duplicate of type
   variables occurring in the list of types [bs]. *)
let type_vars bs =
  List.sort_uniq compare
    (List.fold_left (fun l b -> tyvars b @ l) [] bs)
;;

(* Redefinition of [tyvars] so that the output is sorted and has no
   duplicate. *)
let tyvars b = List.sort_uniq compare (tyvars b);;

(* [type_vars_in_terms ts] returns the ordered list with no duplicate
   of type variables occurring in the list of terms [ts]. *)
let type_vars_in_terms ts =
  List.sort_uniq compare
    (List.fold_left (fun l t -> type_vars_in_term t @ l) [] ts)
;;

(* Redefinition of [type_vars_in_term] so that the output is sorted
   and has no duplicat. *)
let type_vars_in_term t = List.sort_uniq compare (type_vars_in_term t)

(* [type_vars_in_terms th] returns the ordered list with no duplicate
   of type variables occurring in the theorem [th]. *)
let type_vars_in_thm thm =
  let ts,t = dest_thm thm in type_vars_in_terms (t::ts);;

(* [vars_terms ts] returns the ordered list with no duplicate of all
   the term variables (including bound variables) occurring in the
   terms [ts] *)
let vars_terms =
  let rec vars_term t =
    match t with
    | Const _ -> []
    | Var _ -> [t]
    | Abs(t,u) -> t :: vars_term u
    | Comb(t,u) -> vars_term t @ vars_term u
  in
  fun ts ->
  List.sort_uniq compare
    (List.fold_left (fun vs t -> vs @ vars_term t) [] ts);;

(* [variant rmap v] returns a variable with the same type as the one
   of [v] but with a name not occuring in the codomain of [rmap]. *)
let variant rmap =
  let rec variant v =
    match v with
    | Var(n,b) ->
       if List.exists (fun (_,s) -> s = n) rmap then variant (mk_var(n^"'",b))
       else v
    | _ -> assert false
  in variant
;;

(* [add_var rmap v] returns a map extending [rmap] with a mapping from
   [v] to a name not occurring in the codomain of [rmap]. *)
let add_var rmap v =
  match variant rmap v with
  | Var(n,_) -> (v,n)::rmap
  | _ -> assert false
;;

(* [renaming_map vs] returns an association list giving new distinct names
   to all the variables occurring in the list of variables [vs]. *)
let renaming_map = List.fold_left add_var [];;

(* Subterm positions in types are represented as list of natural numbers. *)

(* [subtype b p] returns the type at position [p] in the type [b]. *)
let rec subtype b p =
  match b, p with
  | _, [] -> b
  | Tyapp(_, bs), p::ps -> subtype (List.nth bs p) ps
  | _ -> invalid_arg "subtype"
;;

(* [type_vars_pos b] returns an association list mapping every type
   variable occurrence to its posiion in [b]. *)
let type_vars_pos b =
  let rec aux acc l =
    match l with
    | [] -> acc
    | (Tyvar n, p)::l -> aux ((n, List.rev p)::acc) l
    | (Tyapp(n,bs), p)::l ->
       aux acc
         (let k = ref (-1) in
          List.fold_left
            (fun l b -> incr k; (b,!k::p)::l)
            l bs)
  in aux [] [b,[]]
;;

(* test:
type_vars_pos
  (mk_type("fun",[mk_vartype"a"
                 ;mk_type("fun",[mk_vartype"a";mk_vartype"b"])]));;*)

(****************************************************************************)
(* Functions on proofs. *)
(****************************************************************************)

(* [deps p] returns the list of proof indexes the proof [p] depends on. *)
let deps p =
  let Proof(_,content) = p in
  match content with
  | Ptrans(p1,p2) | Pmkcomb(p1,p2) | Peqmp(p1,p2) | Pdeduct(p1,p2) -> [p1;p2]
  | Pabs(p1,_) | Pinst(p1,_) | Pinstt(p1,_)| Pdeft(p1,_,_,_) -> [p1]
  | _ -> []
;;

(* Print some statistics on how many times a proof is used. *)
let print_proof_stats() =
  (* Array for mapping each proof index to the number of times it is used. *)
  let proof_uses = Array.make (nb_proofs()) 0 in
  (* Maximum number of times a proof is used. *)
  let max = ref 0 in
  (* Actually compute [proof_uses]. *)
  let use k =
    let n = Array.get proof_uses k + 1 in
    Array.set proof_uses k n;
    if n > !max then max := n
  in
  iter_proofs (fun _ p -> List.iter use (deps p));
  (* Array for mapping to each number n <= !max the number of proofs which
     is used n times. *)
  let hist = Array.make (!max + 1) 0 in
  let f nb_uses = Array.set hist nb_uses (Array.get hist nb_uses + 1) in
  Array.iter f proof_uses;
  (* Print histogram *)
  log "i: n means that n proofs are used i times\n";
  let nonzeros = ref 0 in
  for i=0 to !max do
    let n = Array.get hist i in
    if n>0 then (incr nonzeros; log "%d: %d\n" i n)
  done;
  log "number of mappings: %d\n" !nonzeros;
  (* Count the number of times each proof rule is used. *)
  let index p =
    let Proof(_,c) = p in
    match c with
    | Prefl _ -> 0
    | Ptrans _ -> 1
    | Pmkcomb _ -> 2
    | Pabs _ -> 3
    | Pbeta _ -> 4
    | Passume _ -> 5
    | Peqmp _ -> 6
    | Pdeduct _ -> 7
    | Pinst _ -> 8
    | Pinstt _ -> 9
    | Paxiom _ -> 10
    | Pdef _ -> 11
    | Pdeft _ -> 12
  in
  let name = function
    | 0 -> "refl"
    | 1 -> "trans"
    | 2 -> "comb"
    | 3 -> "abs"
    | 4 -> "beta"
    | 5 -> "assume"
    | 6 -> "eqmp"
    | 7 -> "deduct"
    | 8 -> "term_subst"
    | 9 -> "type_subst"
    | 10 -> "axiom"
    | 11 -> "sym_def"
    | 12 -> "type_def"
    | _ -> assert false
  in
  let rule_uses = Array.make 13 0 in
  let f k p =
    let i = index p in
    let n = Array.get rule_uses i + 1 in
    Array.set rule_uses i n
  in
  iter_proofs f;
  let total = float_of_int (nb_proofs()) in
  let part n = float_of_int (100 * n) /. total in
  let f i n = log "%10s %9d %2.f%%\n" (name i) n (part n) in
  Array.iteri f rule_uses
;;

(****************************************************************************)
(* Build a map associating to each constant c a list of positions
   [p1;..;pn] such that pi is the position in the type of c of its
   i-th type variable (as given by tyvars). *)
(****************************************************************************)

let update_map_const_type_vars_pos() =
  map_const_type_vars_pos :=
    List.fold_left
      (fun map (n,b) ->
        let l = type_vars_pos b in
        let ps =
          List.map
            (fun v ->
              match v with
              | Tyvar n ->
                 begin
                   try List.assoc n l
                   with Not_found -> assert false
                 end
              | _ -> assert false)
            (tyvars b)
        in
        MapStr.add n ps map)
      MapStr.empty (constants())
;;

let type_var_pos_list = list_sep "; " (list_sep "," int);;

let print_map_const_type_vars_pos() =
  MapStr.iter
    (fun c ps -> log "%s %a\n" c (olist (olist int)) ps)
    !map_const_type_vars_pos;;

let const_type_vars_pos n =
  try MapStr.find n !map_const_type_vars_pos
  with Not_found -> log "no const_type_vars_pos for %s@." n; assert false;;

set_jrh_lexer;;
