(* ------------------------------------------------------------------------- *)
(* Load in the bignum library.                                               *)
(* ------------------------------------------------------------------------- *)

Topfind.load_deeply ["zarith"];;

(* A wrapper of Zarith that has an interface of Num.
   However, this is different from the real Num library because it supports
   infinity and undef. If exception happens, Failure with the name of the
   exception is raised. *)
module Num = struct
  type num = Q.t

  let num_of_int (n:int):num = Q.of_int n

  let int_of_num (n:num):int =
    try Q.to_int n
    with Z.Overflow -> failwith "Z.Overflow"

  let float_of_num (n:num):float = Q.to_float n

  (* base must be Z.t and exponent
     must fit in the range of OCaml int type *)
  let power_num (base:num) (exponent:num):num =
    let exp_i = int_of_num exponent in
    Q.of_bigint (Z.pow (Q.to_bigint base) exp_i)

  let pow (base:num) (exponent:int):num =
    Q.of_bigint (Z.pow (Q.to_bigint base) exponent)

  let add_num = Q.add

  let abs_num = Q.abs

  let ceiling_num (c:num) =
    try Q.of_bigint (Z.cdiv c.num c.den)
    with Division_by_zero -> failwith "Division_by_zero"

  let compare_num = Q.compare

  let div_num = Q.div

  let eq_num = Q.equal

  let floor_num (c:num) =
    try Q.of_bigint (Z.fdiv c.num c.den)
    with Division_by_zero -> failwith "Division_by_zero"

  let ge_num = Q.geq

  let gt_num = Q.gt

  let le_num = Q.leq

  let lt_num = Q.lt

  let max_num = Q.max

  let minus_num = Q.neg

  let min_num = Q.min

  let mod_num = fun x y ->
    Q.of_bigint (Z.erem (Q.to_bigint x) (Q.to_bigint y))

  let mult_num = Q.mul

  (* 1/2 -> 1, -1/2 -> -1 *)
  let round_num =
    let half = Q.make (Z.of_int 1) (Z.of_int 2) in
    let one = Q.make (Z.of_int 1) (Z.of_int 1) in
    fun x ->
      let s = Q.sign x in
      if s = 0 then x
      else
        let v = Q.abs x in
        let vint = floor_num v in
        let vfrac = Q.sub v vint in
        let absres =
          if Q.leq half vfrac
          then Q.add vint one
          else vint in
        Q.mul (Q.of_int s) absres

  let sign_num = Q.sign

  let sub_num = Q.sub

  let quo_num = fun x y ->
    Q.of_bigint (Z.ediv (Q.to_bigint x) (Q.to_bigint y))

  let is_integer_num (n:num) =
    Q.equal n (floor_num n)

  let succ_num = fun n ->
    Q.of_bigint (Z.succ (Q.to_bigint n))

  let string_of_num (n:num) = Q.to_string n

  (* Num's num_of_string only accepts integers. *)
  let num_of_string (s:string) =
    try Q.of_bigint (Z.of_string s)
    with _ -> failwith "num_of_string"

end;;

let (=/) x y = Num.eq_num x y;;

let (<>/) x y = not (x =/ y);;

let (+/) x y = Num.add_num x y;;

let (-/) x y = Num.sub_num x y;;

let (//) x y = Num.div_num x y;;

let ( */) x y = Num.mult_num x y;;

let (</) x y = Num.lt_num x y;;

let (>/) x y = Num.gt_num x y;;

let (<=/) x y = Num.le_num x y;;

let (>=/) x y = Num.ge_num x y;;

let pp_print_num fmt (n:Num.num) =
  Format.pp_open_hbox fmt ();
  Format.pp_print_string fmt (Num.string_of_num n);
  Format.pp_close_box fmt ();;

let print_num = pp_print_num Format.std_formatter;;

#install_printer pp_print_num;;

include Num;;

let num = Num.num_of_int;;

let ( **/) x y =
  if y >=/ num 0 then Num.power_num x y
  else num 1 // Num.power_num x (minus_num y);;

let power_num = ( **/);;

module NumExt = struct
  let numdom (r:num):num * num =
    Q.of_bigint r.num, Q.of_bigint r.den

  let gcd_num =
      fun x y -> Q.of_bigint (Z.gcd (Q.to_bigint x) (Q.to_bigint y))

end;;

open NumExt;;
