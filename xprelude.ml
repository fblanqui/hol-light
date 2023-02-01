(****************************************************************************)
(* Definitions shared between all files for Dedukti/Lambdapi export. *)
(****************************************************************************)

#load "unix.cma";;
#load "str.cma";;

let out = Printf.fprintf;;
let log = Printf.printf;;

let time_of p =
  let t0 = Sys.time() in
  p();
  let t1 = Sys.time() in
  Printf.printf "time: %f s\n" (t1 -. t0)
;;

let print_time =
  let t = ref (Sys.time()) in
  fun () ->
  let t' = Sys.time() in log "time: %f s\n" (t' -. !t); t := t'
;;

module OrdInt = struct type t = int let compare = (-) end;;
module MapInt = Map.Make(OrdInt);;

let map_thm_id_name = ref MapInt.empty;;

module OrdStr = struct type t = string let compare = compare end;;
module MapStr = Map.Make(OrdStr);;
module SetStr = Set.Make(OrdStr);;

let map_const_type_vars_pos = ref MapStr.empty;;

let map_file_thms = ref MapStr.empty;;
