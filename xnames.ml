(****************************************************************************)
(* Compute the theorems of each file, following ProofTrace/proofs.ml. *)
(****************************************************************************)

let PROVE_1_RE = Str.regexp (String.concat "" (
  "\\(let\\|and\\)[ \n\t]*"::
  "\\([a-zA-Z0-9_-]+\\)[ \n\t]*"::
  "=[ \n\t]*"::
  "\\(prove\\|"::
  "prove_by_refinement\\|"::
  "new_definition\\|"::
  "new_basic_definition\\|"::
  "new_axiom\\|"::
  "new_infix_definition\\|"::
  "INT_OF_REAL_THM\\|"::
  "define_finite_type\\|"::
  "TAUT\\|"::
  "INT_ARITH\\|"::
  "new_recursive_definition\\)"::
  []
))

let PROVE_2_RE = Str.regexp (String.concat "" (
  "\\(let\\|and\\)[ \n\t]*"::
  "\\([a-zA-Z0-9_-]+\\)[ \n\t]*,[ \n\t]*"::
  "\\([a-zA-Z0-9_-]+\\)[ \n\t]*"::
  "=[ \n\t]*"::
  "\\(define_type\\|"::
  "(CONJ_PAIR o prove)\\)"::
  []
))

let PROVE_3_RE = Str.regexp (String.concat "" (
  "\\(let\\|and\\)[ \n\t]*"::
  "\\([a-zA-Z0-9_-]+\\)[ \n\t]*,[ \n\t]*"::
  "\\([a-zA-Z0-9_-]+\\)[ \n\t]*,[ \n\t]*"::
  "\\([a-zA-Z0-9_-]+\\)[ \n\t]*"::
  "=[ \n\t]*"::
  "\\(new_inductive_definition\\)"::
  []
))

let search_1 content =
  let rec search acc start =
    try
      let _ = Str.search_forward PROVE_1_RE content start in
      let matches = (Str.matched_group 2 content)::[] in
      search (matches @ acc) (Str.match_end())
    with e -> (acc)
  in search [] 0
;;

let search_2 content =
  let rec search acc start =
    try
      let _ = Str.search_forward PROVE_2_RE content start in
      let matches = (Str.matched_group 2 content)::
                    (Str.matched_group 3 content)::
                    [] in
      search (matches @ acc) (Str.match_end())
    with e -> (acc)
  in search [] 0
;;

let search_3 content =
  let rec search acc start =
    try
      let _ = Str.search_forward PROVE_3_RE content start in
      let matches = (Str.matched_group 2 content)::
                    (Str.matched_group 3 content)::
                    (Str.matched_group 4 content)::
                    [] in
      search (matches @ acc) (Str.match_end())
    with e -> (acc)
  in search [] 0
;;

let load_file f =
  let ic = open_in f in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  Bytes.to_string s
;;

let theorems_of_file f =
  let s = load_file f in search_1 s @ search_2 s @ search_3 s
;;

let source_files() =
  let rec walk acc = function
  | [] -> acc
  | dir::tail ->
     let contents = Array.to_list (Sys.readdir dir) in
     let dirs, files =
       List.fold_left
         (fun (dirs,files) f ->
           try
             if Filename.check_suffix f ".ml"
                || Filename.check_suffix f ".hl" then
               let f = Filename.concat dir f in (dirs, f::files)
             else
               (*FIXME:temporary hack to avoid following links*)
               if f = "_opam" then (dirs, files) else
               let f = Filename.concat dir f in
               (*Unix.(match (stat f).st_kind with
               | S_DIR -> (f::dirs, files)
               | _ -> (dirs, files))*)
               if Sys.is_directory f then (f::dirs, files)
               else (dirs, files)
           with Sys_error _ -> (dirs, files))
         ([],[]) contents
     in
     walk (files @ acc) (dirs @ tail)
  in walk [] [Sys.getcwd()]
;;

let files = log "compute list of files ...\n%!"; source_files();;

unset_jrh_lexer;;

let update_map_file_thms() =
  log "compute theorem names in each file ...\n%!";
  map_file_thms :=
    List.fold_left
      (fun map f -> MapStr.add f (theorems_of_file f) map)
      MapStr.empty files
;;

(****************************************************************************)
(* Compute the map thm_id -> name, following ProofTrace/proof.ml. *)
(****************************************************************************)

let eval code =
  let as_buf = Lexing.from_string code in
  let parsed = !Toploop.parse_toplevel_phrase as_buf in
  ignore (Toploop.execute_phrase true Format.std_formatter parsed)

let idx = ref (-1);;

let cmd_set_idx name = Printf.sprintf "idx := index_of %s;;" name;;

let update_map_thm_id_name() =
  log "compute map id -> theorem ...\n%!";
  map_thm_id_name :=
    MapStr.fold
      (fun filename thm_names map ->
        List.fold_left
          (fun map name ->
            if name = "_" then map else
            let name = if name = "_FALSITY_" then name ^ "DEF" else name in
              (* to give a name to the theorem "_FALSITY_" different
                 from the constant "_FALSITY_". *)
            try eval (cmd_set_idx name); MapInt.add !idx name map
            with _ -> map)
          map thm_names)
      !map_file_thms MapInt.empty
;;

let print_map_thm_id_name() =
  MapInt.iter (fun k name -> log "%d %s\n" k name) !map_thm_id_name;;

set_jrh_lexer;;
