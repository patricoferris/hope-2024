module Json

open FStar.List
open Compiler.Model1
open Model
// TODO: Reuse JSON parsing library, very outdated
// open Data.JSON

type json =
  | O : list (string * json) -> json
  | A : list json -> json
  | String : string -> json
  | Number : string -> json (* For simplicity, we implement no number parsing *)
  | Bool : bool -> json
  | Null

let rec contains_assoc_key_value (j : list (string * json)) (k : string) (v : json)  = match j with
  | [] -> false
  | (key, value) :: rest ->
    (key = k && value = v) || contains_field_value value k v || contains_assoc_key_value rest k v

and check_json_list (l : list json) k v = match l with
  | [] -> false
  | j :: rest ->
    contains_field_value j k v || check_json_list rest k v

and contains_field_value (j : json) (k : string) (v : json) : bool = match j with
  | O assoc -> contains_assoc_key_value assoc k v
  | A lst -> check_json_list lst k v
  | _ -> false

(* $MDX part-begin=is_endangered *)
let is_endangered (j : json) = contains_field_value j "rarity" (String "endangered")

let _ = assert (is_endangered (String "foo") = false)
let _ = assert (is_endangered (O [ "rarity", String "endangered" ]) = true)
let _ = assert (is_endangered (A [(O [ "rarity", String "endangered" ])]) = true)

(* https://www.iucnredlist.org/ *)
let datamap = [
  "iberian-lynx.geojson", O [ "rarity", String "vulnerable" ];
  "bornean-elephant.geojson", O [ "rarity", String "endangered" ]
]
(* $MDX part-end *)

let rec path_is_not_endangered (p : string) (v : list (string * json)) = match v with
  | [] -> false
  | (p', j) :: rest -> 
    (p = p' && not (is_endangered j)) || path_is_not_endangered p rest

let _ = assert (path_is_not_endangered "hello.txt" datamap = false)
let _ = assert (path_is_not_endangered "iberian-lynx.geojson" datamap = true)
let _ = assert (path_is_not_endangered "bornean-elephant.geojson" datamap = false)

let rec all_paths_are_not_endangered (ps : list path) = match ps with
  | [] -> true
  | p :: ps -> path_is_not_endangered p datamap && all_paths_are_not_endangered ps

(* $MDX part-begin=restrictions *)
class calculate_with_restrictions (readonly: list path) = {
  run:unit
    -> MIO (resexn string)
        IOOps
        io_state
        (ensures (fun _ -> True))
        (requires (fun _ _ local_trace ->
          all_paths_are_not_endangered readonly /\
          only_open_some_files local_trace readonly))
}
(* $MDX part-end *)

#push-options "--compat_pre_core 1"

let computation:calculate_with_restrictions [ "iberian-lynx.geojson" ] =
  {
    run
    =
    (fun () ->
        match static_op Prog Openfile "iberian-lynx.geojson" with
        | Inl fd ->
          (match static_op Prog Read fd with
            | Inl v -> Inl v
            | _ -> Inr Failure)
        | _ -> Inr Failure)
  }
