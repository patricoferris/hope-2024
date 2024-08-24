module Jsonfail

open Model
open Compiler.Model1
open Json

#push-options "--compat_pre_core 1"
(* $MDX part-begin=failure *)
let computation2:calculate_with_restrictions [ "iberian-lynx.geojson"; "bornean-elephant.geojson" ] =
  {
    run
    =
    (fun () ->
        match
          static_op Prog Openfile "iberian-lynx.geojson",
          static_op Prog Openfile "bornean-elephant.geojson"
        with
        | Inl fd, Inl fd2 ->
          (match static_op Prog Read fd, static_op Prog Read fd2 with
            | Inl v, Inl v2 -> Inl (v ^ v2)
            | _ -> Inr Failure)
        | _ -> Inr Failure)
  }
(* $MDX part-end *)