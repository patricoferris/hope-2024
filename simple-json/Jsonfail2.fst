module Jsonfail2

open Compiler.Model1
open Model
open Json

#push-options "--compat_pre_core 1"
(* $MDX part-begin=failure *)
let computation3:calculate_with_restrictions [ "iberian-lynx.geojson" ] =
  {
    run
    =
    (fun () ->
     match static_op Prog Unlink "iberian-lynx.geojson" with
	 | Inl b -> if b then Inl "done" else Inr Failure
	 | Inr _ -> Inr Failure)
  }
(* $MDX part-end *)