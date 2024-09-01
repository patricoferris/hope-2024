Simple JSON
-----------

This example takes the [simple-io](../simple-io/README.md) example and adds a proof of concept
JSON-reasoning to protect computations from reading "endangered" species. 

<!-- $MDX file=./Json.fst,part=is_endangered -->
```fstar
(* Following IUCN's Globally Endangered (GE) scoring *) 
let is_endangered (j : json) = contains_field_value j "rarity" (function Int i -> i >= 3 | _ -> false)

let _ = assert (is_endangered (String "foo") = false)
let _ = assert (is_endangered (O [ "rarity", Int 2 ]) = false)
let _ = assert (is_endangered (A [(O [ "rarity", Int 3])]) = true)

(* https://www.iucnredlist.org/ *)
let datamap = [
  "iberian-lynx.geojson", O [ "rarity", Int 2 ];
  "bornean-elephant.geojson", O [ "rarity", Int 3 ]
]
```

We implement a simple check for the key-value pair that indicates whether or not a specific
species is [endangered](https://www.iucnredlist.org) or not. We can then add that to our reasoning
on what a specific implementation can safely use.

<!-- $MDX file=./Json.fst,part=restrictions -->
```fstar
class calculate_with_restrictions (readonly: list path) = {
  run:unit
    -> MIO (resexn string)
        IOOps
        io_state
        (ensures (fun _ -> True))
        (requires (fun _ _ local_trace ->
		dont_delete_any_file local_trace /\
          all_paths_are_not_endangered readonly /\
          only_open_some_files local_trace readonly))
}
```

And then catch instances where readonly paths are not for a known non-endangered species.

<!-- $MDX file=./Jsonfail.fst,part=failure -->
```fstar
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
```

And then compiled.

```sh
$ fstar.exe --include ../vendor/fstar-io/sciostar --include ../simple-io Json.fst 2>&1 | grep "All"
All verification conditions discharged successfully
$ fstar.exe  --include ../vendor/fstar-io/sciostar --include ../simple-io Jsonfail.fst 2>&1  | grep -A 2 Error
* Error 19 at Jsonfail.fst(14,8-22,26):
  - Assertion failed
  - The SMT solver could not prove the query. Use --query_stats for more
```

We can also protect against malicious (or accidental) unlinking of files!

```sh
$ fstar.exe --include ../vendor/fstar-io/sciostar --include ../simple-io Jsonfail2.fst  2>&1  | grep -A 2 Error
* Error 19 at Jsonfail2.fst(14,5-16,24):
  - Assertion failed
  - The SMT solver could not prove the query. Use --query_stats for more
```

Of course, there are many hoops to jump through to make this more realisitic:

 - Heading towards allowing type-checking / proof-checking to do a lot of computation 
   including potentially IO and reasoning dynamically which could also be a potential
   leak! 
 - Linking parsed JSON to a specific file read and open
