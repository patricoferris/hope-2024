Simple IO
---------

A simple example leveraging the MIO effect from [Securing Verified IO Programs Against Unverified Code in F*](https://dl.acm.org/doi/10.1145/3632916).

We keep the trace and runtime state the same:

<!-- $MDX file=Model.fst,part=state -->
```fstar
let io_state:mstate = { typ = trace; abstracts = (fun s h -> s == h) }
```

We define a simple predicate for checking if a file was ever opened and if so
with which filename:

<!-- $MDX file=Model.fst,part=check-files -->
```fstar
let rec only_open_some_files (ev: list event) (files: list path) =
  match ev with
  | EOpenfile _ args _ :: rest ->
    let fnm = args in
    fnm `mem` files && only_open_some_files rest files
  | _ :: ts -> only_open_some_files ts files
  | [] -> true
```

And now a typeclass that we require all calculations to conform too. There isn't any particular reason this has to be typeclass here.

<!-- $MDX file=Model.fst,part=calculate -->
```fstar
class calculate (readonly: list path) = {
  run:unit
    -> MIO (resexn string)
        IOOps
        io_state
        (ensures (fun _ -> True))
        (requires (fun _ _ local_trace -> 
          dont_delete_any_file local_trace /\
		  only_open_some_files local_trace readonly))
}
```

The first example in the file succeeds as the implementation only uses the `result.txt` file.

<!-- $MDX file=Model.fst,part=computation -->
```fstar
let computation:calculate ["result.txt"] =
  {
    run
    =
    (fun () ->
        match static_op Prog Openfile "result.txt" with
        | Inl fd ->
          (match static_op Prog Read fd with
            | Inl v -> Inl v
            | _ -> Inr Failure)
        | _ -> Inr Failure)
  }
```

The second example , which tries to access `/etc/passwd`, does not typecheck.

<!-- $MDX file=Model.fst,part=failing_computation -->
```fstar
let failing_computation:calculate ["result.txt"] =
  {
    run
    =
    (fun () ->
        let _sfd = static_op Prog Openfile "/etc/passwd" in
        match static_op Prog Openfile "result.txt" with
        | Inl fd ->
          (match static_op Prog Read fd with
            | Inl v -> Inl v
            | _ -> Inr Failure)
        | _ -> Inr Failure)
  }
```

```sh
$ fstar.exe --include ../vendor/fstar-io/sciostar Model.fst 2>&1 | grep -A 2 Error
* Error 19 at Model.fst(68,14-75,26):
  - Assertion failed
  - The SMT solver could not prove the query. Use --query_stats for more
```
