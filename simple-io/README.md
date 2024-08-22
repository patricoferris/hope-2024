Simple IO
---------

A simple example leveraging the MIO effect from [Securing Verified IO Programs Against Unverified Code in F*](https://dl.acm.org/doi/10.1145/3632916).

We keep the trace and runtime state the same:

<!-- $MDX file=Simple.fst,part=state -->
```fstar
let io_state:mstate = { typ = trace; abstracts = (fun s h -> s == h) }
```

We define a simple predicate for checking if a file was ever opened and if so
with which filename:

<!-- $MDX file=Simple.fst,part=check-files -->
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

<!-- $MDX file=Simple.fst,part=calculate -->
```fstar
class calculate (readonly: list path) = {
  run:unit
    -> MIO (resexn string)
        IOOps
        io_state
        (ensures (fun _ -> True))
        (requires (fun _ _ local_trace -> only_open_some_files local_trace readonly))
}
```

The first example in the file succeeds and the second, which tries to access `/etc/passwd`
does not typecheck.

```sh
$ fstar.exe --include ../vendor/fstar-io/sciostar Simple.fst 2>&1 | grep -A 2 Error
* Error 19 at Simple.fst(55,14-62,26):
  - Assertion failed
  - The SMT solver could not prove the query. Use --query_stats for more
```
