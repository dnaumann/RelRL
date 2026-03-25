(** gensym.ml -- fresh name generation via local generator objects.

    Instead of module-level counter refs that require explicit reset calls,
    create a [t] at the start of each pass and let it be garbage-collected
    when the pass is done. This eliminates reset bugs entirely. *)

type t = { mutable count: int }

(** Create a new generator, starting at 0. *)
let create () = { count = 0 }

(** Generate a fresh name by appending a unique integer suffix to [base]. *)
let next (g: t) (base: string) : string =
  g.count <- g.count + 1;
  base ^ string_of_int g.count

(** Like [next], but keeps incrementing until the produced name satisfies
    [not (known name)]. Use this when the generated name must not collide
    with an existing set of names. *)
let next_not_in (g: t) (known: string -> bool) (base: string) : string =
  let rec loop () =
    let s = next g base in
    if known s then loop () else s
  in
  loop ()
