# Pre-translation API Reference

## pretrans/pretrans.ml

Pre-translation analysis and transformations.

### Main Entry Point

```ocaml
(* Process program environment with all analyses *)
val process : Ctbl.t -> penv -> penv
```

### Sub-modules

```ocaml
(* Expand specifications with invariants *)
module Expand_method_spec : sig
  val expand : penv -> penv
end

(* Validate encapsulation *)
module Encap_check : sig
  val check : Ctbl.t -> penv -> unit Result.t
end

(* Derive bimodule interfaces *)
module Derive_biinterface : sig
  val derive : penv -> penv
end

(* Resolve datagroup wildcards *)
module Resolve_datagroups : sig
  val resolve : penv -> penv
end

(* Generate frame lemmas *)
module Generate_frame_lemmas : sig
  val generate : penv -> penv
end
```

### Configuration

```ocaml
(* Control simplification *)
val simplify_effects : bool ref

(* Control which passes run — set via command-line flags *)
```
