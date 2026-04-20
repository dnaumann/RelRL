# Utility API Reference

## util/lib.ml

General utility functions.

### List Utilities

```ocaml
val concat_map : ('a -> 'b list) -> 'a list -> 'b list
val foldr : ('a -> 'b -> 'b) -> 'b -> 'a list -> 'b
val mapr : ('a -> 'b) -> 'a list -> 'b list
val last : 'a list -> 'a
val range : int -> int -> int list
val zip : 'a list -> 'b list -> ('a * 'b) list
```

### Option Utilities

```ocaml
val opt_map : ('a -> 'b) -> 'a option -> 'b option
val opt_to_list : 'a option -> 'a list
val filter_some : 'a option list -> 'a list
```

### Result Monad

```ocaml
type 'a t = Ok of 'a | Error of string

val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t

val to_option : 'a t -> 'a option
val of_option : 'a option -> string -> 'a t

val iter : ('a -> unit) -> 'a t -> unit
val map : ('a -> 'b) -> 'a t -> 'b t
```

### String Utilities

```ocaml
val starts_with : string -> string -> bool
val ends_with : string -> string -> bool
val capitalize : string -> string
val lowercase : string -> string
val join : string -> string list -> string
```

### Map Module

```ocaml
module M : sig
  type key = Ast.ident
  type 'a t

  val empty : 'a t
  val add : key -> 'a -> 'a t -> 'a t
  val find : key -> 'a t -> 'a
  val find_opt : key -> 'a t -> 'a option
  val remove : key -> 'a t -> 'a t
  val iter : (key -> 'a -> unit) -> 'a t -> unit
  val map : ('a -> 'b) -> 'a t -> 'b t
  val bindings : 'a t -> (key * 'a) list
end
```

### Set Module

```ocaml
module S : sig
  type elt = string
  type t

  val empty : t
  val add : elt -> t -> t
  val remove : elt -> t -> t
  val mem : elt -> t -> bool
  val iter : (elt -> unit) -> t -> unit
end
```

---

## util/why3util.ml

Why3 parse tree construction helpers.

### Identifier Construction

```ocaml
val mk_ident : string -> Why3.Ptree.ident
val mk_qualid : string list -> Why3.Ptree.qualid
```

### Type Construction

```ocaml
val mk_tvar : string -> Why3.Ptree.expr
val mk_tclass : string -> Why3.Ptree.expr
val mk_tarrow : Why3.Ptree.expr -> Why3.Ptree.expr -> Why3.Ptree.expr
```

### Term/Expression Construction

```ocaml
val mk_const : Why3.Number.number -> Why3.Ptree.expr
val mk_int : int -> Why3.Ptree.expr
val mk_bool : bool -> Why3.Ptree.expr
val mk_var : string -> Why3.Ptree.expr

val mk_binop : Ast.binop -> Why3.Ptree.expr -> Why3.Ptree.expr -> Why3.Ptree.expr
val mk_unop : Ast.unrop -> Why3.Ptree.expr -> Why3.Ptree.expr
val mk_app : Why3.Ptree.expr -> Why3.Ptree.expr list -> Why3.Ptree.expr
```

### Formula Construction

```ocaml
val mk_and : Why3.Ptree.term -> Why3.Ptree.term -> Why3.Ptree.term
val mk_or : Why3.Ptree.term -> Why3.Ptree.term -> Why3.Ptree.term
val mk_not : Why3.Ptree.term -> Why3.Ptree.term
val mk_impl : Why3.Ptree.term -> Why3.Ptree.term -> Why3.Ptree.term

val mk_forall : (string * Why3.Ptree.expr) list -> Why3.Ptree.term -> Why3.Ptree.term
val mk_exists : (string * Why3.Ptree.expr) list -> Why3.Ptree.term -> Why3.Ptree.term
```

### Declaration Construction

```ocaml
val mk_let : string -> Why3.Ptree.expr list -> Why3.Ptree.expr -> Why3.Ptree.decl
val mk_axiom : string -> Why3.Ptree.term -> Why3.Ptree.decl
val mk_lemma : string -> Why3.Ptree.term -> Why3.Ptree.decl
```
