# Coding Style Guide


### Naming Conventions
```ocaml
(* Type constructors: Capitalized *)
Tclass, Tint, Tmath, Trgn

(* Values: lowercase *)
int_ty, bool_ty, rgn_ty, unit_ty

(* Classes in Why3: Capitalized *)
Cell → "Cell", M::MyClass → "M_MyClass"

(* Fields in Why3: lowercase_class_field *)
Cell.value → "cell_value"

(* Methods: preserved from source *)
foo() → "foo"
```\

- **Naming**: Use snake_case for functions, lowercase modules
- **Type annotations**: Annotate non-trivial functions
- **Comments**: Document complex logic, especially in typing.ml and translate.ml
- **Error handling**: Use `Result` monad (defined in `lib.ml`)
- **Modules**: Split large modules into logical components with `.mli` interfaces
