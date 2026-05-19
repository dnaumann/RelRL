{0:top Ego}

Ego (EGraphs OCaml) is an OCaml library that provides generic equality
saturation using EGraphs. The design of Ego loosely follows the
design of Rust's egg library, providing a flexible interface to run
equality saturation extended with custom user-defined analyses.

{[
(* create an egraph *)
let graph = EGraph.init ()
(* add expressions *)
let expr1 = EGraph.add_sexp graph [%s ((a << 1) / 2)]
(* Convert to graphviz *)
let g : Odot.graph = EGraph.to_dot graph
]}



The rest of this page will provide a quick-start guide to using
{{:#top}Ego}. Advanced users may instead want to check out the {{!Ego}API documentation}.

{1:library-overview Library overview}

{{:#top}Ego} provides two interfaces to its equality saturation
engine:

 1. {!Ego.Basic} - an out-of-the-box interface to pure equality
 saturation (i.e supporting only syntactic rewrites).

 2. {!Ego.Generic} - a higher order interface to equality saturation,
 parameterised over custom user defined analyses.
 
{1:getting-started Getting Started with Ego}

In the rest of this section, we'll provide a small walkthrough of
using {{:#top} Ego} to implement a variety of program transformations
using egraphs.

{2:basic-interface Basic EGraphs with Ego}
The basic interface to {{:#top}Ego} lives under {!Ego.Basic}:
{[
open Ego.Basic
]}


{!Ego.Basic} provides a simple equality-saturation engine that just
works "out-of-the-box" - it isn't particularly extensible or
customisable, but this means that it is a good place to start
experimenting with EGraphs.

Let's start with by creating a new EGraph using {!Ego.Basic.EGraph.init}:
{[
let graph = EGraph.init ()
]}

The equality saturation engine defined in {!Ego.Basic} operates over
[s-expressions] - so to simplify some of the code in this section, our
examples will be using a custom (unpublished) ppx to convert OCaml
expressions into [Sexp]s.

{3:basic-nodes Adding nodes}
Let's start by creating a new expression:
{[
let expr = [%s ((a << 1) / 2)]
]}
{i If you're following along at home, this is equivalent to the following:}
{[
let expr =
    let open Sexplib0.Sexp in
    List [Atom "/"; List [Atom "<<"; Atom "a"; Atom "1"]; Atom "2"]
]}

We can now add this expression to our EGraph:
{[
let expr_id = EGraph.add_sexp graph expr
]}

{3:basic-printing Printing EGraphs}

Internally, [EGraph]s operate by tracking equivalence classes over
sub-expressions - to help with debugging, we can view the state of our
[EGraph] using the helper functions {!Ego.Basic.EGraph.to_dot}, which returns a
Graphviz respresentation of the current state of the EGraph.
{[
let g : Odot.graph = EGraph.to_dot graph
]}

If we convert this Graphviz representation [g] to a string using
[Odot.string_of_graph] and pass it to Graphviz's [dot] command
(externally), we get the following diagram:


As we can see, the EGraph now contains the expression we fed into it,
and each node in the expression has also been assigned a unique
equivalence class.

Because EGraphs track the structural equivalences between nodes, if
you add any terms that are sub-expressions of nodes that are already
in the EGraph, then the graph does not change.

Try this out for yourself with the expression [(a << 1)]!

{3:basic-rules Defining rewrites}

Adding nodes is nice and all, but the real magic of EGraphs is with {b
rewrites} - expressing transformations of the program source code in
terms of equivalences between terms.

We express {i rewrites} in Ego through two components: {!Ego.Basic.Query}s and
{!Ego.Basic.Rule}s.

 - A [Query] represents a pattern over the term language that
   destructs an expression and binds its subexpressions to variables.

 - A [Rule] is a pair of [Query]s - a {b from} query, that matches
   subexpressions in the term language, and an {b into} query that
   then rearranges the subexpressions bound in the from query.

Let's build a rule to transform expressions of the form [a << 1] into [a * 2].

We can build our from pattern using {!Ego.Basic.Query.of_sexp}:

{[
let from = Query.of_sexp [%s ("?a" << 1)]
]}

Here, by prefixing the variable with ["?"] to get ["?a"], we denote a
pattern variable that binds to a subexpression rather than being
matched literally.

Next, let's construct the into pattern, which then just updates the
matched expression to use a multiplication:

{[
let into = Query.of_sexp [%s ("?a" * 2)]
]}

With these two patterns defined, we can combine them into a rewrite rule using [Rule.make]:

{[
let rule = Rule.make ~from ~into
]}

Once we have a rule, the EGraph can then {i efficiently} enact the
corresponding transformation by {i merging} the equivalence classes
associated with the matched and transformed subexpressions.

As this change may then reveal other subexpressions that could be also
rewritten, we may be able to repeat the rewrite multiple times.

{{:#top}Ego} exposes two methods to execute rewrite rules:
{!Ego.Basic.EGraph.apply_rules} or {!Ego.Basic.EGraph.run_until_saturation}.
 
 - [EGraph.apply_rules graph rules] simply runs each one of the
   rewrites in [rules] exactly once.

 - [EGraph.run_until_saturation ?fuel graph rules] repeatedly each one
   of the rewrites in [rules] until no further changes occur ({i i.e
   equality saturation }), or until it runs out of [fuel].

Our current rewrite system is fairly small - let's just run the rules
until saturation without any explicit fuel limit:

{[
let _ = run_until_saturation graph [rule]
]}

Let's have a look at the resulting EGraph structure:
 

Indeed, as we can see above, the EGraph has now merged the eclass
previously for the subexpression with lshift [a << 1] with the eclass for
the subexpression with multiplication [a * 2].

{3:basic-extraction Extracting nodes}

Finally, in order to pull an expression back out of the EGraph,
{{:#top}Ego} provides the function {!Ego.Basic.EGraph.extract}, which when
given a cost function and a term id, returns the lowest-cost
equivalent expression.
{[
val extract : ((Ego.Id.t -> float) -> Symbol.t * Ego.Id.t list -> float) -> EGraph.t -> Ego.Id.t -> Sexplib0.Sexp.t
]}

The extraction function takes two parameters [score] and [node]:

  - A scoring function [score] that returns the scores of the children
    of the current node

  - The [node] to be scored, represented as a pair: the operator of
    the node, and a list of ids corresponding to its children.

Let's write a simple cost function that places higher cost on shifts and lower cost on multiplications:

{[
let cost_function score (sym, children) =
  let node_score = 
    match Symbol.to_string sym with
    | "*" -> 1.
    | "/" -> 1.
    | "<<" -> 2.
    | _ -> 0. in
  node_score +. List.fold_left (fun acc vl -> acc +. score vl) 0. children
]}

With a scoring function in hand, we can now try and pull out an equivalent expression to our initial term [(/ (<< a 1) 2)]:

{[
let result = EGraph.extract cost_function graph expr_id
(* (/ (* a 2) 2) *)
]}

Tada! Equality saturation Ladies and Gents.

{2:advanced-interface Eclass Analysis with Ego}

Now that we've seen the basics of how equality saturation works, let's
have a look at {{:#top}Ego}'s advanced analysis interface.

{3:advanced-langauge Defining a language}

Unlike the basic interface which operates over arbitrary
S-expressions, {{:#top}Ego}'s generic EGraph framework is
parameterised over an arbitrary definition of a language.

We can specify this language by defining a module satisfying the
{!Ego.Generic.LANGUAGE} interface.

As such, let's start creating a module to define our language.

{[
module L = struct
]}

The first type we'll need to supply is a polymorphic type ['a shape], that
captures the {i shape} of the expression langauge, with the type
parameter ['a] encoding recursive occurances:

{[
type 'a shape =
  | Add of 'a * 'a
  | Sub of 'a * 'a
  | Mul of 'a * 'a
  | Div of 'a * 'a
  | Var of string
  | Const of int
[@@deriving ord]
]}

Here, we've defined a basic numerical language consisting of addition,
subtraction, multiplication and division over integers and variables.
We also use [ppx_deriving] to derive an abitrary order over
expressions - this ordering doesn't need to have any semantic meaning,
and is just there for efficiently storing terms of the language.

We'll also define a basic pretty printer for ['a shape]:

{[
let pp f fmt = function
  | Add (l,r) -> Format.fprintf fmt "(%a + %a)" f l f r
  | Sub (l,r) -> Format.fprintf fmt "(%a - %a)" f l f r
  | Mul (l,r) -> Format.fprintf fmt "(%a * %a)" f l f r
  | Div (l,r) -> Format.fprintf fmt "(%a / %a)" f l f r
  | Const n -> Format.fprintf fmt "%d" n
  | Var s -> Format.fprintf fmt "%s" s
]}

In order to convert this shape datatype ['a shape] into a form that
represents concrete terms from our language we can "tie-the-knot"
using a new datatype [t]:

{[
type t = Mk of t shape
]}

Next, we need to define a type of tags [op] that uniquely identify
each constructor and its non-recursive data:

{[
type op = AddOp | SubOp | MulOp | DivOp | VarOp of string | ConstOp of int [@@deriving eq]

let op : 'a shape -> op = function
  | Add _ -> AddOp
  | Sub _ -> SubOp
  | Mul _ -> MulOp
  | Div _ -> DivOp
  | Var s -> VarOp s
  | Const i -> ConstOp i
]}

Additionally, given an op and an appropriate number of children, we
should be able to recreate the corresponding ['a shape]

{[
let make : op -> 'a list -> 'a shape = fun op ls ->
  match[@warning "-8"] op,ls with
  | AddOp, [l;r] -> Add (l,r)
  | SubOp, [l;r] -> Sub (l,r)
  | MulOp, [l;r] -> Mul (l,r)
  | DivOp, [l;r] -> Div (l,r)
  | VarOp s, [] -> Var s
  | ConstOp i, [] -> Const i
]}

Finally, We also need to define some generic operations to manipulate nodes in
terms of their children:

{[
let children : 'a shape -> 'a list = function
  | Add (l,r) | Sub (l,r) | Mul (l,r) | Div (l,r) -> [l;r]
  | Var _ | Const _ -> []

let map_children : 'a shape -> ('a -> 'b) -> 'b shape = fun term f -> match term with
  | Add (l,r) -> Add (f l, f r)
  | Sub (l,r) -> Sub (f l, f r)
  | Mul (l,r) -> Mul (f l, f r)
  | Div (l,r) -> Div (f l, f r)
  | Var s -> Var s
  | Const i -> Const i
]}

This completes our definition of the language.

{[
end
]}

By separating out expressions into ['a shape] and their discriminants
[op], this allows the EGraph framework to efficiently reason about the
{b shape} of expressions {i independently} from their children.

{3:advanced-analysis Defining an analysis}

Loosely following Rust's egg library, {{:#top}Ego} allows users to run
EClass analyses over its EGraphs - the idea here is that we can attach
additional information to the equivalence classes in our EGraph, and
then use this to perform more complex rewrites in a principaled way.

We can define EClass analyses in {{:#top}Ego} in two steps:

+ First, we express the data used in our analysis by supplying a
module satisfying the {!Ego.Generic.ANALYSIS} interface.

+ Second, we define the operations over this data through a functor
  satisfying {!Ego.Generic.ANALYSIS_OPS} that receives an interface to
  the EGraph as a module satisfying {!Ego.Generic.GRAPH_API}.

Sounds complicated? Well, don't worry! With a bit of experience, this
will quickly become second nature - let's have a look at using this
interface to implement a {b constant folding} analysis.

We can start by specifying the data for our analysis as below:

{[
module A = struct

  type t = unit

  type data = int option [@@deriving eq, show]

end
]}

In the module above, the type [data] represents the additional
analysis information that we will be attached to each EClass, and the
type [t] represents any persistent state that our analysis may need to
track separately from each eclasses - in this case, we don't have any
additional information, so we just leave it empty.

With the analysis data defined, we can next move on to defining the
analysis operations. To do this, We start by defining a functor that
takes in a module satisfying the {{:#top}Ego}'s
{!Ego.Generic.GRAPH_API} interface:

{[
module MA (S : GRAPH_API
           with type 'p t = (Ego.Id.t L.shape, A.t, A.data, 'p) egraph
           and type analysis := A.t
           and type data := A.data
           and type node := L.t)  = struct
]}

The module [S] represents the interface to the EGraph available to the
analysis:

{[
module S: sig
  type 'p t = (Ego.Id.t L.shape, unit, A.data, 'p) egraph
  val freeze : rw t -> ro t
  val set_data : rw t -> Ego.Id.t -> A.data -> unit
  val get_data : ro t -> Ego.Id.t -> A.data
  val get_analysis : rw t -> A.t
  val add_node : rw t -> L.t -> Ego.Id.t
  val merge : rw t -> Ego.Id.t -> Ego.Id.t -> unit
end
]}

For convenience, the operations over the EGraph are split into those
which {b read and write} to the graph [rw t] and those that are {b
read-only} [ro t]. When defining the analysis operations, certain
operations assume that the graph is not modified, so these anotations
will help users to avoid violating the internal invariants of the data
structure.

Now, before we define our analysis, we'll first define a small helper
{i abstract} evaluation function, that evaluates the values of
expressions over our domain:

{[
let eval : A.data L.shape -> A.data =
  function
  | L.Add (Some l, Some r)  -> Some (l + r)
  | L.Sub (Some l, Some r) -> Some (l - r)
  | L.Mul (Some l, Some r) -> Some (l * r)
  | L.Div (Some l, Some r) -> if r <> 0 then Some (l / r) else None
  | L.Const n -> Some n
  | _ -> None
]}

With this definition in hand, we're now ready to define the
analysis. To do so, we'll need to define three functions:

- A [make] operation, which is called whenever a new node is added and
  should generate a new abstract value for the node, usually using the
  abstract values of its children.

- A [merge] operation, which is called whenever two equivalance
  classes are merged and should produce a new abstract value that
  represents the merge of their corresponding abstract values.

- A [modify] operation, which is called whenever the children or
  abstract values of an eclass are modified and may use the abstract
  value of its to modify the egraph.

Let's have a look at the implementation of each one of these
operations for our constant folding analysis.

Our [make] operation simply reuses our abstract evaluation function,
and determines the value of the new node by evaluating the operation
over the values of its children if they are constant:

{[
let make : ro t -> Ego.Id.t L.shape -> A.data =
  fun graph term ->
  eval (L.map_children term (S.get_data graph))
]}

Next, whenever two eclasses are merged, the [merge] operation simply
propagates the constants known for either of the eclasses:

{[
let merge : A.t -> A.data -> A.data -> A.data =
  fun () l r ->  match l,r with
    | Some l, _ -> Some l
    | _, Some r -> Some r
    | _ -> None
]}

Finally, the [modify] operation tracks the constant values of terms
and adds the corresponding constant terms to the graph if known:

{[
let modify : rw t -> Ego.Id.t -> unit = fun graph cls ->
  match S.get_data (S.freeze graph) cls with
  | None -> ()
  | Some n ->
    let nw_cls = S.add_node graph (L.Mk (Const n)) in
    S.merge graph nw_cls cls
]}

This completes the definition of our constant folding analysis.

{[
end
]}

Putting it all together, we can now create the EGraph using
{{:#top}Ego}'s {!Ego.Generic.Make} functor:

{[
module EGraph = Make (L) (A) (MA)
]}

Let's try it out!

First, let's create a new EGraph as we did using the {{:#basic-interface} basic interface}:

{[
let graph = EGraph.init ()
]}

We can then add expressions to our EGraph as before:

{[
let expr = L.of_sexp [%s (2 * 2)]
]}

{i Here we're using an ommited basic function to convert between
s-expressions and terms of our language.}

Finally, we can plot the EGraph using Graphviz as before:

{[
EGraph.to_dot graph
]}


As we can see, the EGraph has the usual structure, however we're now
also tracking our analysis information alongside each equivalence
class, and have also added new equivalences between certain
expressions and their corresponding constant values.

{3:advanced-extraction Extracting nodes}

Much like the {{:#basic-interface}basic interface}, we can also
extract expressions using {{:#top}Ego}'s generic EGraphs - in
particular by defining a module that satisfies the {!Ego.Generic.COST}
interface.

{[
module C = struct
]}

The cost interface is fairly straightforward.

We must first provide an ordered type to encode the cost of
expressions. Here, we'll use floats:

{[
type t = float [@@deriving ord]
]}

Next, we can define a cost function [cost] that computes the cost of
expressions:

{[
let cost f : Id.t L.shape -> t = function
  | L.Add (l, r) -> f l +. f r +. 1.0
  | L.Sub (l, r) -> f l +. f r +. 1.0
  | L.Mul (l, r) -> f l +. f r +. 1.0
  | L.Div (l, r) -> f l +. f r +. 1.0
  | L.Var _ -> 1.0
  | L.Const _ -> 1.0
]}

This completes the cost interface.

{[
end
]}

We can build an expression extractor using the
{!Ego.Generic.MakeExtractor} interface:

{[
module Extractor = MakeExtractor (L) (C)
]}

Finally, let's extract an expression:

{[
Extractor.extract graph expr_id
(* 4 *)
]}

Tada! EClass Analysis Ladies and Gents!

{1:other-stuff Other cool stuff}

There are a few parts of the API that we haven't had a chance to cover
in this quick-start guide - in particular, the rewrite system for the
{{:#advanced-interface} generic interface}.

{{:#top}Ego} also provides support for rewrites through the
{!Ego.Generic.RULE} interface implemented by
{!Ego.Generic.Make.Rule}.

Unlike the {{:#basic-interface}basic interface}, alongside supporting
purely syntactic rewrites ({!Ego.Generic.RULE.make_constant}), the
generic interface allows for rewrites that can condition on the
information the analysis ({!Ego.Generic.RULE.make_conditional}), or
even dynamically generate the transformation patterns
({!Ego.Generic.RULE.make_dynamic}).

We don't currently have a guide of how to define these kinds of
rewrites, but may add an additional section in the future.

Have fun and Happy hacking!