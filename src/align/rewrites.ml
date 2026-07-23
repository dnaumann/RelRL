open Annot

(* Alignment rewrites over [Annot.bicommand].

   A [rewrite] is a partial transformation on a bicommand: [Some cc'] when it
   applies at the *root* of its argument, [None] otherwise.  Every rewrite below
   preserves the projections ([Annot.projl] / [Annot.projr]), so applying any
   sequence of them to a default (sequential) alignment yields another alignment
   of the same pair of unary programs -- only the synchronisation structure
   changes.  These mirror the weaving relation of Banerjee et al. (TOPLAS 2022). *)
type rewrite = bicommand -> bicommand option

(* -- Forward weaving (coarse alignment -> finer): introduce synchronisation -- *)

(* (Var x | Var y in (C | C'))  ~~>  Var x | y in (C | C')
   Lift a split of two variable declarations into a bi-declaration, sharing
   bi-program scope and exposing the bodies to further weaving. *)
let weave_vardecl : rewrite = function
  | Bisplit (Vardecl (lx, lm, lty, lb), Vardecl (rx, rm, rty, rb)) ->
    Some (Bivardecl (Some (lx, lm, lty), Some (rx, rm, rty), Bisplit (lb, rb)))
  | _ -> None

(* (C1;C2 | C1';C2')  ~~>  (C1 | C1') ; (C2 | C2') 
  split a bicom of sequences into a sequence of bicoms, aligning the two leading statements.  *)
let weave_seq : rewrite = function
  | Bisplit (Seq (l1, l2), Seq (r1, r2)) ->
    Some (Biseq (Bisplit (l1, r1), Bisplit (l2, r2)))
  | _ -> None

(* (A | A)  ~~>  |_ A _|
   collapse a split of two identical atomic commands into a
   single synchronised step.  Equality is structural equality on the atomic
   command -- the same test [Annot.eqv_command] uses for atomic commands. *)
let weave_sync : rewrite = function
  | Bisplit (Acommand a1, Acommand a2) when a1 = a2 -> Some (Bisync a1)
  | _ -> None

(* (if E then C1 else C2 | if E' then C1' else C2')
      ~~>  if E | E' then (C1 | C1') else (C2 | C2')
   assumes the two guards agree, pairing the
   then-branches and the else-branches.  (Diverging guards would instead call
   for the four-way [Biif4], which this rule deliberately does not introduce.) *)
let weave_if : rewrite = function
  | Bisplit (If (le, lt, lf), If (re, rt, rf)) ->
    Some (Biif (le, re, Bisplit (lt, rt), Bisplit (lf, rf)))
  | _ -> None

(* (if E then C1 else C2 | if E' then C1' else C2')
      ~~>  if E | E' then4 (C1|C1') (C1|C2') (C2|C1') (C2|C2')
   The honest four-way expansion: it does NOT assume the guards agree, pairing
   every combination of branches.  Sound and adequate unconditionally (whereas
   [weave_if] collapses to the two-way [Biif] under a guard-agreement proof
   obligation).  Deliberately excluded from [auto_align] since it de-aligns. *)
let weave_if4 : rewrite = function
  | Bisplit (If (le, lt, lf), If (re, rt, rf)) ->
    Some (Biif4 (le, re,
                 { then_then = Bisplit (lt, rt);
                   then_else = Bisplit (lt, rf);
                   else_then = Bisplit (lf, rt);
                   else_else = Bisplit (lf, rf) }))
  | _ -> None

(* Lockstep loop alignment *)
let default_align_guard : alignment_guard = (Rleft Ffalse, Rright Ffalse)

(* Convert the two loops' *unary* invariants into bi-invariants: an invariant
   present (syntactically) on both sides becomes [Rboth] (it holds of both
   states), a left-only one becomes [Rleft], a right-only one [Rright].  This is
   projection-safe (projl/projr recover the original side's invariants, with the
   other side's projecting to Ftrue) and means weaving a loop no longer discards
   the invariants the unary loops were verified with. *)
let lift_unary_invariants (ls : while_spec) (rs : while_spec) : rformula list =
  let li = ls.winvariants and ri = rs.winvariants in
  List.map (fun f -> Rboth f)  (List.filter (fun f -> List.mem f ri) li)
  @ List.map (fun f -> Rleft f)  (List.filter (fun f -> not (List.mem f ri)) li)
  @ List.map (fun f -> Rright f) (List.filter (fun f -> not (List.mem f li)) ri)

(* Build a [biwhile_spec] from the two loops' specs: lift the invariants, pair
   the frames, and leave the (relational) variant for the user. *)
let biwhile_spec_of (ls : while_spec) (rs : while_spec) : biwhile_spec =
  { biwinvariants = lift_unary_invariants ls rs;
    biwframe = (ls.wframe, rs.wframe);
    biwvariant = None }

(* (while E do C | while E' do C')
      ~~>  while E | E' . <false | false> do (C | C')
   carrying the unary invariants/frames across (lockstep guard). *)
let weave_while : rewrite = function
  | Bisplit (While (le, ls, lb), While (re, rs, rb)) ->
    Some (Biwhile (le, re, default_align_guard, biwhile_spec_of ls rs,
                   Bisplit (lb, rb)))
  | _ -> None

(* Like [weave_while] but with a caller-supplied alignment guard. *)
let weave_while_guard (ag : alignment_guard) : rewrite = function
  | Bisplit (While (le, ls, lb), While (re, rs, rb)) ->
    Some (Biwhile (le, re, ag, biwhile_spec_of ls rs, Bisplit (lb, rb)))
  | _ -> None

(* ---- Relational invariant suggestion -------------------------------------- *)

(* A typed variable occurrence. *)
let evar (x : ident t) : exp t = (Evar x) -: x.ty

(* Typed [Evar] occurrences in an expression. *)
let rec evars_of_exp (e : exp t) : exp t list =
  match e.node with
  | Evar _ -> [e]
  | Econst _ -> []
  | Ebinop (_, a, b) -> evars_of_exp a @ evars_of_exp b
  | Eunrop (_, a) | Esingleton a | Einit a -> evars_of_exp a
  | Eimage (a, _) | Esubrgn (a, _) -> evars_of_exp a
  | Ecall (_, args) -> List.concat (List.map evars_of_exp args)

(* Typed [Evar] occurrences (read or written) in a command. *)
let rec evars_of_command (c : command) : exp t list =
  match c with
  | Acommand ac -> evars_of_atomic ac
  | Seq (a, b) -> evars_of_command a @ evars_of_command b
  | If (e, a, b) -> evars_of_exp e @ evars_of_command a @ evars_of_command b
  | While (e, _, body) -> evars_of_exp e @ evars_of_command body
  | Vardecl (_, _, _, body) -> evars_of_command body
  | Assume _ | Assert _ -> []
and evars_of_atomic : atomic_command -> exp t list = function
  | Skip -> []
  | Assign (x, e) | Field_update (x, _, e) | New_array (x, _, e) -> evar x :: evars_of_exp e
  | Havoc x | New_class (x, _) -> [evar x]
  | Field_deref (y, x, _) -> [evar y; evar x]
  | Array_access (x, a, e) -> evar x :: evar a :: evars_of_exp e
  | Array_update (a, i, e) -> evar a :: (evars_of_exp i @ evars_of_exp e)
  | Call (xo, _, args) ->
    (match xo with Some x -> [evar x] | None -> []) @ List.map evar args

let var_name (e : exp t) : ident option = match e.node with Evar x -> Some x.node | _ -> None

(* Candidate relational invariants for a loop pair: agreement [v =:= v] for each
   variable that occurs in both loops (guard or body).  These are *candidates*,
   not proven invariants -- some (e.g. a counter that drifts) will not hold; the
   user keeps the ones the relational spec needs.  Variables found only in one
   loop are dropped.  Deduplicated by name; built from the left occurrence. *)
let couplings (le : exp t) (lb : command) (re : exp t) (rb : command) : rformula list =
  let lvars = evars_of_exp le @ evars_of_command lb in
  let rnames = List.filter_map var_name (evars_of_exp re @ evars_of_command rb) in
  let seen = Hashtbl.create 16 in
  List.filter_map (fun ev ->
      match var_name ev with
      | Some n when List.mem n rnames && not (Hashtbl.mem seen n) ->
        Hashtbl.add seen n (); Some (Rbiequal (ev, ev))
      | _ -> None)
    lvars

let coupling_candidates : bicommand -> rformula list = function
  | Bisplit (While (le, _, lb), While (re, _, rb)) -> couplings le lb re rb
  | Biwhile (le, re, _, _, body) -> couplings le (projl body) re (projr body)
  | _ -> []

(* Add a relational invariant to a [Biwhile]. *)
let add_invariant (inv : rformula) : rewrite = function
  | Biwhile (e, e', ag, sp, cc) ->
    Some (Biwhile (e, e', ag, { sp with biwinvariants = inv :: sp.biwinvariants }, cc))
  | _ -> None

(* Remove the first occurrence of [inv] from a [Biwhile]'s invariant list. *)
let remove_invariant (inv : rformula) : rewrite = function
  | Biwhile (e, e', ag, sp, cc) ->
    let invs' = List.filter (( <> ) inv) sp.biwinvariants in
    if List.length invs' = List.length sp.biwinvariants then None
    else Some (Biwhile (e, e', ag, { sp with biwinvariants = invs' }, cc))
  | _ -> None

(* Replace the alignment guards of a [Biwhile] with [ag]. *)
let change_ag (ag : alignment_guard) : rewrite = function
  | Biwhile (e, e', _, sp, cc) -> Some (Biwhile (e, e', ag, sp, cc))
  | _ -> None

(* Insert a relational assert after/before the focus.  Used to seed proof
   hints (e.g. literal lemma instances) when /verify reports unproven goals.
   Biassert projects to skip on both sides, so projection checks are
   unaffected. *)
let add_assert_after (rf : rformula) : rewrite =
  fun cc -> Some (Biseq (cc, Biassert rf))

let add_assert_before (rf : rformula) : rewrite =
  fun cc -> Some (Biseq (Biassert rf, cc))

(* -- Inverse weaving (finer alignment -> coarser): remove synchronisation -- *)

(* (C1 | C1') ; (C2 | C2')  ~~>  (C1;C2 | C1';C2')   -- inverse of [weave_seq] *)
let unweave_seq : rewrite = function
  | Biseq (Bisplit (l1, r1), Bisplit (l2, r2)) ->
    Some (Bisplit (Seq (l1, l2), Seq (r1, r2)))
  | _ -> None

(* |_ A _|  ~~>  (A | A)   -- inverse of [weave_sync] *)
let unsync : rewrite = function
  | Bisync a -> Some (Bisplit (Acommand a, Acommand a))
  | _ -> None

(* (C | C')  ~~>  (C | skip) ; (skip | C')  -- schedule left then right; neither side may already be skip *)
let skip_split : rewrite = function
  | Bisplit (Acommand Skip, _) | Bisplit (_, Acommand Skip) -> None
  | Bisplit (lc, rc) ->
    Some (Biseq (Bisplit (lc, Acommand Skip), Bisplit (Acommand Skip, rc)))
  | _ -> None

(* (a;rest | C')  ~~>  (a | skip) ; (rest | C')
   (a | C')       ~~>  skip_split                -- left is already atomic *)
let left_first : rewrite = function
  | Bisplit (Seq (Acommand a, rest), rc) ->
    Some (Biseq (Bisplit (Acommand a, Acommand Skip), Bisplit (rest, rc)))
  | Bisplit (Acommand _, _) as cc -> skip_split cc
  | _ -> None

(* (C | a;rest)  ~~>  (skip | a) ; (C | rest)
   (C | a)       ~~>  skip_split                -- right is already atomic *)
let right_first : rewrite = function
  | Bisplit (lc, Seq (Acommand a, rest)) ->
    Some (Biseq (Bisplit (Acommand Skip, Acommand a), Bisplit (lc, rest)))
  | Bisplit (_, Acommand _) as cc -> skip_split cc
  | _ -> None

(* (C | skip) ; (skip | D)  ~~>  (skip | D) ; (C | skip)
   commute a left-only step past the following right-only step.  Projection-safe:
   each side's projection is unchanged ([C;skip = skip;C] on the left,
   [skip;D = D;skip] on the right). *)
let lrc : rewrite = function
  | Biseq (Bisplit (lc, Acommand Skip), Bisplit (Acommand Skip, rc)) ->
    Some (Biseq (Bisplit (Acommand Skip, rc), Bisplit (lc, Acommand Skip)))
  | _ -> None

(* Named registry -- handy for an interactive user "which rewrites apply
   here?" query (see [suggest_at]). *)
let all_rewrites : (string * rewrite) list =
  [ "weave_vardecl", weave_vardecl;
    "weave_seq",     weave_seq;
    "weave_sync",    weave_sync;
    "weave_if",      weave_if;
    "weave_if4",     weave_if4;
    "weave_while",   weave_while;
    "unweave_seq",   unweave_seq;
    "unsync",        unsync;
    "skip_split",    skip_split;
    "left_first",    left_first;
    "right_first",   right_first;
    "lrc",           lrc ]

(* -- Focusing: apply a rewrite at a sub-term identified by a path ----------- *)

(* A [path] selects a sub-bicommand by indexing children top-down:
     Bivardecl (_,_,cc)          child 0 = cc
     Biseq (c1,c2)               child 0 = c1, child 1 = c2
     Biif  (_,_,c1,c2)           child 0 = then, child 1 = else
     Biif4 (_,_,{tt;te;et;ee})   children 0..3
     Biwhile (_,_,_,_,cc)        child 0 = cc
   Leaves (Bisplit, Bisync, Biassume, ...) have no children. *)
type path = int list

let child_count : bicommand -> int = function
  | Bivardecl _ | Biwhile _ -> 1
  | Biseq _ | Biif _ -> 2
  | Biif4 _ -> 4
  | Bisplit _ | Bisync _ | Biassume _ | Biassert _
  | Bihavoc_right _ | Biupdate _ -> 0

let get_child (cc: bicommand) (i: int) : bicommand =
  match cc, i with
  | Bivardecl (_, _, c), 0 -> c
  | Biwhile (_, _, _, _, c), 0 -> c
  | Biseq (c1, _), 0 -> c1
  | Biseq (_, c2), 1 -> c2
  | Biif (_, _, c1, _), 0 -> c1
  | Biif (_, _, _, c2), 1 -> c2
  | Biif4 (_, _, {then_then; _}), 0 -> then_then
  | Biif4 (_, _, {then_else; _}), 1 -> then_else
  | Biif4 (_, _, {else_then; _}), 2 -> else_then
  | Biif4 (_, _, {else_else; _}), 3 -> else_else
  | _ -> invalid_arg "Rewrites.get_child: index out of range"

let with_child (cc: bicommand) (i: int) (child': bicommand) : bicommand =
  match cc, i with
  | Bivardecl (x, y, _), 0 -> Bivardecl (x, y, child')
  | Biwhile (e, e', ag, sp, _), 0 -> Biwhile (e, e', ag, sp, child')
  | Biseq (_, c2), 0 -> Biseq (child', c2)
  | Biseq (c1, _), 1 -> Biseq (c1, child')
  | Biif (e, e', _, c2), 0 -> Biif (e, e', child', c2)
  | Biif (e, e', c1, _), 1 -> Biif (e, e', c1, child')
  | Biif4 (e, e', b), 0 -> Biif4 (e, e', { b with then_then = child' })
  | Biif4 (e, e', b), 1 -> Biif4 (e, e', { b with then_else = child' })
  | Biif4 (e, e', b), 2 -> Biif4 (e, e', { b with else_then = child' })
  | Biif4 (e, e', b), 3 -> Biif4 (e, e', { b with else_else = child' })
  | _ -> invalid_arg "Rewrites.with_child: index out of range"

(* Apply [r] at the sub-term reached by [path].  [None] if the path runs off the
   tree or the rewrite does not apply at the focus. *)
let rec apply_at (path: path) (r: rewrite) (cc: bicommand) : bicommand option =
  match path with
  | [] -> r cc
  | i :: rest ->
    if i < 0 || i >= child_count cc then None
    else begin
      match apply_at rest r (get_child cc i) with
      | Some child' -> Some (with_child cc i child')
      | None -> None
    end

(* The sub-bicommand reached by [path], if the path stays within the tree. *)
let rec subterm_at (path: path) (cc: bicommand) : bicommand option =
  match path with
  | [] -> Some cc
  | i :: rest ->
    if i < 0 || i >= child_count cc then None
    else subterm_at rest (get_child cc i)

(* The local variables in scope at [path]: the [Bivardecl] bindings passed
   through on the way down, split into (left, right).  Combined with the method
   parameters this is the typing context for a relational invariant at a loop. *)
let scope_at (path: path) (cc: bicommand) : varbind list * varbind list =
  let rec go path cc lacc racc =
    let lacc = match cc with Bivardecl (Some lv, _, _) -> lv :: lacc | _ -> lacc in
    let racc = match cc with Bivardecl (_, Some rv, _) -> rv :: racc | _ -> racc in
    match path with
    | [] -> (lacc, racc)
    | i :: rest ->
      if i < 0 || i >= child_count cc then (lacc, racc)
      else go rest (get_child cc i) lacc racc
  in
  go path cc [] []

(* All named rewrites that apply at [path], paired with their results -- the
   set of moves available at a given focus. *)
let suggest_at (path: path) (cc: bicommand) : (string * bicommand) list =
  List.filter_map
    (fun (name, r) ->
       match apply_at path r cc with
       | Some cc' -> Some (name, cc')
       | None -> None)
    all_rewrites

(* -- Greedy driver: weave a sequential bicom toward maximal lockstep -------- *)

(* Repeatedly apply the forward weaving rules, descending into the structure, to
   turn the default sequential alignment into the finest lockstep alignment the
   two programs' shared structure permits.  Statements that do not line up are
   left as a [Bisplit].  This is only a *suggested* alignment; the user refines
   it with the focused rewrites above. *)
let rec auto_align (cc: bicommand) : bicommand =
  match cc with
  | Bisplit (Vardecl _, Vardecl _) ->
    (match weave_vardecl cc with Some cc' -> auto_align cc' | None -> cc)
  | Bisplit (Seq _, Seq _) ->
    (match weave_seq cc with Some cc' -> auto_align cc' | None -> cc)
  | Bisplit (If _, If _) ->
    (match weave_if cc with Some cc' -> auto_align cc' | None -> cc)
  | Bisplit (While _, While _) ->
    (match weave_while cc with Some cc' -> auto_align cc' | None -> cc)
  | Bisplit (Acommand _, Acommand _) ->
    (match weave_sync cc with Some cc' -> cc' | None -> cc)
  | Bisplit _ -> cc
  | Bivardecl (x, y, c) -> Bivardecl (x, y, auto_align c)
  | Biseq (c1, c2) -> Biseq (auto_align c1, auto_align c2)
  | Biif (e, e', c1, c2) -> Biif (e, e', auto_align c1, auto_align c2)
  | Biif4 (e, e', b) -> Biif4 (e, e', map_fourwayif auto_align b)
  | Biwhile (e, e', ag, sp, c) -> Biwhile (e, e', ag, sp, auto_align c)
  | Bisync _ | Biassume _ | Biassert _ | Bihavoc_right _ | Biupdate _ -> cc
