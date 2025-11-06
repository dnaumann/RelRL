bimodule REL_STACK (ArrayStack | ListStack) =

  import theory Stack_theory

  /*
  predicate cellsAgree (stk: Stack | stk: Stack) =
    forall n:int|n:int,rc:Cell. Both (0 <= n) /\ Both (let sz = stk.size in n < sz) ->
      Agree n ->
      [> let hd = stk.head in nodeNth(hd, n, rc) |> ->
      let top | = stk.top in
      let arr | = stk.arr in
      let lc  | = arr[top-n] in
      lc =:= rc
   */

  coupling stackCoupling =
    Both (stackPub()) /\ <| arrayStackPriv() <] /\ [> listStackPriv () |> /\
    Agree maxSize /\
    Agree pool /\
    (forall s:Stack in pool|s:Stack in pool. s =:= s ->
       let stk|stk = s.contents|s.contents in
       Agree stk) /* /\
    (forall s:Stack in pool | s:Stack in pool. s =:= s ->
       let sz|sz = s.size|s.size in Agree sz /\
       cellsAgree(s|s)) */

  meth Stack (self:Stack | self:Stack) : (unit | unit)
    requires { Both (~(self in pool)) }
    requires { Both (stackPub()) }
    requires { Agree self }
    requires { Agree ({self} diff (pool union pool`rep))`any }
    ensures  { Both (stackPub()) }
    ensures  { Both (self.size = 0) }
    ensures  { Both (self.contents = nil) }
    ensures  { Both (let opool = old(pool) in pool = opool union {self}) }
    ensures  { Both (let oa = old(alloc) in
                     ({self}`rep diff {null}) subset (alloc diff oa)) }
    ensures  { let s_alloc | s_alloc = old(alloc) | old(alloc) in
               let self0 | self0 = old({self}) | old({self}) in
               Agree (((alloc diff s_alloc) union self0) 
                  diff (pool union pool`rep))`any }
    effects  { rw {self}`any, alloc, pool; rd self, maxSize
             | rw {self}`any, alloc, pool; rd self, maxSize }
  = Var arr: CellArray| in
    Var rep: rgn| in
    ( self.rep := {}; | self.rep := {null}; self.head := null );
    |_ self.contents := nil _|;
    {{ let stk|stk = self.contents|self.contents in Agree stk }};
    |_ self.size := 0 _|;
    ( self.top := -1; arr := new CellArray[maxSize]; self.arr := arr;
      rep := self.rep; self.rep := rep union {arr};
    | skip );
    |_ pool := pool union {self} _|;
    /* Safe to assume public and private invariants because we've already
     * established these when verifying unary modules ArrayStack and ListStack.
     * Assuming these here makes Why3 proofs go faster. */
     Assume { Both (stackPub()) /\ 
         <| arrayStackPriv() <] /\ [> listStackPriv() |> };
     Assume { Both (let oa = old(alloc) in 
                    ({self}`rep diff {null}) subset (alloc diff oa)) };

  meth isEmpty (self:Stack | self:Stack) : (bool | bool)
    requires { Both (self in pool) }
    requires { Agree {self}`any }
    requires { Agree self }
    requires { Both (stackPub()) }
    ensures  { Both (result <-> self.size = 0) }
    ensures  { Both (stackPub()) }
    ensures  { let s_alloc | s_alloc = old(alloc) | old(alloc) in
               Agree (alloc diff s_alloc diff (pool union pool`rep))`any }
    effects  { rd self; rd {self}`any | rd self; rd {self}`any }
  = Var sz: int | sz: int in
    |_ sz := self.size _|; |_ result := (sz = 0) _|

  meth push (self:Stack, k:int | self:Stack, k:int) : (unit | unit)
    requires { Both (self in pool) }
    requires { Both (stackPub()) }
    requires { Both (let sz = self.size in sz < maxSize) }
    requires { Agree self /\ Agree k }
    requires { Agree (({self} union {self}`rep) diff (pool union pool`rep))`any }
    ensures  { Both (stackPub()) }
    ensures  { Both (let osz = old(self.size) in self.size = osz + 1) }
    ensures  { Both (let xs = old(self.contents) in self.contents = cons(k,xs)) }
    ensures  { Both (let oa = old(alloc) in (alloc diff oa) subset {self}`rep) }
    ensures  { Both (let oa = old(alloc) in let orep = old(self.rep) in
                     {self}`rep subset (orep union (alloc diff oa))) }
    ensures  { let s_alloc | s_alloc = old(alloc) | old(alloc) in
               let snap_r1 | snap_r1 = old({self} union {self}`rep) | old({self} union {self}`rep) in
               Agree (((alloc diff s_alloc) union snap_r1) diff (pool union pool`rep))`any }
    effects  { rw {self}`any, {self}`rep`any, alloc; rd self, k, maxSize 
             | rw {self}`any, {self}`rep`any, alloc; rd self, k, maxSize }
  = Var a: CellArray | in
    Var t: int | in
    Var v: Cell | v: Cell in
    Var | n: Node in
    Var | tmp: Node in
    Var sz: int | sz: int in
    Var rep: rgn | rep: rgn in
    Var ghost contents: intList | ghost contents: intList in
    ( a := self.arr; t := self.top; self.top := t+1 | skip );
    |_ v := new Cell _|;
    Link v with v; /* update current refperm */
    /* TODO: Update ArrayStack -- use Cell constructor */
    ( v.cell_value := k; v.cell_rep := {v}
    | Cell(v,k) );
    ( a[t+1] := v; self.arr := a | skip );
    ( skip 
    | n := new Node; n.car := v; tmp := self.head; n.cdr := tmp;
      self.head := n );
    |_ sz := self.size _|; |_ self.size := sz+1 _|;
    |_ rep := self.rep _|;
    ( self.rep := rep union {v}
    | self.rep := rep union {v} union {n} );
    |_ contents := self.contents _|;
    |_ self.contents := cons(k,contents) _|;
    Assume {  Both(stackPub()) /\ <| arrayStackPriv() <] /\ [> listStackPriv() |>};
    Assume { Both (let oa = old(alloc) in (alloc diff oa) subset {self}`rep) };
    Assume { Both (let oa = old(alloc) in let orep = old(self.rep) in
                   {self}`rep subset (orep union (alloc diff oa))) }

  meth pop (self:Stack | self:Stack) : (Cell | Cell)
    requires { Both (self in pool) }
    requires { Both (let sz = self.size in sz > 0) }
    requires { Both (stackPub()) }
    requires { Agree self }
    requires { Agree (({self} union {self}`rep) diff (pool union pool`rep))`any }
    ensures  { Both (let osz = old(self.size) in self.size = osz - 1) }
    ensures  { Both (let oxs = old(self.contents) in
                     let t = hd(oxs) in result.cell_value = t) }
    ensures  { Both (let ostk = old(self.contents) in self.contents = tl(ostk)) }
    ensures  { Both (let rep = self.rep in result in rep) }
    ensures  { Both(let rep = old(self.rep) in self.rep = rep) }
    ensures  { Both (stackPub()) }
    ensures  { let s_alloc | s_alloc = old(alloc) | old(alloc) in
               let snap_r1 | snap_r1 = old({self} union {self}`rep) | old({self} union {self}`rep) in
               Agree (((alloc diff s_alloc) union snap_r1) diff (pool union pool`rep))`any }
    ensures  { let r|r = result|result in let c|c = r.cell_value|r.cell_value in Agree c }
    effects  { rw {self}`any, {self}`rep`any; rd self, maxSize 
             | rw {self}`any, {self}`rep`any; rd self, maxSize }
  = Var a: CellArray | in
    Var t: int | in
    Var | tmp: Node in
    Var | nxt: Node in
    Var sz: int | sz: int in
    Var ghost contents: intList | ghost contents: intList in
    ( a := self.arr; t := self.top | tmp := self.head );
    Assert { [> let stk = self.contents in exists h:int, t:intList. stk = cons(h,t) |> };
    Assert { [> tmp <> null |> };
    Assert { <| arrayStackPriv() <] /\ [> listStackPriv() |> /\ stackCoupling(|) };
    ( result := a[t] | result := tmp.car );
    /* Assert { Agree result }; */ Assert { stackCoupling(|) };
    Assert { let sz|sz = self.size|self.size in Agree sz };
    ( self.top := t-1 | nxt := tmp.cdr; self.head := nxt );
    |_ sz := self.size _|; |_ self.size := sz-1 _|; 
    Assert { let sz|sz = self.size|self.size in Agree sz };
/*    Assert { cellsAgree(self|self) }; */
/*    Assert { forall n:int|n:int, rc:Cell. Both (0 <= n) /\ Both (let sz = self.size in n < sz) ->
      Agree n ->
      [> let hd = self.head in nodeNth(hd, n, rc) |> ->
      let top | = self.top in
      let arr | = self.arr in
      let lc  | = arr[top-n] in
      lc =:= rc }; */
    |_ contents := self.contents _|; |_ self.contents := tl(contents) _|;
    Assume { Both(stackPub()) /\ <| arrayStackPriv() <] /\ [> listStackPriv() |> };
    Assume { Both(let rep = self.rep in result in rep) }

  meth getCellValue (c: Cell | c: Cell) : (int | int)
    requires { let v|v = c.cell_value|c.cell_value in v =:= v }
    ensures  { Agree result }
    effects  { rd c, {c}`any; rw result | rd c, {c}`any; rw result }
  = |_ result := c.cell_value _|;


end
