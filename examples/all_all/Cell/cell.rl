interface CELL =

  class Cell { value: int; rep: rgn; }

  ghost pool : rgn

  boundary { pool, pool`any, pool`rep`any }

  public invariant cellP = forall c:Cell in pool, d:Cell in pool.
    let crep = c.rep in
    let drep = d.rep in
    c <> d -> crep # drep

  lemma emptyPoolCellP : pool = {} -> cellP ()

  meth Cell (self:Cell, k:int) : unit
    requires { ~(self in pool) }
    requires { self.rep = {} }
    requires { k >= 0 }
    ensures  { self in pool }
    effects  { rw {self}`any, alloc, pool; rd self, k }

  meth cset (self:Cell, k:int) : unit
    requires { self in pool }
    requires { k >= 0 }
    effects  { rw {self}`any, alloc; rd self, k }

  meth cget (self:Cell) : int
    requires { self in pool }
    ensures  { result >= 0 }
    effects  { rd self, {self}`any; rw alloc }

end

module ACell : CELL =

  class Cell { value: int; rep: rgn; }

  private invariant cellI = forall c:Cell in pool.
    c.rep = {c} /\ let v = c.value in v >= 0

  meth Cell (self:Cell, k:int) : unit =
    self.value := k;
    self.rep := {self};
    pool := pool union {self};

  meth cset (self:Cell, k:int) : unit =
    self.value := k;

  meth cget (self:Cell) : int =
    result := self.value;

end

module BCell : CELL =

  class Cell
  { value : int;
    rep   : rgn;
  }

  private invariant cellI = forall c:Cell in pool.
    let v = c.value in
    v <= 0 /\ c.rep = {c}

  meth Cell (self:Cell, k:int) : unit =
    if k <= 0 then
      self.value := k;
    else
      self.value := -k;
    end;
    self.rep := {self};
    pool := pool union {self};

  meth cset (self:Cell, k:int) : unit =
    if k <= 0 then
      self.value := k;
    else
      self.value := -k;
    end;

  meth cget (self:Cell) : int =
    var value : int in
    value := self.value;
    result := -value;

end

bimodule CELL_REL ( ACell | BCell ) =

  coupling cellC =
    Agree pool /\
    Both (cellI ()) /\
    (Cell of pool) =:= (Cell of pool) /\
    (forall c:Cell in pool | c:Cell in pool.
       c =:= c -> let v|v = c.value|c.value in v =:= -v)

  meth Cell (self:Cell,k:int | self:Cell,k:int) : (unit | unit)
    requires { cellC(|) }
    ensures  { cellC(|) }
    requires { Both (~(self in pool)) }
    requires { Both (self.rep = {}) }
    requires { Both (cellP()) }
    requires { Both (cellI()) }
    requires { let rp|rp = self.rep|self.rep in rp =:= rp }
    requires { let vl|vl = self.value|self.value in vl =:= -vl }
    requires { k =:= k }
    requires { self =:= self }
    requires { Both (k >= 0) }
    ensures  { Both (cellP()) }
    ensures  { Both (cellI()) }
    ensures  { Both (self in pool) }
    effects  { rw {self}`any, alloc, pool; rd k
             | rw {self}`any, alloc, pool; rd k }
  = ( self.value := k
    | if k <= 0 then self.value := k else self.value := -k end; );
    Assert { Both (k >= 0) -> let v|v = self.value|self.value in v =:= -v };
    |_ self.rep := {self} _|;
    |_ pool := pool union {self} _|;

  meth cset (self:Cell,k:int | self:Cell,k:int) : (unit | unit)
    requires { cellC(|) }
    ensures  { cellC(|) }
    requires { Both (self in pool) }
    requires { Both (cellP()) }
    requires { Both (cellI()) }
    requires { let rep|rep = self.rep|self.rep in rep =:= rep }
    requires { let vl|vl = self.value|self.value in vl =:= -vl }
    requires { k =:= k }
    requires { Both (k >= 0) }
    ensures  { let rep|rep = self.rep|self.rep in rep =:= rep }
    ensures  { Both (cellP()) }
    ensures  { Both (cellI()) }
    effects  { rw {self}`any, alloc, pool; rd k
             | rw {self}`any, alloc, pool; rd k }
  = Assert { self =:= self };
    ( self.value := k
    | if k <= 0 then self.value := k else self.value := -k end; );

  meth cget (self:Cell | self:Cell) : (int | int)
    requires { cellC(|) }
    ensures  { cellC(|) }
    requires { Both (self in pool) }
    requires { Both (cellP()) }
    requires { Both (cellI()) }
    requires { let rep|rep = self.rep|self.rep in rep =:= rep }
    requires { let vl|vl = self.value|self.value in vl =:= -vl }
    ensures  { Both (cellP()) }
    ensures  { Both (cellI()) }
    ensures  { Both (result >= 0) }
    ensures  { result =:= result }
    effects  { rw {self}`any, alloc, pool
             | rw {self}`any, alloc, pool }
  = ( result := self.value
    | var value : int in
      value := self.value;
      result := -value );

end

module Main =
  import CELL related by CELL_REL

  meth main(x:int) : int
    requires { pool = {} }
    requires { x >= 0 }
    effects { rw alloc, pool, x }
  = var c : Cell in
    c := new Cell;
    var k : int in
    k := 0;
    Cell (c,k);
    { c in alloc };
    x := x + 1;
    cset (c, x);
    result := cget (c);

end
