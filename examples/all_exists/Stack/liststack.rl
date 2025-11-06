module ListStack : STACK =

  class Node { car: Cell; cdr: Node; }
  class Stack { rep: rgn; size: int; ghost contents: intList; head: Node; }

  /* predicate nodeNth (n: Node, i: int, c: Cell) = true */
  /* NOTE: REPLACED by script replacements.py */

  predicate stackRep (xs: intList, n: Node) = true
  /* NOTE: REPLACED by script replacements.py in Makefile:

     The predicate stackRep(xs, n) says xs is the mathematical list that
     corresponds to n.  Unfortunately, we cannot express this predicate in
     WhyRel's source language.  The predicate is recursive and Why3 requires
     all recursion be structural (for predicates, at least in v1.3.3 which we
     use).  WhyRel does not support this yet, but if it did, stackRep(xs,n)
     could be defined as:

     match xs with
     | Nil -> n = null
     | Cons h t ->
       n <> null /\ n.car <> null /\ n.car.cell_value = h /\ stackRep t n.cdr
     end

     The script also adds two lemmas about stackRep.
   */

  private invariant listStackPriv =
    stackPub () /\ forall s:Stack in pool.
      let rep = s.rep in
      let head = s.head in
      let stk = s.contents in
      null in rep /\ head in rep /\
      rep`cdr subset rep /\
      (forall n:Node in rep. let c = n.car in c in rep) /\
      stackRep(stk, head)

  meth Stack (self:Stack) : unit
  = self.rep := {null};
    self.head := null;
    self.contents := nil;
    self.size := 0;
    pool := pool union {self};

  meth isEmpty (self:Stack) : bool
  = var sz: int in sz := self.size; result := (sz = 0);

  meth push (self:Stack, k:int) : unit
  = var v: Cell in
    var n: Node in
    var tmp: Node in
    var sz: int in
    var rep: rgn in
    var ghost contents: intList in
    v := new Cell; Cell(v, k);
    n := new Node; n.car := v;
    tmp := self.head; { let rep = self.rep in tmp in rep };
    n.cdr := tmp;
    { let rep = self.rep in forall n:Node in rep. let c = n.car in c in rep };
    self.head := n;
    sz := self.size; self.size := sz+1;
    rep := self.rep; self.rep := rep union {v} union {n};
    { let h = self.head in let n = h.cdr in let rep = self.rep in n in rep };
    { let rep = self.rep in rep`cdr subset rep };
    { let h = self.head in let c = h.cdr in let rep = self.rep in c in rep };
    { let rep = self.rep in forall n:Node in rep. let c = n.car in c in rep };
    contents := self.contents; self.contents := cons(k,contents);
    { let h = self.head in let stk = self.contents in stackRep(stk,h) }

  meth pop (self:Stack) : Cell
  = var tmp: Node in
    var nxt: Node in
    var sz: int in
    var ghost contents: intList in
    { let stk = self.contents in exists h:int, t:intList. stk = cons(h,t) };
    tmp := self.head; { tmp <> null };
    result := tmp.car;
    nxt := tmp.cdr;
    self.head := nxt; /* self.head = self.head.next */
    sz := self.size; self.size := sz - 1;
    contents := self.contents; self.contents := tl(contents);

  meth getMaxSize() : int
  = result := maxSize;

  meth getCellValue(c:Cell) : int
  = result := c.cell_value;

end
