module ListStack : STACK =
  import theory Stack_theory

  class Node { car: Cell; cdr: Node; }
  class Stack { rep: rgn; size: int; ghost contents: intList; head: Node; }

  /* NOTE: REPLACED by script replacements.py */
  predicate stackRep (xs: intList, n: Node) = true
 
/* The following may be used a whyrel definition of stackRep avoiding the use of the add_lemma script. However, status quo is kept as this might effect stackRep_mono lemma etc if whyrel translation changes and feels risky to decouple. 

  inductive stackRep (xs: intList, n: Node) = 
    | nil_stack : stackRep (nil, null)
    | cons_stack : 
        forall n:Node , l: intList.
        let nxt = n.cdr in
        let new_cell = n.car in
        let v = new_cell.cell_value in
        stackRep(l, nxt) -> 
        stackRep(cons(v, l), n)
The whyrel stackRep definition is translated into the whyml def below
  inductive stackRep (s: state) (xs: intList) (n: reference) = 

     nil_stack : 
        forall s : state. stackRep s STACK.nil null 
    | cons_stack : 
        forall s : state. forall  n1 : reference, l : intList.\
        (isAllocated s n1) -> 
        (hasNodeType s n1) -> 
        (let nxt = s.cdr[n1] in 
        let new_cell = s.car[n1] in 
        let v = s.cell_value[new_cell] in 
        (stackRep s l nxt) -> 
        (stackRep s (STACK.cons v l) n1))
*/

  private invariant listStackPriv =
    stackPub () /\ forall st:Stack in pool.
      let rep = st.rep in
      let head = st.head in
      let stk = st.contents in
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
    { let h = self.head in let c = h.cdr in let rep = self.rep in c in rep };
    { let rep = self.rep in rep`cdr subset rep };
    { let rep = self.rep in forall n:Node in rep. let c = n.car in c in rep };
    contents := self.contents; self.contents := cons(k,contents);
    { let h = self.head in let stk = self.contents in stackRep(stk,h) }

  meth pop (self:Stack) : Cell
  = var tmp: Node in
    var nxt: Node in
    var sz: int in
    var ghost contents: intList in
    { let stk = self.contents in exists h:int, m:intList. stk = cons(h,m) };
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
