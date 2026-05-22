module ListStack : STACK =
  import theory Stack_theory
  
  class Node { car: int; cdr: Node; }
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
      Type(rep, Node) /\
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
  =
    var n: Node in
    var tmp: Node in
    var sz: int in
    var rep: rgn in
    var ghost contents: intList in
    n := new Node; n.car := k;
    tmp := self.head; { let rep = self.rep in tmp in rep };
    n.cdr := tmp;
    self.head := n;
    sz := self.size; 
    self.size := sz+1;
    rep := self.rep; 
    self.rep := rep union {n};
    contents := self.contents; self.contents := cons(k,contents);

  meth pop (self:Stack) : int
  = var tmp: Node in
    var nxt: Node in
    var sz: int in
    var ghost contents: intList in
    { let stk = self.contents in exists h:int, m:intList. stk = cons(h,m) };
    tmp := self.head; { tmp <> null };
    nxt := tmp.cdr;
    self.head := nxt; 
    sz := self.size; self.size := sz - 1;
    contents := self.contents; self.contents := tl(contents);
    result := tmp.car;

  meth getMaxSize() : int
  = result := maxSize;

end
