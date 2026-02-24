module ArrayStack : STACK =

  class CellArray { slots: Cell array; length: int; }
  class Stack { rep: rgn; size: int; ghost contents: intList;
                arr: CellArray; top: int; }

  private invariant arrayStackPriv =
    (forall st:Stack in pool.
      let arr = st.arr in
      let stk = st.contents in
      let siz = st.size in
      let top = st.top in
      let rep = st.rep in
      Type(rep, CellArray | Cell) /\
      arr <> null /\ arr.length = maxSize /\ arr in rep /\
      /* all the Cell's up to top are nonnull and in rep */
      (forall i:int. 0 <= i /\ i <= top -> let c = arr[i] in c <> null /\ c in rep) /\
      siz = listLength(stk) /\
      siz = top+1 /\
      /* correspondence between arr and contents */
      (forall i:int. 0 <= i /\ i <= top ->
         let c = arr[i] in
	 let v = c.cell_value in
	 v = listNth(top-i, stk))) /\ stackPub()

  meth Stack (self:Stack) : unit
  = var arr: CellArray in
    var rep: rgn in
    self.rep := {};
    self.contents := nil;
    self.size := 0;
    self.top := -1;
    arr := new CellArray[maxSize];
    self.arr := arr;
    rep := self.rep; self.rep := rep union {arr};
    pool := pool union {self};

  meth isEmpty (self:Stack) : bool
  = var sz: int in
    sz := self.size;
    result := (sz = 0);

  meth push (self:Stack, k:int) : unit
  = var a: CellArray in
    var m: int in
    var v: Cell in
    var sz: int in
    var rep: rgn in
    var ghost contents: intList in
    a := self.arr;
    m := self.top;
    self.top := m+1;
    v := new Cell;
    Cell(v, k);
    a[m+1] := v;
    self.arr := a;
    sz := self.size; self.size := sz+1;
    rep := self.rep; self.rep := rep union {v};
    contents := self.contents; self.contents := cons(k,contents);
    { let top = self.top in
      forall i:int.  0 <= i /\ i <= top ->
        let stk = self.contents in
        let arr = self.arr in
        let box = arr[i] in
        box.cell_value = listNth(top-i,stk) }

  meth pop (self:Stack) : Cell
  = var a: CellArray in
    var m: int in
    var sz: int in
    var ghost contents: intList in
    a := self.arr; m := self.top;
    result := a[m];
    self.top := m-1;
    sz := self.size; self.size := sz-1;
    contents := self.contents; self.contents := tl(contents);

  meth getMaxSize() : int
  = result := maxSize;

  meth getCellValue(c:Cell) : int
  = result := c.cell_value;

end
