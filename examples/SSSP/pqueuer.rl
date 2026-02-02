module PqueueR : PQUEUE =

  class Node { tag: int; key: int; prev: Node; sibling: Node; child: Node; }

  class NodeArray { length: int; slots: Node array; }

  class Pqueue { head: Node; size: int; rep: rgn; sntl: Node; }

  predicate repOk (pq:Pqueue) =
    pq <> null ->
    let sntl = pq.sntl in
    let rep = pq.rep in
    Type(rep, Node) /\
    sntl notin rep /\
    null notin rep /\
    forall n:Node in rep.
      let chl = n.child in
      let sib = n.sibling in
      let prev_ = n.prev in
      (chl in rep \/ chl = sntl) /\
      (sib in rep \/ sib = sntl) /\
      (prev_ in rep \/ prev_ = sntl)

  lemma repOk_EMPTY : forall p:Pqueue. p.rep = {} -> repOk (p)

  predicate sntlOk (sntl:Node) =
    sntl <> null ->
    sntl.tag = -1 /\
    sntl.key = -1 /\
    sntl.sibling = sntl /\
    sntl.child = sntl /\
    sntl.prev = sntl

  predicate strongDisjoint (r:rgn) = forall p:Pqueue in r, q:Pqueue in r.
    let prep = p.rep in
    let qrep = q.rep in
    p <> q -> prep inter qrep = {}

  private invariant pqueueI = forall pq:Pqueue in pool.
    let rep = pq.rep in
    let sz = pq.size in
    let sntl = pq.sntl in
    let head = pq.head in
    sntl <> null /\
    sntl in pool /\
    sntl notin rep /\
    repOk (pq) /\
    head <> null /\
    (head <> sntl -> head in rep) /\
    sz >= 0 /\
    (sz = 0 <-> head = sntl) /\
    (forall pq2:Pqueue in pool. pq <> pq2 -> sntl <> pq2.sntl) /\
    (forall pq2:Pqueue in pool. let r = pq2.rep in sntl notin r) /\
    sntlOk(sntl)

  lemma disjointNotIn : forall r:rgn.
    forall p:Pqueue in pool, q:Pqueue in pool.
      pqueuePub () ->
      p <> q ->
      let prep = p.rep in
      let qrep = q.rep in
      forall n:Node in prep. ~ (n in qrep)

  meth Node (self:Node, k:int, m:int) : unit
    ensures { self.key = k }
    ensures { self.tag = m }
    effects  { rw {self}`tag, {self}`key; rd k, m, self }
  = self.key := k;
    self.tag := m;

  meth getTag (self:Node) : int
  = result := self.tag;

  meth getKey (self:Node) : int
  = result := self.key;

  meth Pqueue (self:Pqueue) : unit
  = var sntl : Node in
    sntl := new Node;
    var sntlVal : int in
    sntlVal := -1;
    Node (sntl, sntlVal, sntlVal);
    { forall pq:Pqueue in pool. pq.sntl <> sntl };
    self.rep := {};
    self.sntl := sntl;
    self.head := sntl;
    sntl.sibling := sntl;
    sntl.child := sntl;
    sntl.prev := sntl;
    pool := pool union {self} union {sntl};

  meth isEmpty (self:Pqueue) : bool
  = var sz : int in
    sz := self.size;
    result := sz = 0;

  meth findMin (self:Pqueue) : Node
  = { let sntl = self.sntl in self.head <> sntl };
    result := self.head;

  meth link (self:Pqueue, first:Node, second:Node) : Node
    requires { self in pool }
    requires { let rep = self.rep in first in rep /\ second in rep }
    requires { pqueuePub () }
    requires { pqueueI () }
    ensures  { pqueuePub () }
    ensures  { pqueueI () }
    ensures  { (result = first /\ first.child = second) \/
               (result = second /\ second.child = first) }
    ensures  { result = first \/ result = second }
    ensures  { let rep = self.rep in result in rep }
    writes   { {self}`rep`child, {self}`rep`prev, {self}`rep`sibling }
    reads    { {self}`rep`any, {self}`any, self, first, second }
  = var fkey : int in
    var skey : int in
    var tmp : Node in
    var rep : rgn in
    var sntl : Node in
    sntl := self.sntl;
    { first <> sntl /\ second <> sntl };
    { forall p:Pqueue in pool. let snt = p.sntl in first <> snt /\ second <> snt };
    rep := self.rep; fkey := first.key; skey := second.key;
    { forall p:Pqueue in pool. p <> self -> repOk (p) };
    { sntlOk (sntl) };
    { forall p:Pqueue in pool. p <> self -> let snt = p.sntl in sntlOk(snt) };
    if skey < fkey then
        tmp := first.prev;
        { tmp <> sntl -> tmp in rep };
        second.prev := tmp;
	{ let snt = self.sntl in sntlOk(snt) };
        first.prev := second;
        { let p = first.prev in p in rep };
        tmp := second.child;
        first.sibling := tmp;
	{ sntlOk (sntl) };
	{ forall p:Pqueue in pool. let snt = p.sntl in sntlOk(snt) };
        if tmp <> sntl then
            tmp := first.sibling;
            { let rep = self.rep in tmp in rep };
            { forall p:Pqueue in pool. p <> self -> let rep = p.rep in tmp notin rep };
            { let rep = self.rep in let p = tmp.prev in p = sntl \/ p in rep };
            tmp.prev := first;
            { tmp in rep };
            { let p = tmp.prev in p in rep };
            { repOk (self) };
	    { sntlOk (sntl) };
	    { forall p:Pqueue in pool. let snt = p.sntl in sntlOk(snt) };
        end;
	{ first <> sntl };
        second.child := first;
	{ second.child <> sntl };
        result := second;
        { repOk (self) };
	{ sntlOk (sntl) };
	{ forall p:Pqueue in pool. let snt = p.sntl in sntlOk(snt) };
    else
        second.prev := first;
        tmp := second.sibling;
        { tmp <> sntl -> tmp in rep };
        first.sibling := tmp;
        if tmp <> sntl then
            tmp := first.sibling;
            tmp.prev := first;
        end;
        tmp := first.child;
        second.sibling := tmp;
        if tmp <> sntl then
            { tmp in rep };
            tmp := second.sibling;
            { tmp in rep };
            tmp.prev := second;
        end;
        first.child := second;
        result := first;
        { repOk (self) };
    end;

  lemma insert_wr_rgn_eq : forall self:Pqueue, n:Node.
    let rep = self.rep in
    n in rep ->
    {n} union {self}`rep = {self}`rep

  meth insert (self:Pqueue, k:int, m:int) : Node
  = var sntl : Node in
    sntl := self.sntl;
    result := new Node;
    Node (result, k, m);
    { pqueuePub () };
    { forall p:Pqueue in pool. let rep = p.rep in result notin rep };

    result.sibling := sntl;
    result.child := sntl;
    result.prev := sntl;

    var rep : rgn in
    rep := self.rep; { repOk (self) };
    self.rep := rep union {result}; { repOk (self) };

    { forall p:Pqueue in pool. p <> self -> let r = old(p.rep) in p.rep = r };
    { forall p:Pqueue in pool. p <> self -> let r = p.rep in result notin r };
    { forall p:Pqueue in pool. p <> self -> let r = p.rep in let r2 = self.rep in r#r2 };
    { pqueuePub () };

    var hd : Node in
    hd := self.head;
    if hd = sntl then
        self.head := result; { repOk (self) };
    else
        var tmp : Node in
        tmp := link (self, hd, result);
        self.head := tmp;
        { let hd = self.head in
          let rep = self.rep in hd <> null /\ hd in rep };
    end;
    var sz : int in
    sz := self.size;
    self.size := sz + 1;

  meth combineAux (self:Pqueue, handle:Node) : Node
    requires { self in pool }
    requires { self.size <> 0 }
    requires { let rep = self.rep in handle in rep }
    requires { let sntl = self.sntl in handle.sibling <> sntl /\ handle.sibling <> null }
    requires { pqueuePub () }
    requires { pqueueI () }
    ensures  { pqueuePub () }
    ensures  { pqueueI () }
    ensures  { let rep = self.rep in result in rep }
    effects  { wr {self}`rep`prev, {self}`rep`sibling, {self}`rep`child, alloc;
                  /* {result}`prev, {result}`sibling, {result}`child, alloc; */
               rd self, handle, alloc, {self}`any, {self}`rep`any }
  = var trees : NodeArray in
    var index : int in
    var current : Node in
    var sntl : Node in
    var tmp : Node in
    var fst : Node in
    var snd : Node in
    var i : int in
    var j : int in

    sntl := self.sntl;

    trees := new NodeArray[1024];
    trees[0] := handle; { trees[0] <> null };
    { forall p:NodeArray. p <> trees -> let old_slots = old(p.slots) in old_slots = p.slots };
    index := 1;
    current := handle.sibling;

    while (current <> sntl) do
      invariant { 1 <= index /\ let l = trees.length in index < l }
      invariant { forall k:int. 0 <= k -> k < index -> trees[k] <> sntl }
      invariant { forall k:int. 0 <= k -> k < index -> let n = trees[k] in let rep = self.rep in n in rep }
      invariant { current <> sntl -> let rep = self.rep in current in rep }
      invariant { pqueuePub () }
      invariant { pqueueI () }
      writes { {trees}`slots, {self}`rep`sibling, {self}`rep`child, {self}`rep`prev }

      assume { let l = trees.length in index < l-1 };

      trees[index] := current;
      tmp := current.prev;
      tmp.sibling := sntl;
      current := current.sibling;
      index := index + 1;
    done;
    trees[index] := sntl;

    i := 0; tmp := trees[0];
    while ((i + 1) < index) do
      invariant { forall k:int. 0 <= k -> k < index -> trees[k] <> sntl }
      invariant { forall k:int. 0 <= k -> k < index -> let n = trees[k] in let rep = self.rep in n in rep }
      invariant { let rep = self.rep in tmp in rep /\ tmp <> null }
      invariant { pqueuePub () }
      invariant { pqueueI () }
      invariant { 0 <= i /\ i <= index }
      writes { {trees}`slots, {self}`rep`sibling, {self}`rep`child, {self}`rep`prev }

      fst := trees[i];
      snd := trees[i+1];
      tmp := link(self, fst, snd);
      trees[i] := tmp;
      i := i + 2;
    done;

    j := i - 2;
    if (j >= 0 and j = index - 3) then
        { (j + 2) < index };
        fst := trees[j];
        snd := trees[j+2];
        tmp := link(self, fst, snd);
        trees[j] := tmp;
    end;

    while (2 <= j) do
      invariant { forall k:int. 0 <= k -> k < index -> trees[k] <> sntl }
      invariant { forall k:int. 0 <= k -> k < index -> let n = trees[k] in let rep = self.rep in n in rep }
      invariant { let rep = self.rep in tmp in rep /\ tmp <> null }
      invariant { -2 <= j /\ j < index }
      invariant { pqueuePub () }
      invariant { pqueueI () }
      writes { {trees}`slots, {self}`rep`sibling, {self}`rep`child, {self}`rep`prev }

      fst := trees[j-2];
      snd := trees[j];
      tmp := link(self, fst, snd);
      { tmp <> null /\ Type({tmp},Node) };
      trees[j-2] := tmp;
      j := j - 2;
    done;
    result := trees[0];

  meth combine (self:Pqueue, handle:Node) : Node
    requires { self in pool }
    requires { let rep = self.rep in handle in rep }
    requires { pqueuePub () }
    requires { pqueueI () }
    requires { self.size <> 0 }
    ensures  { pqueueI () }
    ensures  { pqueuePub () }
    ensures  { let rep = self.rep in result in rep }
    ensures  { let ohd = old (self.head) in self.head = ohd }
    effects  { wr {self}`rep`child, {self}`rep`prev, {self}`rep`sibling, alloc;
                  /* {result}`child, {result}`prev, {result}`sibling, alloc; */
               rd {self}`any, {self}`rep`any, self, handle, alloc }
  = var tmp : Node in
    var sntl : Node in
    tmp := handle.sibling;
    sntl := self.sntl;
    if (tmp = sntl) then
        result := handle;
    else
        result := combineAux (self, handle);
    end;

  meth deleteMin (self:Pqueue) : Node
  = result := findMin (self);
    var tmp : Node in
    var sntl : Node in
    sntl := self.sntl;
    tmp := self.head;
    tmp := tmp.child;
    if (tmp = sntl) then
        assume { self.size = 1 };
        self.head := sntl;
    else
        assume { let sz = self.size in sz > 1 };
        tmp := combine(self, tmp);
        self.head := tmp;
    end;
    var sz : int in
    sz := self.size;
    self.size := sz - 1;

  meth decreaseKey (self:Pqueue, handle:Node, k:int) : unit
  = var tmp : Node in
    var pos : Node in
    var sntl : Node in
    sntl := self.sntl;
    handle.key := k;
    tmp := self.head; { repOk(self) };
    if (handle <> tmp) then
        tmp := handle.sibling;
        if (tmp <> sntl) then
            /* handle.sibling.prev := handle.prev */
            pos := handle.prev;
            tmp.prev := pos;
            { repOk(self) };
        end;

        /* if (handle.prev <> self.sentinel) ... */
        tmp := handle.prev;
        if (tmp <> sntl) then
            /* if (handle.prev.child = handle) ... */
            pos := tmp.child;
            if (pos = handle) then
                /* handle.prev.child := handle.sibling */
                pos := handle.sibling;
                tmp.child := pos;
            else
                { handle.prev <> sntl };
                /* handle.prev.sibling := handle.sibling */
                pos := handle.sibling;
                tmp.sibling := pos;
                { pos <> sntl -> let rep = self.rep in let sibling_ = tmp.sibling in sibling_ in rep };
            end;
            { forall p:Node. let r = self.rep in
                p notin r -> let sib = old(p.sibling) in p.sibling = sib };
        end;

        handle.sibling := sntl;
        pos := self.head;
        tmp := link(self,pos,handle);
        self.head := tmp;
    end;

end
