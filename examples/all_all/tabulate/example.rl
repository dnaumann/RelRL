interface I =

  class Node { value: int; nxt: Node; }
  class List { head: Node; rep: rgn; }

  predicate rep_closed (xs:List) =
    xs <> null ->
    let hd = xs.head in
    let rep = xs.rep in
    Type(rep,Node) /\ rep`nxt subset rep /\ null in rep /\ hd in rep

  lemma rep_closed_def : forall xs:List.
    rep_closed(xs) ->
    let rep = xs.rep in
    forall n:Node in rep. let nxt = n.nxt in nxt in rep

  meth Node (self:Node, v:int) : unit
    requires { self.nxt = null }
    ensures { self.nxt = null }
    ensures { self.value = v }
    effects { rd v, self; rw {self}`value }

  meth List (self:List) : unit
    ensures { self.head = null }
    ensures { self.rep = {null} }
    ensures { rep_closed(self) }
    effects { rd self; rw {self}`head, {self}`rep }

  meth f (i:int) : int
    requires { i >= 0 }
    effects { rd i }

  meth tabulate (n:int) : List
    requires { n > 0 }
    effects { rd n; rw alloc }

end

module M0 : I =

  class Node { value:int; nxt:Node; }
  class List { head: Node; rep: rgn; }

  meth Node (self:Node, v:int) : unit =
    self.value := v;

  meth List (self:List) : unit =
    self.head := null;
    self.rep := {null};

  meth f (i:int) : int

  meth tabulate (n:int) : List =
    var l: List in
    var p: Node in
    var i: int in
    l := new List;
    List(l);
    i := 0;
    while (i < n) do
      invariant { 0 <= i /\ i <= n }
      invariant { rep_closed(l) }
      invariant { let rep = l.rep in p in rep }
      invariant { let s_alloc = old(alloc) in let rep = l.rep in rep # s_alloc }
      effects { rd i, n; rw alloc, {l}`rep, {l}`rep`any }
      var k: int in
      i := i + 1;
      k := f(i);
      p := new Node;
      Node(p, k);
      var hd: Node in
      hd := l.head;
      p.nxt := hd;
      l.head := p;
      var r: rgn in
      r := l.rep;
      l.rep := r union {p};
    done;
    result := l;

end

module M1 : I =

  class Node { value: int; nxt: Node; }
  class List { head: Node; rep: rgn; }

  meth Node (self:Node, v:int) : unit =
    self.value := v;

  meth List (self:List) : unit =
    self.head := null;
    self.rep := {null};

  meth f (i:int) : int

  meth tabulate (n:int) : List =
    var l: List in
    var p: Node in
    var i: int in
    l := new List;
    List(l);
    i := 1;
    while (i <= n) do
      invariant { 1 <= i /\ i <= n+1 }
      invariant { rep_closed(l) }
      invariant { let rep = l.rep in p in rep }
      invariant { let s_alloc = old(alloc) in let rep = l.rep in rep # s_alloc }
      effects { rd i, n; rw alloc, {l}`rep, {l}`rep`any }
      var k: int in
      k := f(i);
      p := new Node;
      Node(p, k);
      var hd: Node in
      hd := l.head;
      p.nxt := hd;
      l.head := p;
      var r: rgn in
      r := l.rep;
      l.rep := r union {p};
      i := i + 1;
    done;
    result := l;

end
