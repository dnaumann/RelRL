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
      havoc k;
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
      havoc k;
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

bimodule MREL (M0 | M1) =

  meth Node (self:Node, v: int | self:Node, v: int) : (unit | unit)
    requires { Agree self }
    requires { Agree v }
    requires { Both (self.nxt = null) }
    ensures { Both (self.nxt = null) }
    ensures { Both (self.value = v) }
    ensures { Agree {self}`value }
    effects { rd self, v; rw {self}`value
            | rd self, v; rw {self}`value }

  meth List (self:List | self:List) : (unit | unit)
    requires { Agree self }
    ensures { Both (self.head = null) }
    ensures { Both (self.rep = {null}) }
    ensures { Both (rep_closed(self)) }
    ensures { Agree {self}`rep /\ Agree {self}`head }
    effects { rd self; rw {self}`head, {self}`rep
            | rd self; rw {self}`head, {self}`rep }

  meth f (i:int | i:int) : (int | int)
    requires { Both (i >= 0) }
    requires { i =:= i }
    ensures { result =:= result }
    effects { rd i | rd i }

  meth tabulate (n: int | n: int) : (List | List)
    requires { Both (n > 0) }
    requires { Agree n }
    ensures { let s_alloc | s_alloc = old(alloc) | old(alloc) in
              Agree (alloc diff s_alloc)`any }
    ensures { Agree result }
    effects  { rd n; wr alloc | rd n; wr alloc }
  = Var l: List | l: List in
    Var p: Node | p: Node in
    Var i: int | i: int in
    |_ l := new List _|;
    Connect l with l;
    |_ List(l) _|;
    ( i := 0 | i := 1 );
    While (i < n) | (i <= n) . <| false <] | [> false |> do
      invariant { <| 0 <= i /\ i <= n <] /\ [> 1 <= i /\ i <= n+1 |> }
      invariant { Both (rep_closed(l)) /\ Both (let rep = l.rep in p in rep) }
      invariant { Both (let s_alloc = old(alloc) in let rep = l.rep in rep # s_alloc) }
      invariant { (i+1) =:= i }
      invariant { Agree l /\ Agree {l}`rep /\ Agree {l}`head }
      invariant { let s_alloc|s_alloc = old(alloc)|old(alloc) in
                  Agree (alloc diff s_alloc)`any }
      invariant { Agree {l}`rep`any } /* OK */
      invariant { let s_alloc|s_alloc = old(alloc)|old(alloc) in
                  Both ((alloc diff s_alloc diff {l}) subset {l}`rep) } /* OK */
      effects { rd i, n; rw alloc, {l}`rep, {l}`rep`any
              | rd i, n; rw alloc, {l}`rep, {l}`rep`any }

      Var k: int | k: int in
      ( i := i + 1 | skip );
      Assert { i =:= i };
      (havoc k | skip);
      HavocR k {k =:= k};
      |_ p := new Node _|;
      Connect p with p;
      |_ Node(p, k) _|;
      Assert { Agree {p}`any }; /* OK */
      Var hd: Node | hd: Node in
      |_ hd := l.head _|;
      |_ p.nxt := hd _|;
      |_ l.head := p _|;
      Assert { Agree {l}`head }; /* OK */
      Assert { Agree {l}`rep };  /* OK */
      Assert { Agree {l}`rep`any }; /* OK, but takes manual effort */
      Var r: rgn | r: rgn in
      |_ r := l.rep _|;
      |_ l.rep := r union {p} _|;
      Assert { Agree {l}`rep };  /* OK, but takes manual effort */
      Assert { Agree {l}`rep`any }; /* OK */
      ( skip | i := i + 1 );

      /* Assume unary invariants; already verified */
      Assume { Both (rep_closed(l)) /\ Both (let rep = l.rep in p in rep) };
      Assume { Both (let s_alloc = old(alloc) in let rep = l.rep in rep # s_alloc) };
    done;
    |_ result := l _|;

end
