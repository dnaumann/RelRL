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
      |_ k := f(i) _|;
      Assert { k =:= k };
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
