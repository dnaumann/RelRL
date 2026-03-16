bimodule PQUEUE_REL ( PqueueL | PqueueR ) =

  predicate coupling0 (pq: Pqueue | pq: Pqueue) =
    Both (pq <> null) ->
    Agree pq ->
      let sntl | sntl = pq.sntl | pq.sntl in
      let rep | rep = pq.rep | pq.rep in
      let hd | hd = pq.head | pq.head in
      let sz | sz = pq.size | pq.size in
      (Agree sz) /\
      (Agree hd \/ (<| hd = null <] /\ [> hd = sntl |>)) /\
      ((Node of rep) =:= (Node of rep)) /\
      (forall n:Node in rep | n:Node in rep.
         Agree n -> (
           let k | k = n.key | n.key in
           let m | m = n.tag | n.tag in
           let prev_ | prev_ = n.prev | n.prev in
           let sib | sib = n.sibling | n.sibling in
           let chl | chl = n.child | n.child in
           Agree k /\
           Agree m /\
           /* For f in prev_,sib,chl: can say (Agree f /\ Both (f in rep)) \/ (<| f = null <] /\ [> f = sntl |>) */
           ((Agree prev_ /\ (<| prev_ <> null <] /\ [> prev_ <> sntl |>)) \/ (<| prev_ = null <] /\ [> prev_ = sntl |>)) /\
           ((Agree sib /\ (<| sib <> null <] /\ [> sib <> sntl |>)) \/ (<| sib = null <] /\ [> sib = sntl |>)) /\
           ((Agree chl /\ (<| chl <> null <] /\ [> chl <> sntl |>)) \/ (<| chl = null <] /\ [> chl = sntl |>))))

  coupling pqueueR =
    (Pqueue of pool) =:= (Pqueue of pool) /\
    (forall pq:Pqueue in pool | pq:Pqueue in pool. Agree pq -> coupling0 (pq | pq)) /\
    Both (pqueueI ()) /\ Both (pqueuePub ())

  meth isEmpty (self:Pqueue | self:Pqueue) : (bool | bool)
    requires { Both (self in pool) }
    requires { Both (pqueuePub ()) }
    requires { Both (pqueueI ()) }
    requires { Agree {self}`size }
    requires { Agree self }
    ensures  { let s_alloc | s_alloc = old(alloc) | old(alloc) in
               Agree (alloc diff s_alloc)`any }
    ensures  { Agree result }
    ensures  { Both (pqueuePub ()) }
    ensures  { Both (pqueueI ()) }
    effects  { rd {self}`size | rd {self}`size }
  = Var sz : int | sz : int in
    |_ sz := self.size _|;
    |_ result := sz = 0 _|;

  meth findMin (self:Pqueue | self:Pqueue) : (Node | Node)
    requires { Both (self in pool) }
    requires { Both (let sz = self.size in sz > 0) }
    requires { Both (pqueuePub ()) }
    requires { Both (pqueueI ()) }
    requires { Agree self }
    ensures  { let s_alloc | s_alloc = old(alloc) | old(alloc) in
               Agree (alloc diff s_alloc)`any }
    ensures  { Both (let hd = self.head in result = hd) }
    ensures  { Agree result }
    ensures  { Both (pqueuePub ()) }
    ensures  { Both (pqueueI ()) }
    effects  { rd {self}`head, alloc | rd {self}`head, alloc }
  = {{ <| self.head <> null <] /\ [> let sntl = self.sntl in self.head <> sntl |> }};
    |_ result := self.head _|


  meth link (self:Pqueue, first:Node, second:Node | self:Pqueue, first:Node, second:Node) : (Node | Node)
    requires { Both (self in pool) }
    requires { Both (let rep = self.rep in first in rep /\ second in rep) }
    requires { Both (pqueuePub ()) }
    requires { Both (pqueueI ()) }
    requires { pqueueR(|) }
    requires { Agree self }
    requires { Agree first }
    requires { Agree second }
    ensures  { Both ((result = first /\ first.child = second) \/ (result = second /\ second.child = first)) }
    ensures  { Both (result = first \/ result = second) }
    ensures  { Agree result }
    ensures  { let s_alloc | s_alloc = old(alloc) | old(alloc) in
               Agree (alloc diff s_alloc)`any }
    ensures  { Both (pqueuePub ()) }
    ensures  { Both (pqueueI ()) }
    ensures  { pqueueR(|) }
    effects  { wr {self}`rep`child, {self}`rep`prev, {self}`rep`sibling; rd {self}`rep`any
             | wr {self}`rep`child, {self}`rep`prev, {self}`rep`sibling; rd {self}`rep`any }

  meth insert (self:Pqueue, k:int, m:int | self:Pqueue, k:int, m:int) : (Node | Node)
    requires { Both (self in pool) }
    requires { Both (pqueuePub ()) }
    requires { Both (pqueueI ()) }
    requires { Agree self }
    requires { Agree k }
    requires { Agree m }
    ensures  { Both (let rep = self.rep in result in rep) }
    ensures  { Both (let orep = old(self.rep) in self.rep = orep union {result}) }
    ensures  { Both (let osz = old(self.size) in self.size = osz + 1) }
    ensures  { Both (result.key = k) }
    ensures  { Both (result.tag = m) }
    ensures  { Agree result }
    ensures  { Both (pqueuePub ()) }
    ensures  { Both (pqueueI ()) }
    ensures  { Both (let rep = self.rep in forall n:Node in rep. n <> result ->
                       let ot = old(n.tag) in
                       let ok = old(n.key) in
                       n.tag = ot /\ n.key = ok) }
    effects  { rw {self}`head, {self}`size, {self}`rep, {self}`rep`any, alloc
             | rw {self}`head, {self}`size, {self}`rep, {self}`rep`any, alloc }
   = {{ coupling0 (self | self) }};
     Var sntl: Node | sntl: Node in
     ( skip | sntl := self.sntl );
     |_ result := new Node _|;
     |_ Node(result,k,m) _|;
     ( skip | result.sibling := sntl; result.child := sntl; result.prev := sntl );
     Connect result with result;

     {{ Agree result }};
     {{ <| result.sibling = null /\ result.child = null /\ result.prev = null <] /\
        [> result.sibling = sntl /\ result.child = sntl /\ result.prev = sntl |> }};

     Var rep: rgn | rep: rgn in
     |_ rep := self.rep _|;
     |_ self.rep := rep union {result} _|;
     Var hd: Node | hd: Node in
     |_ hd := self.head _|;

     {{ <| self.head = null <] <-> [> self.head = sntl |> }};

     If hd = null | hd = sntl then
         |_ self.head := result _|;
         {{ let hd | hd = self.head | self.head in Agree hd }};
         {{ forall pq:Pqueue in pool | pq:Pqueue in pool. Agree pq ->
              let hd | hd = pq.head | pq.head in
              Agree hd \/ (<| hd = null <] /\ [> hd = pq.sntl |>) }};
         {{ coupling0 (self | self) }};
     else
         {{ coupling0 (self | self) }};
         Var tmp: Node | tmp: Node in
         Assume { Both (pqueuePub ()) /\ Both (pqueueI ()) };
         |_ tmp := link(self,hd,result) _|;
         |_ self.head := tmp _|;
     end;

     Var sz: int | sz: int in
     |_ sz := self.size _|; {{ sz =:= sz }};
     |_ self.size := sz + 1 _|;
     /* verified -- assumed in order to simplify verifying the biprogram */
     Assume { Both (pqueuePub ()) /\ Both (pqueueI ()) };


  meth combine (self:Pqueue, handle: Node | self:Pqueue, handle: Node) : (Node | Node)
    requires { Both (self in pool) }
    requires { Both (let rep = self.rep in handle in rep) }
    requires { Both (self.size <> 0) }
    requires { Both (pqueuePub ()) }
    requires { Both (pqueueI ()) }
    requires { Agree self }
    requires { Agree handle }
    requires { pqueueR(|) }
    ensures  { Both (pqueueI ()) }
    ensures  { Both (pqueuePub ()) }
    ensures  { Both (let rep = self.rep in result in rep) }
    ensures  { Both (let ohd = old (self.head) in self.head = ohd) }
    ensures  { pqueueR(|) }
    ensures  { Agree result }
    ensures  { let s_alloc | s_alloc = old(alloc) | old(alloc) in
               Agree (alloc diff s_alloc)`any }
    effects  { wr {self}`rep`child, {self}`rep`prev, {self}`rep`sibling, alloc, {}`slots, {}`length;
               rd {self}`rep`any
             | wr {self}`rep`child, {self}`rep`prev, {self}`rep`sibling, alloc, {}`slots, {}`length;
               rd {self}`rep`any }



  meth deleteMin (self:Pqueue | self:Pqueue) : (Node | Node)
    requires { Both (self in pool) }
    /* requires { Both (let hd = self.head in hd <> null) } */
    /* requires { Both (let sz = self.size in sz > 0) } */
    requires { Both (self.size <> 0) }
    requires { Both (pqueuePub ()) }
    requires { Both (pqueueI ()) }
    requires { Agree self }
    ensures  { Agree result }
    ensures  { Both (let osz = old(self.size) in self.size = osz - 1) }
    ensures  { Both (let orep = old(self.rep) in self.rep = orep) }
    ensures  { Both (let rep = self.rep in
                 forall n:Node in rep.
                   let otag = old(n.tag) in
                   let okey = old(n.key) in
                   n.tag = otag /\ n.key = okey) }
    ensures  { Both (pqueuePub ()) }
    ensures  { Both (pqueueI ()) }
    effects  { rw {self}`any, {self}`rep`any, alloc
             | rw {self}`any, {self}`rep`any, alloc }
  = |_ result := findMin(self) _|;
    Var tmp : Node | tmp : Node in
    Var sntl : Node | sntl : Node in
    ( skip | sntl := self.sntl );
    |_ tmp := self.head _|;
    |_ tmp := tmp.child _|;
    If tmp = null | tmp = sntl then
        Assume { Both (self.size = 1) };
        ( self.head := null | self.head := sntl );
    else
        Assume { Both (let sz = self.size in sz > 1) };
        |_ tmp := combine(self, tmp) _|;
        |_ self.head := tmp _|;
    end;
    Var sz : int | sz : int in
    |_ sz := self.size _|;
    |_ self.size := sz - 1 _|;
    Assume { Both (pqueueI ()) };

  meth decreaseKey (self:Pqueue, handle:Node, k:int | self:Pqueue, handle:Node, k:int) : (unit | unit)
    requires { Both (self in pool) }
    requires { Both (let rep = self.rep in handle in rep) }
    requires { Both (let key = handle.key in k <= key) }
    requires { Both (let sz = self.size in sz > 0) }
    requires { Both (pqueuePub ()) }
    requires { Both (pqueueI ()) }
    requires { Agree self }
    requires { Agree handle }
    requires { Agree k }
    ensures  { Both (handle.key = k) }
    ensures  { Both (pqueuePub ()) }
    ensures  { Both (pqueueI ()) }
    effects  { rw {self}`any, {self}`rep`any
             | rw {self}`any, {self}`rep`any }
  = Var tmp : Node | tmp : Node in
    Var pos : Node | pos : Node in
    Var sntl : Node | sntl : Node in
    ( skip | sntl := self.sntl );
    |_ handle.key := k _|;
    |_ tmp := self.head _|;
    If (handle <> tmp) | (handle <> tmp) then
        |_ tmp := handle.sibling _|;
        If tmp <> null | tmp <> sntl then
            |_ pos := handle.prev _|;
            |_ tmp.prev := pos _|;
        end;

        |_ tmp := handle.prev _|;
        If tmp <> null | tmp <> sntl then
            |_ pos := tmp.child _|;
            {{ Both (handle.prev <> null) /\ [> handle.prev <> sntl |> }};
            {{ Agree tmp /\ <| tmp <> null <] /\ [> tmp <> sntl |> }};
            {{ let c | c = tmp.child | tmp.child in
               (Agree c /\ <| c <> null <] /\ [> c <> sntl |>) \/
               (<| c = null <] /\ [> c = sntl |>)
            }};
            If pos = handle | pos = handle then
                |_ pos := handle.sibling _|;
                |_ tmp.child := pos _|;
            else
                |_ pos := handle.sibling _|;
                |_ tmp.sibling := pos _|;
            end;
            {{ coupling0(self|self) }}; /* Added */
        end;

        ( handle.sibling := null | handle.sibling := sntl );
        |_ pos := self.head _|;
        Assume { Both (pqueuePub () /\ pqueueI ()) };
        |_ tmp := link(self, pos, handle) _|;
        |_ self.head := tmp _|;
    end;
    Assume { Both (pqueuePub () /\ pqueueI ()) };

end
