interface REVERSE =
  import theory Reverse_theory

  extern type intSeq with default = emptySeq
  extern seqLength (intSeq) : int
  extern seqNth (int, intSeq) : int
  extern rev (intSeq) : intSeq

  class Node { value:int; nxt:Node; ghost pos:int; }
  class List { head:Node; rep:rgn; ghost contents:intSeq; }

  /* Exactly one node at every position in [lo, hi), with consecutive links.
     xs describes the whole list; this segment uses only its selected range. */
  predicate segment (head:Node, nodes:rgn, xs:intSeq, lo:int, hi:int) =
    0 <= lo /\ lo <= hi /\ hi <= seqLength(xs) /\
    Type(nodes, Node) /\ ~(null in nodes) /\
    ((lo = hi /\ head = null /\ nodes = {}) \/
     (lo < hi /\ head <> null /\ head in nodes /\ head.pos = lo)) /\
    (forall p:Node in nodes.
      let i = p.pos in
      lo <= i /\ i < hi /\ p.value = seqNth(i, xs) /\
      let next = p.nxt in
      ((i = hi-1 /\ next = null) \/
       (i < hi-1 /\ next <> null /\ next in nodes /\ next.pos = i+1))) /\
    (forall p:Node in nodes, q:Node in nodes.
      let i = p.pos in let j = q.pos in i = j -> p = q)

  lemma segment_tail : forall head:Node, nodes:rgn, xs:intSeq, lo:int, hi:int.
    head <> null /\ segment(head, nodes, xs, lo, hi) ->
    let next = head.nxt in segment(next, nodes diff {head}, xs, lo+1, hi)

  lemma segment_cons : forall head:Node, tail:Node?, nodes:rgn, xs:intSeq,
                             lo:int, hi:int.
    0 < lo /\ head <> null /\ ~(head in nodes) /\
    head.pos = lo-1 /\ head.value = seqNth(lo-1, xs) /\ head.nxt = tail /\
    segment(tail, nodes, xs, lo, hi) ->
    segment(head, {head} union nodes, xs, lo-1, hi)

  predicate listrep (self:List) =
    self <> null /\
    let head = self.head in let nodes = self.rep in
    let xs = self.contents in segment(head, nodes, xs, 0, seqLength(xs))

  meth reverse (self:List) : unit
    requires { listrep(self) }
    ensures { listrep(self) }
    ensures { let xs = old(self.contents) in self.contents = rev(xs) }
    ensures { let nodes = old(self.rep) in self.rep = nodes }
    effects { rd self, {self}`head, {self}`rep, {self}`contents,
                 {self}`rep`value, {self}`rep`nxt, {self}`rep`pos;
              wr {self}`head, {self}`contents, {self}`rep`nxt, {self}`rep`pos }
end

module Reverse : REVERSE =
  class Node { value:int; nxt:Node; ghost pos:int; }
  class List { head:Node; rep:rgn; ghost contents:intSeq; }

  meth reverse (self:List) : unit =
    var current:Node in
    var previous:Node in
    var next:Node in
    var ghost todo:rgn in
    var ghost doneNodes:rgn in
    var ghost original:intSeq in
    var ghost reversed:intSeq in
    var ghost size:int in
    var ghost k:int in
    original := self.contents;
    reversed := rev(original);
    size := seqLength(original);
    k := 0;
    current := self.head;
    previous := null;
    todo := self.rep;
    doneNodes := {};
    while (current <> null) do
      invariant { 0 <= k /\ k <= size }
      invariant { size = seqLength(original) /\ size = seqLength(reversed) }
      invariant { let xs = old(self.contents) in original = xs }
      invariant { reversed = rev(original) }
      invariant { segment(current, todo, original, k, size) }
      invariant { segment(previous, doneNodes, reversed, size-k, size) }
      invariant { todo # doneNodes }
      invariant { let nodes = self.rep in nodes = todo union doneNodes }
      effects { wr {self}`rep`nxt, {self}`rep`pos }
      assert { current in todo /\ current.pos = k /\ k < size };
      next := current.nxt;
      assert { segment(next, todo diff {current}, original, k+1, size) };
      current.nxt := previous;
      current.pos := size-k-1;
      assert { segment(next, todo diff {current}, original, k+1, size) };
      assert { segment(previous, doneNodes, reversed, size-k, size) };
      assert { segment(current, {current} union doneNodes, reversed, size-k-1, size) };
      todo := todo diff {current};
      doneNodes := doneNodes union {current};
      previous := current;
      current := next;
      k := k+1;
    done;
    self.head := previous;
    self.contents := reversed;
end
