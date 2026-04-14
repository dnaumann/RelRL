module Main =

  import UNIONFIND related by UFREL

  import theory Kruskal_aux

  extern type intList with default = nil
  extern cons (int,intList) : intList
  extern listLength (intList) : int

  extern type graph with default = emptyGraph
  extern hasVertex (graph, int) : bool
  extern numVertices (graph) : int
  extern const maxWeight : int

  extern type edge with default = arbEdge
  extern startVertex (edge) : int
  extern endVertex (edge) : int
  extern weight (edge) : int
  extern edges (graph) : edge array
  extern numEdges (edge array) : int

  class Node { value: int; nxt: Node; }
  class List { head: Node; lrep: rgn; }

  predicate lrep_closed (xs:List) = /* TODO: not used -- remove */
    xs <> null ->
    let hd = xs.head in
    let lrep = xs.lrep in
    Type(lrep,Node) /\ lrep`nxt subset lrep /\ null in lrep /\ hd in lrep

  meth Node (self: Node, v: int, n: Node?) : unit
    requires { self notin (pool union pool`rep) }
    requires { self.nxt = null }
    ensures { self.nxt = n }
    ensures { self.value = v }
    effects { rd v, self, n; rw {self}`value, {self}`nxt }
  = self.nxt := n;
    self.value := v;

  meth List (self: List) : unit
    requires { self notin (pool union pool`rep) }
    ensures { self.head = null }
    ensures { self.lrep = { null } }
    ensures { lrep_closed(self) }
    effects { rd self; rw {self}`head, {self}`lrep }
  = self.lrep := { null };
    self.head := null;

  meth main (g:graph) : List
    requires { numVertices(g) > 0 }
    requires { pool = {} }
    ensures { True }
    effects { wr alloc, pool, pool`any, pool`rep`any;
              rd alloc, pool, pool`any, pool`rep`any, g }
  = var uf: Ufind in
    var es: edge array in
    es := edges(g);
    var nverts: int in
    nverts := numVertices(g);

    uf := new Ufind;
    Ufind(uf, nverts);
    { let prt = uf.part in nverts = pSize(prt) };

    var l: List in
    l := new List;
    List(l); { l notin (pool union pool`rep) };

    var i: int in
    while i < numEdges(es)
      do invariant { ufPub() }
         invariant { 0 <= i /\ i <= numEdges(es) }
         invariant { let prt = uf.part in nverts = pSize(prt) }
         invariant { let s_alloc = old(alloc) in let lrep = l.lrep in lrep # s_alloc }
         invariant { l notin (pool union pool`rep) }
         invariant { uf in pool }
         invariant { let s_alloc = old(alloc) in ({uf}`rep) subset (alloc diff s_alloc) } /* CHECK */
         effects { wr {uf}`any, {uf}`rep`any, {l}`lrep, {l}`lrep`any }

      var curredge: edge in
      var startv: int in var endv: int in
      curredge := get(es,i);
      startv := startVertex(curredge);
      endv := endVertex(curredge);
      var srepr: int in
      var erepr: int in
      srepr := find(uf, startv);
      erepr := find(uf, endv);
      if srepr <> erepr then
        { l notin (pool union pool`rep) };
        ufUnion(uf, startv, endv);
        { l notin pool };
        { l notin pool`rep };

        var p: Node in
        p := new Node;

        /* Node(p, i, l.head) */
        var hd: Node in
        hd := l.head;
        Node(p, i, hd);
        { p.nxt = hd };

        l.head := p;

        /* l.lrep := l.lrep union {p} */
        var lr: rgn in
        lr := l.lrep;
        l.lrep := lr union {p};
      end;

      i := i+1;
    done;
    result := l;

end
