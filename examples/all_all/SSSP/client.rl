interface CLIENT = end

module Main =
  import PQUEUE related by PQUEUE_REL
  import theory Graph_theory

  extern type graph with default = emptyGraph
  extern hasVertex (graph, int) : bool
  extern numVertices (graph) : int
  extern const maxWeight : int

  extern type edge with default = arbEdge
  extern startVertex (edge) : int
  extern endVertex (edge) : int
  extern weight (edge) : int
  extern edges (graph) : edge array

  class DistArray { dLength: int; dSlots: int array; }

  meth initDistances (d: DistArray, k: int) : unit
    requires { k >= 0 }
    ensures { let len = d.dLength in forall i:int. 0 <= i -> i < len -> d[i] = k }
    effects { rw {d}`dSlots; rd {d}`dLength }

  meth main (g: graph, source: int) : DistArray
    requires { pool = {} }
    requires { pqueuePub() }
    requires { hasVertex(g,source) }
    effects { wr alloc, pool, pool`any, pool`rep, pool`rep`any;
              rd alloc, pool, pool`any, pool`rep, pool`rep`any, g, source }
  = var queue : Pqueue in
    var numVs : int in
    numVs := numVertices(g);
    queue := new Pqueue;
    Pqueue (queue);

    var dist : DistArray in
    dist := new DistArray[numVs];
    initDistances(dist, maxWeight);

    var initDist : int in
    initDist := 0;
    var ins : Node in
    ins := insert(queue, initDist, source);
    var isEmp : bool in
    isEmp := isEmpty(queue);

    var min : Node in
    var minTag : int in
    var minKey : int in
    min := ins;
    while (not isEmp) do
      invariant { isEmp <-> queue.size = 0 }
      invariant { numVs = numVertices(g) /\ dist.dLength = numVs }
      invariant { {dist} # (pool union pool`rep) }
      invariant { let len = dist.dLength in
                  forall k:int. 0 <= k -> k < len -> let v = dist[k] in 0 <= v }
      invariant { let rep = queue.rep in min in rep }
      invariant { let rep = queue.rep in forall n:Node in rep. let key = n.key in key >= 0 }
      invariant { let rep = queue.rep in
                  forall n: Node in rep.
                    let len = dist.dLength in
                    let tag = n.tag in
                    tag >= 0 /\ tag < len }
      invariant { let oa = old(alloc) in
                  (({queue} union {queue}`rep) diff {null}) subset (alloc diff oa) }
      invariant { pqueuePub() }
      effects { wr {dist}`dSlots, {dist}`dLength, {queue}`any, {queue}`rep`any }

      min := deleteMin(queue);
      minTag := getTag(min);
      minKey := getKey(min);
      { minTag >= 0 /\ let len = dist.dLength in minTag < len };

      var i : int in
      i := dist[minTag];

      if (minKey < i) then
        dist[minTag] := minKey;
        var eLen : int in
        var gEdges : edge array in

        isEmp := isEmpty(queue);
        gEdges := edges(g);
        eLen := length(gEdges);

        var i : int in
        while (0 <= i and i < eLen) do
          invariant { 0 <= i /\ i <= eLen }
          invariant { isEmp <-> queue.size = 0 }
          invariant { numVs = numVertices(g) /\ dist.dLength = numVs }
          invariant { let len = dist.dLength in
                      forall k:int. 0 <= k -> k < len -> let v = dist[k] in 0 <= v }
          invariant { let rep = queue.rep in min in rep }
          invariant { let rep = queue.rep in
                      forall n:Node in rep.
                        let len = dist.dLength in
                        let tag = n.tag in
                        tag >= 0 /\ tag < len }
          invariant { {dist} # (pool union pool`rep) }
          invariant { let rep = queue.rep in forall n:Node in rep. let key = n.key in key >= 0 }
          invariant { let oa = old(alloc) in
                      (({queue} union {queue}`rep) diff {null}) subset (alloc diff oa) }
          invariant { pqueuePub() }
          effects { wr {dist}`dSlots, {dist}`dLength, {queue}`any, {queue}`rep`any }

          var startV : int in
          var endV : int in
          var currWeight : int in
          var currEdge : edge in

          currEdge := get(gEdges,i);
          startV := startVertex(currEdge);
          endV := endVertex(currEdge);
          currWeight := weight(currEdge);

          var d : int in
          var candidateDist : int in

          d := dist[startV];
          candidateDist := d + currWeight;
          d := dist[endV];
          if (candidateDist < d) then
            { candidateDist >= 0 /\ endV >= 0 };
            ins := insert(queue, candidateDist, endV);
            dist[endV] := candidateDist;
          end; /* end if (candidateDist < d) */

          i := i + 1;
          isEmp := isEmpty(queue);

        done; /* end while (0 <= i and i < eLen) */
      end; /* end if (minKey < i) */

      isEmp := isEmpty(queue);
    done; /* end while (not isEmp) */
    result := dist;

end
