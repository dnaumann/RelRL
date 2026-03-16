bimodule UFREL ( QuickFind | QuickUnion ) =

  import theory Partition
  extern bipredicate pEq(partition|partition)

  predicate samePartition (p: Ufind | p: Ufind) =
    let prt|prt = p.part|p.part in
    pSize(prt) =:= pSize(prt) /\
    pEq(prt|prt)

  predicate eqReps (p: Ufind | p: Ufind) =
    let prt|prt = p.part|p.part in
    forall i: int| i: int.
      Both (0 <= i /\ i < pSize(prt)) ->
      i =:= i ->
      let id|id = p.id|p.id in
      <| id[i] = i <] <-> [> id[i] = i |>

  predicate eqRepsExcept (p: Ufind, x: int | p: Ufind, x: int) =
    let prt|prt = p.part|p.part in
    forall i:int | i:int.
      Both (0 <= i /\ i < pSize(prt)) ->
      Both (i <> x) ->
      i =:= i ->
      let id|id = p.id|p.id in
      <| id[i] = i <] <-> [> id[i] = i |>

  predicate ufCoupling_aux (|) =
    pool =:= pool /\
    (forall p: Ufind in pool | p: Ufind in pool.
       p =:= p ->
       samePartition(p|p) /\ eqReps(p|p))

  coupling ufCoupling = Both (ufPub()) /\ Both (ufPriv()) /\ ufCoupling_aux(|)

  meth find (self: Ufind, k: int | self: Ufind, k: int) : (int | int)
    requires { Both (self in pool) }
    requires { Both (0 <= k /\ let prt = self.part in k < pSize(prt)) }
    requires { Agree self }
    requires { Agree k }
    requires { Agree pool }     /*XXX*/
    ensures { Both (let p = self.part in mem(result,pFind(k,p))) }
    ensures { Both (0 <= result /\ let p = self.part in result < pSize(p)) }
    ensures { Both (let id = self.id in id[result] = result) }
    ensures { Agree result }    /*XXX*/
    ensures { let s_alloc|s_alloc = old(alloc) | old(alloc) in
              Agree (alloc diff s_alloc)`any }
    effects { rd self, k, {self}`any, pool | rd self, k, {self}`any, pool }
  = ( var id: IntArray in id := self.id; result := id[k]
    | var id: IntArray in
      var idy: int in
      var y: int in
      id := self.id;
      y := k;
      idy := id[y];
      while y <> idy do
        invariant { 0 <= y /\ let prt = self.part in y < pSize(prt) }
        invariant { let prt = self.part in mem(y, pFind(k, prt)) }
        invariant { ufInv(self) }
        invariant { idy = id[y] }
        y := id[y];
        idy := id[y];
      done;
      result := y; )

  meth ufUnion (self: Ufind, x: int, y: int | self: Ufind, x: int, y: int) : (unit | unit)
    requires { Both (self in pool) }
    requires { Both (0 <= x /\ let p = self.part in x < pSize(p)) }
    requires { Both (0 <= y /\ let p = self.part in y < pSize(p)) }
    requires { Agree pool }
    requires { Agree {self}`any }
    requires { Agree self }
    requires { Agree x /\ Agree y }

    ensures { let s_alloc | s_alloc = old(alloc) | old(alloc) in
              let id | id = old ({self}`id) | old({self}`id) in
              let o_self | o_self = old({self}) | old({self}) in
              Agree (alloc diff (s_alloc union o_self))`any /* /\ Agree id`slots */ }
    /*XXX Just not true!  Why would we have agreement on id`slots?  Should
          id`slots appear in the effects clause in the first place?*/

    ensures { Both (let oid = old(self.id) in self.id = oid) }
    ensures { Both (let p = self.part in mem(x, pFind(y, p))) }
    ensures { Both (let op = old(self.part) in
                    let p = self.part in pSize(op) = pSize(p)) }
    effects { rd self, {self}`any, pool; wr {self}`any, {self}`id`slots
            | rd self, {self}`any, pool; wr {self}`any, {self}`id`slots }
  = Var ina: IntArray | ina: IntArray in
    Var xroot: int | xroot: int in
    Var yroot: int | yroot: int in
    Var ghost sid: int array | ghost sid: int array in
    |_ ina := self.id _|;
    {{ Both (forall p:Ufind in pool. p <> self -> p.id <> ina) }};
    ( sid := ina.slots | skip );
    |_ xroot := find(self, x) _|;
    |_ yroot := find(self, y) _|;
    If (xroot <> yroot) | (xroot <> yroot) then

      {{ eqReps(self | self) }}; /*XXX*/
      {{ eqRepsExcept(self, xroot | self, xroot) }};

      Var ghost prt: partition | ghost prt: partition in
      |_ prt := self.part _|;
      |_ self.part := pUnion(prt, pFind(x, prt), pFind(y, prt)) _|;

      {{ samePartition(self | self) }};

      Var i: int | i: int in
      Var len: int | len: int in
      ( i := 0 | skip );
      ( len := ina.length | skip );

      {{ forall p:Ufind in pool|p:Ufind in pool.
           Both (p <> self) -> p =:= p -> samePartition(p|p) /\ eqReps(p|p) }};

      ( while i < len do
          invariant { forall j:int. i <= j /\ j < len -> get(sid,j) = ina[j] }
          invariant { 0 <= i /\ i <= len }
          invariant { forall j:int. 0 <= j /\ j < i -> mem(j, pFind(x, prt)) -> ina[j] = yroot }
          invariant { forall j:int, k:int.
                        0 <= j /\ j < i ->
                        0 <= k /\ k < i ->
                        mem(j, pFind(k, prt)) -> let inaj = ina[j] in ina[k] = inaj }
          invariant { forall j:int. 0 <= j /\ j < i -> get(sid,j) = xroot -> ina[j] = yroot }
          invariant { forall j:int. 0 <= j /\ j < len -> get(sid,j) <> xroot -> ina[j] = get(sid,j) }
          invariant { forall j:int. 0 <= j /\ j < i ->
                        let inaj = ina[j] in
                        ~(mem(j, pFind(x, prt))) ->
                        mem(j, pFind(j, prt)) /\ inaj = get(sid,j) /\ ina[inaj] = inaj }
          invariant { forall p: Ufind in pool. p <> self -> p.id <> ina }
          effects { wr {ina}`slots }

          var inai: int in
          inai := ina[i];
          if inai = xroot then
            { get (sid,i) = xroot };
            ina[i] := yroot;
          else
            { get (sid,i) <> xroot };
          end;
          i := i+1;

          /* Assume some loop invariants -- this loop has already been verified
             in QuickFind */
          assume { forall j:int. 0 <= j /\ j < i ->
                     let inaj = ina[j] in
                     ~(mem(j, pFind(x, prt))) ->
                     mem(j, pFind(j, prt)) /\ inaj = get(sid,j) /\ ina[inaj] = inaj };
        done;
      | assert { forall p: Ufind in pool. p <> self -> p.id <> ina };
        ina[xroot] := yroot );

      {{ eqReps(self | self) }};
      {{ forall p:Ufind in pool|p:Ufind in pool.
           Both (p <> self) -> p =:= p -> samePartition(p|p) /\ eqReps(p|p) }};
      /* {{ eqRepsExcept(self, xroot | self, xroot) }}; */
    end;
    {{ eqReps(self | self) }};
    Assume { Both (ufPub()) /\ Both (ufPriv()) } /*assume invariants already verified*/

end
