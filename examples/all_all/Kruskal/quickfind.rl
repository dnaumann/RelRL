module QuickFind : UNIONFIND =

  class IntArray {length: int; slots: int array;}
  class Ufind {id: IntArray; ghost part: partition; ghost rep: rgn;}

  predicate ufInv (p: Ufind) =
    p <> null /\
    let id = p.id in
    id <> null /\
    let len = id.length in
    let prt = p.part in
    len = pSize(prt) /\
    p.rep = {id} /\
    (forall x:int. 0 <= x /\ x < len -> let idx = id[x] in 0 <= idx /\ idx < len) /\
    (forall x:int. 0 <= x /\ x < len -> let idx = id[x] in id[idx] = idx) /\
    (forall x:int, y:int. 0 <= x /\ x < len -> 0 <= y /\ y < len ->
       let idx = id[x] in
       let idy = id[y] in
       mem(y, pFind(x,prt)) <-> idx = idy)

  private invariant ufPriv = forall p: Ufind in pool. ufInv(p)

  /* for all elements x of the partitioned set, id[x] belongs to the same
     partition as x in the abstract partition. */
  lemma qfind1 : forall p: Ufind in pool, x:int.
    ufPriv () ->
    let prt = p.part in
    let id = p.id in
    0 <= x /\ x < pSize(prt) ->
    let idx = id[x] in
    mem(idx,pFind(x,prt))

  /* for all elements x of the partitioned set, if i is in the partition of x
     and id[i] = i, then i is the representative of the partition of x. */
  lemma qfind2 : forall p: Ufind in pool, x: int, i: int.
    ufPriv() ->
    let prt = p.part in
    let id = p.id in
    0 <= x /\ x < pSize(prt) ->
    0 <= i /\ i < pSize(prt) ->
    mem(i,pFind(x,prt)) ->
    id[i] = i ->
    id[x] = i

  meth Ufind (self: Ufind, k: int) : unit =
    var i: int in
    var prt: IntArray in
    { ufPriv() };
    prt := new IntArray[k];
    i := 0;
    { ufPriv() };
    { forall p:Ufind in pool. p <> self -> p.id <> prt };
    while (i < k) do
      invariant { let s = prt.slots in length(s) = k }
      invariant { forall p:Ufind in pool. p <> self -> p.id <> prt }
      invariant { 0 <= i /\ i <= k }
      invariant { forall j: int. 0 <= j -> j < i -> prt[j] = j }
      invariant { ufPriv() }
      invariant { ufPub() }
      writes { {prt}`slots }
      prt[i] := i;
      i := i+1;
    done;
    self.id := prt;
    self.part := pMake(k);
    var rep : rgn in
    rep := self.rep;
    self.rep := rep union {prt};
    { ufInv(self) };
    { ufPub() };
    pool := pool union {self};

  meth find (self: Ufind, k: int) : int
    ensures { let id = self.id in id[result] = result }
  = var id: IntArray in
    id := self.id;
    result := id[k];

  meth ufUnion (self: Ufind, x: int, y: int) : unit
  = var ina: IntArray in
    var xroot: int in var yroot: int in
    var ghost sid: int array in
    ina := self.id;
    sid := ina.slots;
    xroot := find(self,x);
    yroot := find(self,y);
    if xroot <> yroot then
       { ufInv(self) };

       var ghost prt: partition in
       prt := self.part;
       self.part := pUnion(prt, pFind(x,prt), pFind(y,prt));

       var i: int in var len: int in
       i := 0;
       len := ina.length;
       { forall j:int. 0 <= j /\ j < len -> get(sid,j) = ina[j] };

       while i < len do
         invariant { forall j:int. i <= j /\ j < len -> get(sid,j) = ina[j] }
         invariant { 0 <= i /\ i <= len }
         invariant { forall j:int. 0 <= j /\ j < i ->
                     let prt = self.part in
                     mem(j, pFind(x, prt)) -> ina[j] = yroot }
         invariant { forall j:int, k:int.
                       let prt = self.part in
                       0 <= j /\ j < i ->
                       0 <= k /\ k < i ->
                       mem(j, pFind(k, prt)) -> let inaj = ina[j] in ina[k] = inaj }
         invariant { forall j:int. 0 <= j /\ j < len -> get(sid,j) <> xroot -> ina[j] = get(sid,j) }
         invariant { forall j:int. 0 <= j /\ j < i -> get(sid,j) = xroot -> ina[j] = yroot }
         invariant { forall j:int. 0 <= j /\ j < i ->
                       let inaj = ina[j] in
                       let prt = self.part in
                       ~(mem(j, pFind(x, prt))) ->
                       mem(j, pFind(j, prt)) /\ inaj = get(sid,j) /\ ina[inaj] = inaj }

         effects { wr {ina}`slots }

         var inai: int in
         inai := ina[i];
         if inai = xroot then
            { get(sid,i) = xroot };
            ina[i] := yroot;
         else
            { get(sid,i) <> xroot };
         end;
         i := i+1;
       done;
       { i = len };
       { ufInv(self) };
    end;

end
