module QuickUnion : UNIONFIND =

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
    (forall x:int. 0 <= x /\ x < len -> let idx = id[x] in mem(idx, pFind(x, prt)))

  private invariant ufPriv = forall p: Ufind in pool. ufInv(p)

  meth Ufind (self: Ufind, k: int) : unit =
    var i: int in
    var ina: IntArray in
    ina := new IntArray[k];
    i := 0;
    while i < k do
      invariant { 0 <= i /\ i <= k }
      invariant { forall j: int. 0 <= j -> j < i -> ina[j] = j }
      effects { wr {ina}`slots }
      ina[i] := i;
      i := i+1;
    done;
    self.id := ina;
    self.part := pMake(k);
    var rep : rgn in
    rep := self.rep;
    self.rep := rep union {ina};
    pool := pool union {self}

  meth find (self: Ufind, k: int) : int
    ensures { let id = self.id in id[result] = result }
  = var id: IntArray in
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
    result := y;

  meth ufUnion (self: Ufind, x: int, y: int) : unit
  = var ina: IntArray in
    var xroot: int in
    var yroot: int in
    ina := self.id;
    xroot := find(self,x);
    yroot := find(self,y);
    if xroot <> yroot then
      var ghost prt: partition in
      prt := self.part;
      self.part := pUnion(prt, pFind(x,prt), pFind(y,prt));
      ina[xroot] := yroot;
    end;

end
