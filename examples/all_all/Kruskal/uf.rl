interface UNIONFIND =

  import theory Partition

  extern type intset with default = emptyIntset
  extern type partition with default = pEmpty

  extern predicate mem (int,intset)

  extern pMake (int) : partition
  extern pFind (int,partition) : intset
  extern pUnion (partition,intset,intset) : partition
  extern pSize (partition) : int

  class IntArray {length: int; slots: int array;}
  class Ufind {ghost part: partition; ghost rep: rgn;}

  public pool : rgn

  boundary { pool, pool`any, pool`rep`any }

  public invariant ufPub =
    (forall p:Ufind in pool, q:Ufind in pool.
      p <> q ->
      let prep = p.rep in let qrep = q.rep in
      prep # qrep /\ p notin qrep)

  meth Ufind (self: Ufind, k: int) : unit
    requires { ~ (self in pool) }
    requires { self.rep = {} }
    requires { k > 0 }
    ensures { self.part = pMake(k) }
    ensures { let prt = self.part in pSize(prt) = k }
    ensures { self in pool }
    ensures { let oa = old(alloc) in ({self}`rep) subset (alloc diff oa)  }
    effects { rd self, k; rw {self}`any, {self}`rep`any, pool, alloc }

  meth find (self: Ufind, k: int) : int
    requires { self in pool }
    requires { 0 <= k /\ let p = self.part in k < pSize(p) }
    ensures { let p = self.part in mem(result,pFind(k,p)) }
    ensures { 0 <= result /\ let p = self.part in result < pSize(p) }
    effects { rd self, k, {self}`any, {self}`rep`any; wr result }

  meth ufUnion (self: Ufind, x: int, y: int) : unit
    requires { self in pool }
    requires { 0 <= x /\ let p = self.part in x < pSize(p) }
    requires { 0 <= y /\ let p = self.part in y < pSize(p) }
    ensures { let p = self.part in mem(x,pFind(y,p)) }
    ensures { let op = old(self.part) in let p = self.part in pSize(op) = pSize(p) }
    ensures { let orep = old(self.rep) in self.rep = orep }
    effects { rd self, x, y; rw {self}`any, {self}`rep`any }

end
