interface CLIENT =
end

/* interface TEST_CLIENT = import STACK end
module TestClient : TEST_CLIENT =
  meth prog (n: int) : int
    requires { maxSize > n /\ n >= 0 }
    requires { pool = {} }
    effects  { rw alloc, pool, pool`any, pool`rep`any, result; rd n, maxSize }
   = var stk: Stack in
    var i: int in
    var c: Cell in
    stk := new Stack; Stack(stk); assert { stk in pool };
    while (i < n) do
      invariant { 0 <= i /\ i <= n }
      invariant { stk in pool /\ 0 <= n /\ n < maxSize }
      invariant { let sz = stk.size in sz = i }
      invariant { stackPub() }
      invariant { let oa = old(alloc) in 
                  (({stk} union {stk}`rep) diff {null}) subset (alloc diff oa) }
      effects { rw alloc, {stk}`any, {stk}`rep`any }
      push(stk, i);
      i := i+1;
    done;
    i := 0;
    while (i < n) do
      invariant { 0 <= i /\ i <= n }
      invariant { stk in pool /\ 0 <= n /\ n < maxSize }
      invariant { let sz = stk.size in sz = n-i }
      invariant { stackPub() }
      invariant { c = null \/ let rep = stk.rep in c in rep }
      invariant { let oa = init(alloc) in 
                  (({stk} union {stk}`rep) diff {null}) subset (alloc diff oa) }
      effects { rw {stk}`any, {stk}`rep`any }
      c := pop(stk);
      var v: int in v := getCellValue(c);
      result := result + v;
      i := i+1;
    done;
end 
*/

/* Version of client linked against ArrayStack */
module Client1 : CLIENT =
  import ArrayStack
  meth prog (n: int) : int
    requires { maxSize > n /\ n >= 0 }
    requires { pool = {} }
    effects  { rw alloc, pool, pool`any, pool`rep`any, result; rd n, maxSize }
  = var stk: Stack in
    var i: int in
    var c: Cell in
    stk := new Stack; Stack(stk); assert { stk in pool };
    while (i < n) do
      invariant { 0 <= i /\ i <= n }
      invariant { stk in pool /\ 0 <= n /\ n < maxSize }
      invariant { let sz = stk.size in sz = i }
      invariant { stackPub() /\ arrayStackPriv () }
      /* stk and all objects in stk.rep are fresh */
      invariant { let oa = old(alloc) in 
                  (({stk} union {stk}`rep) diff {null}) subset (alloc diff oa) }
      /* effects { rw alloc, pool, pool`any, pool`rep`any } */
      effects { rw alloc, {stk}`any, {stk}`rep`any }
      push(stk, i); /* ensures that all fresh objects are in {stk}`rep */
      i := i+1;
    done;
    i := 0;
    while (i < n) do
      invariant { 0 <= i /\ i <= n }
      invariant { stk in pool /\ 0 <= n /\ n < maxSize }
      invariant { let sz = stk.size in sz = n-i }
      invariant { stackPub() /\ arrayStackPriv () }
      invariant { c = null \/ let rep = stk.rep in c in rep }
      invariant { let oa = init(alloc) in 
                  (({stk} union {stk}`rep) diff {null}) subset (alloc diff oa) }
      /* effects { rw alloc, pool, pool`any, pool`rep`any, result } */
      effects { rw {stk}`any, {stk}`rep`any }
      c := pop(stk);
      var v: int in v := getCellValue(c);
      result := result + v;
      i := i+1;
    done;

end

/* Version of client linked against ListStack */
module Client2 : CLIENT =
  import ListStack
  meth prog (n: int) : int
    requires { maxSize > n /\ n >= 0 }
    requires { pool = {} }
    effects  { rw alloc, pool, pool`any, pool`rep`any, result; rd n, maxSize }
   = var stk: Stack in
    var i: int in
    var c: Cell in
    stk := new Stack; Stack(stk);
    while (i < n) do
      invariant { 0 <= i /\ i <= n }
      invariant { stk in pool /\ 0 <= n /\ n < maxSize }
      invariant { let sz = stk.size in sz = i }
      invariant { stackPub() /\ listStackPriv() }
      invariant { let oa = old(alloc) in
                  (({stk} union {stk}`rep) diff {null}) subset (alloc diff oa) }
      effects { rw alloc, {stk}`any, {stk}`rep`any }
      push(stk, i);
      i := i+1;
    done;
    i := 0;
    while (i < n) do
      invariant { 0 <= i /\ i <= n }
      invariant { stk in pool /\ 0 <= n /\ n < maxSize }
      invariant { let sz = stk.size in sz = n-i }
      invariant { stackPub() /\ listStackPriv() }
      invariant { c = null \/ let rep = stk.rep in c in rep }
      invariant { let oa = init(alloc) in
                  (({stk} union {stk}`rep) diff {null}) subset (alloc diff oa) }
      /* effects { rw alloc, pool, pool`any, pool`rep`any, result }*/
      effects   { rw {stk}`any, {stk}`rep`any }
      c := pop(stk);
      var v: int in v := getCellValue(c);
      result := result + v;
      i := i+1;
    done;

end

/* Rel verif of client -- proving equivalence of the two versions */
bimodule CLIENT_REL (Client1 | Client2) =
  import REL_STACK
  meth prog (n: int | n: int) : (int | int)
    requires { Both (maxSize > n) /\ Both (n >= 0) /\ Agree n }
    requires { Both (pool = {}) }
    ensures  { Agree result }
    effects  { rw alloc, pool, pool`any, pool`rep`any, result; rd n, maxSize
             | rw alloc, pool, pool`any, pool`rep`any, result; rd n, maxSize }
   = Var stk: Stack | stk: Stack in
    Var i: int | i: int in
    Var c: Cell | c: Cell in
    |_ stk := new Stack _|; Connect stk with stk; |_ Stack(stk) _|;
    While (i < n) | (i < n) . do
      invariant { Both (0 <= i) /\ Both(i <= n) /\ Both(stk in pool) }
      invariant { Agree i /\ Agree n /\ Both(0 <= n) /\ Both(n < maxSize) }
      invariant { let xs|xs = stk.contents|stk.contents in Agree xs }
      invariant { Both(let sz=stk.size in sz=i) }
      invariant { Both(stackPub()) }
      invariant { Both(let oa=old(alloc) in (({stk} union {stk}`rep) diff {null}) subset (alloc diff oa)) }
      effects { rw alloc, {stk}`any, {stk}`rep`any
              | rw alloc, {stk}`any, {stk}`rep`any }
      |_ push(stk, i) _|;
      |_ i:=i+1 _|;
    done;
    |_ i:=0 _|; Assert { Agree result };
    While (i < n) | (i < n) . do
      invariant { Both (0 <= i) /\ Both (i <= n) }
      invariant { Agree i /\ Agree n }
      invariant { Both(stk in pool) /\ Both(0 <= n) /\ Both(n < maxSize) }
      invariant { Both(let sz = stk.size in sz = n-i) }
      invariant { Both(c = null \/ let rep = stk.rep in c in rep) }
      invariant { Both(stackPub()) }
      invariant { let xs|xs = stk.contents|stk.contents in Agree xs }
      invariant { Agree result }
      invariant { Both(let oa = init(alloc) in (({stk} union {stk}`rep) diff {null}) subset (alloc diff oa))}
      effects { rw {stk}`any, {stk}`rep`any
              | rw {stk}`any, {stk}`rep`any }
      |_ c := pop(stk) _|;
      Var v: int | v: int in |_ v := getCellValue(c) _|;
      /* rel spec for getCellValue: if you start with two cells with the same cell_value
         you get back the same result; Agreement on c.cell_value in pre, not on c */
      |_ result := result + v _|;
      |_ i := i+1 _|;
    done;

end

