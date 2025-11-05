/* figure 1 examples is adapted to show refinement of arr based map against function maps
*/

interface Map =

  import IntList
  extern type intList with default = nil
  extern hd(intList) : int
  extern tl(intList) : intList
  extern cons(int,intList) : intList
  extern listNth(int,intList) : int
  extern listLength(intList) : int

  class Map {sz : int; ghost contents: intList; }

/*  ∀ sz. {true} init(sz) {★_k∈[0,sz) k ↦→Map 0} */
  meth Map (self: Map, sz: int): unit
    ensures { let l = self.contents in (listLength(l) = sz /\ forall k:int . (0 <= k && k < sz) -> listNth(l, k) = 0) }
/*
  ∀k w v. {k ↦Map w} set(k,v) {k ↦Map v}
  meth set (self: Map, k: int, v: int) : unit
    requires {exists w : int :: get(self, k) = w }
    ensures {get(self, k) == v}  

  ∀k w v. {k ↦Map v} get(k,v) {r. r = v ∧ k ↦Map v}
  meth get (self:Map, k: int) : int
    requires {exists v :int:: get(self, k) = v}
    ensures {result == get(self, k)}

  ∀k w. {k ↦Map w} set_by_user(k) {∃v. k ↦Map v}
  meth set_by_user_I (k:int);
    ensures { exists v :int :: map_I[k] == v }
*/
end

module Map_Array : Map =

/*
  def init(sz: int) ≡
    data := calloc(sz)

  def get(k: int): int ≡
    return *(data + k)

  def set(k: int, v: int) ≡
    *(data + k) := v

  def set_by_user(k: int) ≡
    set(k, input())
*/


  class Map
  {
    data : int array;
    size : int;
    ghost contents: intList;
  }


  meth Map (self: Map, sz: int) :  unit =
    var i: int in
    var temp_intarray: int Array in
    var temp_intlist: int in

    self.contents := nil;
    i := 0;
    while (i < sz) do
      temp_intarray := self.data;
      self.data := set(temp_intarray, i, 0);
      temp_intlist := self.contents;
      self.contents := cons(0, templist);
      i := i + 1;
    done;

    self.size := sz;
  
/*
  meth set (self: Map, k:int, v: int) : unit =
      self.value[k] := v;
    end;

  meth get (self: Map, k: int) : int =
    result := self.value[k];

  meth set_by_user (self: Map, k: int) : unit =
    var v:int;
    havoc v;
    self.data[k] := v;
*/
end



module Map_Fun : Map =

  import IntFun
  extern type int_fun with default = empty_fun

  class Map { data: int_fun; sz: int; ghost contents: intList;}

  meth Map (self: Map, sz: int) :  unit =
    var i: int in
    var temp_intlist: int in

    self.contents := nil;
    i := 0;
    while (i < sz) do
      temp_intlist := self.contents;
      self.contents := cons(0, templist);
      i := i + 1;
    done;

    self.data := empty_fun;
    self.sz := sz;
  /*
  meth set (self: Map, k:int, v: int) : unit =
    var i: int;
    i := 1;
    var curr_node: Node;
    curr_node := self.start;

    while (i <= k) do
      i := i + 1;
      curr_node := curr_node.next; 
    done;
    curr_node.val := v;
    end;

  meth get (self: Map, k: int) : int =
    var i: int;
    i := 1;
    var curr_node: Node;
    curr_node := self.start;

    while (i <= k) do
      i := i + 1;
      curr_node := curr_node.next; 
    done;
    curr_node.val := v;
    end;

  meth set_by_user (self: Map, k: int) : unit =
    var i: int;
    var v: int;
    i := 1;
    var curr_node: Node;
    curr_node := self.start;

    while (i <= k) do
      i := i + 1;
      curr_node := curr_node.next; 
    done;
    havoc v;
    curr_node.val := v;
    end;
*/
end

bimodule MAP_REL ( Map_Array | Map_Fun ) =



  meth Map (self: Map, sz: int | self: Map, sz:int) : (unit | unit)
    requires { sz =:= sz }
    requires { Both (sz >= 0) }
    ensures {let x|x = self.sz | self.sz in x =:= x}
    ensures {forall i:int|i:int. (let x | x = self.sz | self.sz in Both (0 <= i /\ i < x)) -> 
                i =:= i -> (let x| x = self.contents | self.contents in  let v|v = x[i]|x[i] in v =:= v)}
    effects  { rw {self}`any, alloc | rw {self}`any, alloc }
  = 
    Var i: int | i: int in
    Var temp_intarray: int Array | in
    Var temp_intlist: int | temp_intlist: int in

    |_ self.contents := nil _|;
    |_ i := 0 _|;
    While (i < sz) | (i < sz) . <| false <] | [> false |> do
      (temp_intarray := self.data | skip) ;
      (self.data := set(temp_intarray, i, 0) | skip);
      |_ temp_intlist := self.contents _|;
      |_ self.contents := cons(0, templist) _|;
      |_ i := i + 1 _|;
    done;

    (skip | self.data := empty_fun);
    |_ self.sz := sz _|;

  end

/*
  meth set (self: Map, k: int, v: int | self:Map, k:int, v: int) : (unit | unit)
    requires { cellC(|) }
    ensures  { cellC(|) }
    requires { Both (self in pool) }
    requires { Both (cellP()) }
    requires { Both (cellI()) }
    requires { let rep|rep = self.rep|self.rep in rep =:= rep }
    requires { let vl|vl = self.value|self.value in vl =:= -vl }
    requires { k =:= k }
    requires { Both (k >= 0) }
    ensures  { let rep|rep = self.rep|self.rep in rep =:= rep }
    ensures  { Both (cellP()) }
    ensures  { Both (cellI()) }
    effects  { rw {self}`any, alloc, pool; rd k
             | rw {self}`any, alloc, pool; rd k }
  = Assert { self =:= self };
    ( self.value := k
    | if k <= 0 then self.value := k else self.value := -k end; );

  meth get (self: Map, k: int | self: Map, k: int) : (int | int)
    requires { cellC(|) }
    ensures  { cellC(|) }
    requires { Both (self in pool) }
    requires { Both (cellP()) }
    requires { Both (cellI()) }
    requires { let rep|rep = self.rep|self.rep in rep =:= rep }
    requires { let vl|vl = self.value|self.value in vl =:= -vl }
    ensures  { Both (cellP()) }
    ensures  { Both (cellI()) }
    ensures  { Both (result >= 0) }
    ensures  { result =:= result }
    effects  { rw {self}`any, alloc, pool
             | rw {self}`any, alloc, pool }
  = ( result := self.value
    | var value : int in
      value := self.value;
      result := -value );

end

procedure A_refines_S(sz: int)
  requires sz >= 0;
  modifies map_A, map_I;
  ensures (forall k: int :: 0 <= k && k < sz ==> map_A[k] == map_I[k]);
{
    var i:int;

    call init_A(sz);
    call init_I(sz);
    
    i := 0;
    
    while (i < sz)
      invariant 0 <= i && i <= sz;
      invariant (forall k: int :: (0 <= k && k < i) ==> map_A[k] == map_I[k]);
    {
        call set_by_user_A(i);
        call set_by_user_I(i);
        i := i + 1;
    }
}


module Main =
  import CELL related by CELL_REL

  meth main(x:int) : int
    requires { pool = {} }
    requires { x >= 0 }
    effects { rw alloc, pool, x }
  = var c : Cell in
    c := new Cell;
    var k : int in
    k := 0;
    Cell (c,k);
    { c in alloc };
    x := x + 1;
    cset (c, x);
    result := cget (c);

end
*/
