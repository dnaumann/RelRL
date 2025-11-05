interface List =

  class List



  meth map (self: List, sz: int): unit
    requires { sz >= 0 }
    modifies { forall k:int :: (0 <= k && k < sz) ==> map_I[k] == 0 }

  meth set (self: List, k: int, v: int) : unit
    requires {exists w : int :: get(self, k) = w }
    ensures {get(self, k) == v}  

  meth get (self:List, k: int) : int
    requires {exists v :int:: get(self, k) = v}
    ensures {result == get(self, k)}

  meth set_by_user_I (k:int);
    ensures { exists v :int :: map_I[k] == v }

end


module List_Array : List =

  class List
  {
    data : int array;
    size : int;
  }

  meth List (self: List, sz: int) :  unit =
    var i: int;
    i := 0;
    while (i < sz) do
      self.data[i] := 0;
      i := i + 1;
    done;

    self.size = sz;
  

  meth set (self: List, k:int, v: int) : unit =
      self.value[k] := v;
    end;

  meth get (self: List, k: int) : int =
    result := self.value[k];

  meth set_by_user (self: List, k: int) : unit =
    var v:int;
    havoc v;
    self.data[k] := v;

end


module List_LinkedList : Map =

  class Node { key: int; val: int; next: Node }
  class Map { first: Node}

  meth Node (self: Node, val: int, next: Node) : unit =
    self.val := val;
    self.next := null;

  meth Map (self: Map, sz: int) :  unit =
    var i: int;
    var curr_node: Node;
    var start_node: Node;
    start_node := null;

    if (sz > 0) then
      start_node := Node(0, null);
    end;

    curr_node := start_node;

    i := 1;
    while (i < sz) do
      curr_node.next := Node(0, null);
      curr_node := curr_node.next;
      i := i + 1;
    done;

    self.first := start_node; 
    self.size = sz;
  
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

end


bimodule List_REL ( List_Array | List_LinkedList ) =

  meth Map (self: List, sz: int | self: List, sz:int) : (unit | unit)
    requires { sz =:= sz }
    requires { Both (sz >= 0) }
    ensures {Both (self.sz = sz)}
    effects  { rw {self}`any, alloc | rw {self}`any, alloc }
  = 
    Var i: int | ;
    (i := 0;
    (while (i < sz) do
      self.data[i] := 0;
      i := i + 1;
    done;

  self.size = sz;
  ( self.sz := k
    | if k <= 0 then self.value := k else self.value := -k end; );
    Assert { Both (k >= 0) -> let v|v = self.value|self.value in v =:= -v };
    |_ self.rep := {self} _|;
    |_ pool := pool union {self} _|;

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

  meth Array_refines_LinkedList(sz: int)
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


