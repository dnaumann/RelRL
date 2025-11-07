/* figure 1 examples is adapted to show refinement of arr based map against function maps
*/

interface MAP =

  import theory Map_Theory
  extern type intList with default = nil
  extern hd(intList) : int
  extern tl(intList) : intList
  extern cons(int,intList) : intList
  extern listNth(int,intList) : int
  extern listLength(intList) : int
  extern upd_list(int, int, intList): intList
  extern create_list(int, int): intList

  class Map {sz   : int; ghost contents: intList; }

  predicate map_inv (self: Map) = let sz = self.sz in let l = self.contents in listLength(l) = sz /\  0 <= sz

/*  ∀ sz. {true} init(sz) {★_k∈[0,sz) k ↦→Map 0} */
  meth Map (self: Map, sz : int): unit
    requires {0 <= sz}
    ensures {self.sz = sz}
    ensures { map_inv (self)}
    ensures {let l = self.contents in (forall k:int . (0 <= k /\k < sz) -> listNth(k, l) = 0) }
    effects {rd self, sz; rw {self}`any }


/*  ∀k w v. {k ↦Map w} set(k,v) {k ↦Map v} */ 
  meth set_val (self: Map, k: int, v: int) : unit
    requires {let sz = self.sz in 0 <= k /\ k < sz}
    requires {map_inv (self)}
    ensures {let old_sz = old(self.sz) in self.sz = old_sz}
    ensures {let l = self.contents in let old_l = old(self.contents) in l = upd_list(k , v, old_l) }  
    ensures  {map_inv (self)}
    effects {rd self, v, k; rw {self}`any}
    
    /*  ∀k w v. {k ↦Map v} get(k,v) {r. r = v ∧ k ↦Map v} */
    meth get_val (self:Map, k: int) : int
      requires {map_inv (self)}
      requires {let sz = self.sz in 0 <= k /\ k < sz}
      ensures {map_inv (self)}
      ensures { let l = self.contents in result = listNth(k, l)}
      effects {rd self, {self}`any }

  /* ∀k w. {k ↦Map w} set_by_user(k) {∃v. k ↦Map v} */
  meth set_by_user (self: Map, k:int): unit
    requires {let sz = self.sz in 0 <= k /\ k < sz}
    requires { map_inv (self)}
    ensures {let old_sz = old(self.sz) in self.sz = old_sz}
    ensures { map_inv (self)}
    ensures {exists v: int . let l = self.contents in let old_l = old(self.contents) in l = upd_list(k , v, old_l) }
    effects {rd self, k; rw {self}`any}

end

module Map_Array : MAP =

  class Map
  {
    sz  : int;
    ghost contents: intList;
    data : int array;
  }

  predicate map_array_priv (self: Map) = let sz = self.sz in
      let arr = self.data in length(arr) = sz /\
      forall i: int. (0 <= i /\ i < sz) -> let arr = self.data in let l = self.contents in get(arr, i) = listNth(i, l)

  meth Map (self: Map, sz: int) :  unit 
    ensures { map_array_priv (self) }
    =
    self.data := make(sz, 0);
    self.contents := create_list(sz, 0);
    self.sz := sz;
  
  meth set_val (self: Map, k:int, v: int) : unit 
        requires { map_array_priv (self) }
        ensures { map_array_priv (self) }
        
    =
    var temp_intarray: int array in
    var ghost temp_intlist: intList in

    temp_intarray := self.data;
    self.data := set(temp_intarray, k, v);
    temp_intlist := self.contents;
    self.contents := upd_list(k, v, temp_intlist);

    
  meth get_val (self: Map, k: int) : int 
    requires {map_array_priv (self)}
    =
    var temp_intarray: int array in

    temp_intarray := self.data;

    result := get(temp_intarray, k);
   
    
  meth set_by_user (self: Map, k: int) : unit 
          requires { map_array_priv (self) }
        ensures { map_array_priv (self) }
  =
    var v:int in 
    havoc v;
    set_val(self, k, v);

end

module Map_Fun : MAP =

  import theory Map_Theory
  extern type int_fun with default = empty_fun
  extern const empty_fun : int_fun
  extern add_mapping(int, int, int_fun) : int_fun
  extern get_fn_val(int, int_fun): int

  class Map { sz  : int; ghost contents: intList; data_fn: int_fun; }

    predicate map_fn_priv (self: Map) = let sz = self.sz in forall i: int. (0 <= i /\ i < sz) -> let fn = self.data_fn in let l = self.contents in get_fn_val(i, fn) = listNth(i, l)

  meth Map (self: Map, sz: int) :  unit 
    ensures {map_fn_priv (self)}
    =
    self.data_fn := empty_fun;
    self.contents := create_list(sz, 0);
    self.sz  := sz;
    
  meth set_val (self: Map, k:int, v: int) : unit 
    requires {map_fn_priv (self)}
    ensures {map_fn_priv (self)}
    =
    var temp_fn: int_fun in
    var ghost temp_intlist: intList in  
    
    temp_fn := self.data_fn;
    
    self.data_fn := add_mapping (k, v, temp_fn);
    temp_intlist := self.contents;
    self.contents := upd_list(k, v, temp_intlist);
    
  meth get_val (self: Map, k: int) : int 
    requires {map_fn_priv (self)}
    ensures {map_fn_priv (self)}
    =
    var temp_fn: int_fun in
    
    temp_fn := self.data_fn;
    result := get_fn_val(k, temp_fn)
    
    
  meth set_by_user (self: Map, k: int) : unit 
    requires {map_fn_priv (self)}
    ensures {map_fn_priv (self)}
  =
    var v:int in 
    havoc v;
    set_val(self, k, v);

end

bimodule MAP_REL ( Map_Array | Map_Fun ) =

  meth Map (self: Map, sz: int | self: Map, sz  :int) : (unit | unit)
    requires { sz  =:= sz  }
    requires { Both (sz  >= 0) }
    ensures {Both (map_inv (self))}
    ensures {let x|x = self.sz  | self.sz   in x =:= x}
    ensures {forall i:int|i:int . (let x | x = self.sz  | self.sz   in Both (0 <= i /\ i < x)) ->
       (let x| x = self.contents | self.contents in  let v|v = listNth(i, x) | listNth(i, x) in Both (v = 0))}
    effects  {rd self, sz; rw {self}`any| rd self, sz; rw {self}`any }
    = 
    ( self.data := make(sz, 0) | self.data_fn := empty_fun);
    |_ self.contents := create_list(sz, 0) _|;
    |_ self.sz := sz _|;

  meth set_val (self: Map, k: int, v: int | self:Map, k:int, v: int) : (unit | unit)
    requires {let sz | sz = self.sz | self.sz in sz =:= sz}
    requires {let l | l = self.contents | self.contents in l =:= l}
    requires { k =:= k /\ v =:= v}
    requires {Both (map_inv (self))}
    requires {Both (let sz = self.sz in 0 <= k /\ k < sz)}
    requires { <| map_array_priv (self) <] }
    requires { [> map_fn_priv (self) |> }
    ensures { [> map_fn_priv (self) |> }
    ensures { <| map_array_priv (self) <] }
    ensures {let l | l = self.contents | self.contents in l =:= l}
    ensures {let sz | sz = self.sz | self.sz in sz =:= sz}
    ensures {Both (map_inv (self))}
    effects  { rw {self}`any;  rd self, v, k | rw  {self}`any; rd self, v, k }
    = 
    Var temp_intarray: int array | temp_fn: int_fun in
    Var ghost temp_intlist: intList | ghost temp_intlist: intList in
    
    (temp_intarray := self.data | temp_fn := self.data_fn) ;
    (self.data := set(temp_intarray, k, v) | self.data_fn := add_mapping (k, v, temp_fn));
    |_ temp_intlist := self.contents _|;
    |_ self.contents := upd_list(k, v, temp_intlist) _|;
    
  meth get_val (self: Map, k: int | self: Map, k: int) : (int | int)
    requires {Both (map_inv (self))}
    requires {Both (let sz = self.sz in 0 <= k /\ k < sz)}
    requires { <| map_array_priv (self) <] }
    requires { [> map_fn_priv (self) |> }
    requires { k =:= k }
    requires {let l | l = self.contents | self.contents in l =:= l}
    ensures { result =:= result }
    effects {rd self, {self}`any | rd self, {self}`any  }
  =  Var temp_intarray: int array | temp_fn: int_fun in

    (temp_intarray := self.data | temp_fn := self.data_fn);

    (result := get(temp_intarray, k) | result := get_fn_val(k, temp_fn));

  meth set_by_user (self: Map, k:int | self: Map, k:int): (unit | unit)
    requires {Both (let sz = self.sz in 0 <= k /\ k < sz)}
    requires { k =:= k }
    requires {Both (map_inv (self))}
    requires { <| map_array_priv (self) <] }
    requires { [> map_fn_priv (self) |> }
    requires {let l | l = self.contents | self.contents in l =:= l}
    ensures {Both (let old_sz = old(self.sz) in self.sz = old_sz)}
    ensures {let l | l = self.contents | self.contents in l =:= l}
    effects {rd self, k; rw {self}`any | rd self, k; rw {self}`any}  
    =
      Var v:int | v:int in 
      (havoc v | skip);
      HavocR v { v =:= v };
      |_ set_val(self, k, v) _|;  


end
/*


end

procedure A_refines_S(sz: int)
  requires sz  >= 0;
  modifies map_A, map_I;
  ensures (forall k: int :: 0 <= k && k < sz  ==> map_A[k] == map_I[k]);
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
