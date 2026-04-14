/*

From figure 1 in 2023 CCR POPL paper. https://doi.org/10.1145/3571232

(* module I Map *)
  private data := NULL

  def init(sz: int) ≡
    data := calloc(sz)

  def get(k: int): int ≡
    return *(data + k)

  def set(k: int, v: int) ≡
    *(data + k) := v

  def set_by_user(k: int) ≡
    set(k, input())

(* module A_Map *)
  private map := (fun k => 0)

  def init(sz: int) ≡
    skip

  def get(k: int): int ≡
    return map[k]

  def set(k: int, v: int) ≡
    map := map[k ← v]

  def set_by_user(k: int) ≡
    set(k, input())

(* pre & postconditions S_Map *)

  ∀ sz. {pending} init(sz) {★_k∈[0,sz) k ↦→Map 0}
  ∀k w v. {k ↦Map w} set(k,v) {k ↦Map v}
  ∀k w v. {k ↦Map v} get(k,v) {r. r = v ∧ k ↦Map v}
  ∀k w. {k ↦Map w} set_by_user(k) {∃v. k ↦Map v}

*/


// >>> S_Map definition >>>
var map_I : [int]int;

procedure init_I(sz:int);
  requires sz >= 0;
  modifies map_I;
  ensures (forall k:int :: (0 <= k && k < sz) ==> map_I[k] == 0);

procedure get_I(k:int) returns (r:int);
  requires (exists v :int:: map_I[k] == v);
  ensures r == map_I[k];

procedure set_I(k:int, v:int);
  modifies map_I;
  ensures map_I[k] == v;  

procedure set_by_user_I(k:int);
  modifies map_I;
  ensures (exists v :int :: map_I[k] == v);

// <<< S_Map definition <<<


// >>> A_Map definition >>>

var map_A : [int]int;

procedure init_A(sz:int)
  requires sz >= 0;
  ensures (forall k :int :: 0 <= k && k < sz ==> map_A[k] == 0);
  modifies map_A;
{
    var i: int;

    i := 0;
    while (i < sz)
      invariant 0 <= i && i <= sz;
      invariant (forall k: int :: 0 <= k && k < i ==> map_A[k] == 0);
    {
        map_A[i] := 0;
        i := i + 1;
    }
}

procedure get_A(k:int) returns (r:int)
  requires (exists v :int:: map_A[k] == v);
  ensures r == map_A[k];
{
    r := map_A[k];
}

procedure set_A(k:int, v:int)
  modifies map_A;
  ensures map_A[k] == v;
{
    map_A[k] := v;
}

procedure set_by_user_A(k:int)
  modifies map_A;
  ensures (exists v: int :: map_A[k] == v);
{
    var v:int;
    havoc v;
    map_A[k] := v;
}

// <<< A_Map definition <<<


// >>> A_Map refines S_Map >>>


procedure A_refines_I(sz: int)
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

// <<< A_Map refines S_Map <<<


