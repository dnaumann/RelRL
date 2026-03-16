/* Example from
   Modular Product Programs (Marco Eilers, Peter Müller, Samuel Hitz)
   Fig 1.
*/

interface I =

  class IntArray {length: int; slots: int array;}

  meth is_female (person: int) : int
    effects { rd person }

  meth count_female (people: IntArray) : int
    effects { rd people, {people}`any }

end

module M : I =

  class IntArray {length: int; slots: int array;}

  meth is_female (person: int) : int =
    var gender: int in
    gender := person mod 2;
    if gender = 0 then result := 1
                  else result := 0
    end;

  meth count_female (people: IntArray) : int =
    var i: int in
    var count: int in
    var len: int in
    len := people.length;
    while i < len do
      invariant { 0 <= i /\ i <= len }
      var current: int in
      var f: int in
      current := people[i];
      f := is_female(current);
      count := count + f;
      i := i + 1;
    done;
    result := count;

end

bimodule MREL (M | M) =

  predicate same_array (a: IntArray | a: IntArray) =
    Both (a <> null) ->
    let len|len = a.length|a.length in
    len =:= len /\
    (forall i:int|i:int. Both (0 <= i /\ i < len) -> i =:= i ->
       let v|v = a[i]|a[i] in v =:= v)

  meth is_female (person: int | person: int) : (int | int)
    requires { person =:= person }
    ensures { result =:= result }
  = Var gender: int | gender: int in
    |_ gender := person mod 2 _|;
    If (gender = 0) | (gender = 0)
       then |_ result := 1 _|;
       else |_ result := 0 _|;
    end;

  meth count_female (people: IntArray | people: IntArray) : (int | int)
    requires { same_array(people|people) }
    ensures { result =:= result }
  = Var i: int | i: int in
    Var count: int | count: int in
    Var len: int | len: int in
    |_ len := people.length _|;
    While (i < len) | (i < len) . <| false <] | [> false |> do
      invariant { i =:= i }
      invariant { count =:= count }
      invariant { Both (0 <= i /\ i <= len) }

      Var current: int | current: int in
      Var f: int | f: int in
      |_ current := people[i] _|;
      |_ f := is_female(current) _|;
      |_ count := count + f _|;
      |_ i := i + 1 _|;
    done;
    |_ result := count _|;

end
