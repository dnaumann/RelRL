/*

[forall]
int o;
int x;

o = 0;
while (x > 0) {
    x = x - 1;
    if * {
        o = o + 1;
    } else {
        o = o + 2;
    }
}

[exists]
int o;
int x;
int s;

o = 0;
while (x > 0) {
    x = x - 1;
    s = *;
    o = o + s;
}

[pre]
x_0 == x_1

[post]
o_0 == o_1

*/

/* Hack to trigger instantiation. */
function inst<a>(x: a) : bool { true }  


procedure biprog (x1: int,  x2: int) returns (o1:int, o2:int)
  requires x1 == x2;
  ensures o1 == o2;
{
    var a1: int; var a2: int;
    var s2: int;
    var b1: bool;

    a1:= x1; a2 := x2;

    o1 := 0; o2 := 0;

    while (a1 > 0 && a2 > 0)
      invariant a1 == a2;
      invariant o1 == o2;
    {
        a1 := a1 - 1; a2 := a2 - 1;
        havoc b1 ;

        if (b1) 
        {
            o1 := o1 + 1;
        }
        else
        {
            o1 := o1 + 2;

        }
        assert inst(o1 - o2); // alert prover about instantiation candidate
        assert (exists v: int :: {inst(v)} v == o1 - o2); // inserted by chk
        havoc s2 ;
        assume s2 == o1 - o2;

        o2 := o2 + s2;
    }
}