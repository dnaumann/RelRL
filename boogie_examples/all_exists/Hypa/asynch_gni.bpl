/*
[forall]
int o;
int x;
int s;

o = 0;
while (x > 0) {
    x = x - 1;
    s = *;
    o = o + s;
}

[exists]
int o;
int x;
int s;
int t;

o = 0;
while (x > 0) {
    x = x - 1;
    s = *;
    t = o + s;
    o = t;
}

[pre]
x_0 == x_1

[post]
o_0 == o_1
*/

procedure biprog (x1: int,  x2: int) returns (o1:int, o2:int)
  requires x1 == x2;
  ensures o1 == o2;
{
    var a1: int; var a2: int;
    var s1: int; var s2: int;
    var t2: int;

    a1:= x1; a2 := x2;

    o1 := 0; o2 := 0;

    while (a1 > 0 && a2 > 0)
      invariant a1 == a2;
      invariant o1 == o2;
    {
        a1 := a1 - 1; a2 := a2 - 1;
        havoc s1 ;
        
        assert (exists v: int :: v == s1); // inserted by chk
        havoc s2 ;
        assume s2 == s1;

        o1 := o1 + s1;

        t2 := o2 + s2;
        o2 := t2;
    }
}