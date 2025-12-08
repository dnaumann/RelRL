/*

[forall]
int h;
int o;

if (h > 0) {
    o = - o;
} else {
    o = -o + (h - h);
}

[exists]
int h;
int o;

if (h > 0) {
    o = - o;
} else {
    o = -o + (h - h);
}

[pre]
o_0 == o_1

[post]
o_0 == o_1

*/


procedure biprog (a1: int,  a2: int) returns (o1: int, o2: int)
  requires a1 == a2;
  ensures o1 == o2;
{
    var h1: int; var h2: int;

    o1 := a1; o2 := a2;

    havoc h1;

    if (h1 > 0 )
    {
        o1 := -o1;  
    }
    else
    {
        o1 := -o1 + (h1 - h1); 
    }

    assert (exists v: int :: v == h1);
    havoc h2;
    assume h2 == h1;
    if (h2 > 0)
    {
        o2 := -o2;        
    }
    else
    {
        o2 := -o2 + (h2 - h2);
    }
}