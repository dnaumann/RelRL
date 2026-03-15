/*

[forall]
int h;
int o;
int l;
int b;

if (h > 0) {
    o = l + b;
} else {
    o = l + b;
}

[exists]
int h;
int o;
int l;
int b;

if (h > 0) {
    o = l + b;
} else {
    o = l + b;
}

[pre]
l_0 == l_1 
&& 
b_0 == b_1

[post]
o_0 == o_1

*/


procedure biprog (l1: int,  l2: int, b1: int, b2: int) 
    returns (o1: int, o2: int)
  requires l1 == l2;
  requires b1 == b2;
  ensures o1 == o2;
{
    var h1: int; var h2: int;

    havoc h1;

    if (h1 > 0 )
    {
        o1 := l1 + b1;  
    }
    else
    {
        o1 := l1 + b1;  
    }

    assert (exists v: int :: v == h1);
    havoc h2;
    assume h2 == h1;
    if (h2 > 0)
    {
        o2 := l2 + b2;  
    }
    else
    {
        o2 := l2 + b2;  
    }
}