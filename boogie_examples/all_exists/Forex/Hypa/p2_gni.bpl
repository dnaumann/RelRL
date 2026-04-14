/*
https://github.com/ravenbeutner/ForEx/blob/main/benchmarks/hypa/p2_gni.txt
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