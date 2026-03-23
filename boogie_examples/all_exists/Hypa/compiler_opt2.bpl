// https://github.com/ravenbeutner/ForEx/blob/main/benchmarks/hypa/compiler_opt2.txt


procedure compiler_opt_2 (time1: int, time2: int) returns (o1: int, o2: int)
          requires time1 == time2;
          ensures  o1 == o2;
// should verify successfully
{
  var x1: int; var x2: int;
  var s2: int;
  var s1: int;
  var t1: int;
  var g1: int; // temp 


  x1 := time1; x2 := time2;
  o1 := 0; o2 := 0;

  while (x1 > 0 || x2 > 0)
        invariant x1 == x2;
        invariant o1 == o2;
        // adequacy
        invariant (x1 > 0) <==> (x2 > 0);
  {
    x1 := x1 - 1; x2 := x2 - 1;

    havoc t1;
    while (t1 > 0)
    {
        t1 := t1 - 1;
        havoc s1;
        o1 := o1 + s1;
    }
    
    g1 := o1 - o2; // temp to help z3 
    assert (exists v: int :: v == g1); 
    havoc s2;
    assume s2 == o1 - o2;
    o2 := o2 + s2;
  }
}

