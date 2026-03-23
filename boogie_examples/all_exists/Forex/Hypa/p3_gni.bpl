/* 
https://github.com/ravenbeutner/ForEx/blob/main/benchmarks/hypa/p3_gni.txt
*/

procedure gni () returns (o1: int, o2: int)
          ensures  o1 == o2;
{
  var x1: bool; var x2: bool;

  havoc x1;
  if (x1)
  {
    o1 := 1;
  }
  else{
    o1 := 2;
  }

  assert (exists v: bool :: v == x1);
  havoc x2;
  assume (x2 == x1);
  if (x2)
  {
    o2 := 1;
  }
  else{
    o2 := 2;
  }
}
  
