/* 
[forall]
int o;

if * {
    o = 1;
} else {
    o = 2;
}

[exists]
int o;

if * {
    o = 1;
} else {
    o = 2;
}

[pre]
true

[post]
o_0 == o_1
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
  
