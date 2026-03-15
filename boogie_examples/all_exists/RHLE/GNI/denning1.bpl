/*

// Example adapted from secure information flow lecture notes:
// https://people.cs.vt.edu/~ryder/6304/lectures/10-Denning&Denning-InfoFlow-CACM7-97-KrishnanMurali.pdf

expected: valid;

forall: denning[A];
exists: denning[E];

pre: (and
        (= denning!A!f1_L  denning!E!f1_L)
        (= denning!A!f2_L  denning!E!f2_L));

post: (and
        (= denning!A!f1_L  denning!E!f1_L)
        (= denning!A!f2_L  denning!E!f2_L));

fun denning(f1_L, f2_L, f3_H, f4_H) {
  i   := 1;
  n   := 0;
  sum := 0;
  while (i <= 100) do
    @inv { (and
             (= denning!A!f1_L  denning!E!f1_L)
             (= denning!A!f2_L  denning!E!f2_L)
             (= denning!A!i denning!E!i))}
    @var { (- 300 (+ denning!A!i denning!E!i)) }
    flag := f1_L;
    f2_L := flag;
    x := f3_H;
    if (!(flag == 0)) then
      n := n + 1;
      sum := sum + x;
    endif
    i := i + 1;
  end
  f4_H := n + sum + (sum / n);
  return f4_H;
}

*/


var f1_l_1, f1_l_2, f2_l_1, f2_l_2 : int;
var f3_h_1, f3_h_2, f4_h_1, f4_h_2 : int;

function integer_divide (dividend: int, divisor: int) returns (int);

// axiom (forall x, y, z: int  :: (y != 0 && integer_divide(x, y) == z) <==> y * z == x);

// verifies
procedure biprog () returns ()
  requires f1_l_1 == f1_l_2 && f2_l_1 == f2_l_2;
  ensures f1_l_1 == f1_l_2 && f2_l_1 == f2_l_2;
  modifies f1_l_1, f1_l_2, f2_l_1, f2_l_2, f4_h_1, f4_h_2;
{
  var i1, i2: int;
  var n1, n2: int;
  var sum1, sum2: int;
  var flag1, flag2: int;
  var x1, x2: int;

  i1 := 1; i2 := 1;
  n1 := 0; n2 := 0;
  sum1 := 0; sum2 := 0;

  while (i1 <= 100 && i2 <= 100) 
    invariant f1_l_1 == f1_l_2 && f2_l_1 == f2_l_2;
    invariant i1 == i2;
  {
      flag1 := f1_l_1; flag2 := f1_l_2;

      f2_l_1 := flag1; f2_l_2 := flag2;

      x1 := f3_h_1; x2 := f3_h_2;


      if (!(flag1 == 0)) 
      {
            n1 := n1 + 1;
            sum1 := sum1 + x1;
      }

      if (!(flag2 == 0)) 
      {
            n2 := n2 + 1;
            sum2 := sum2 + x2;
      }
      i1 := i1 + 1; i2 := i2 + 1;
  }

    // assert (n1 != 0 && n2 != 0);
    f4_h_1 := n1 + sum1 + integer_divide(sum1, n1); 
    f4_h_2 := n2 + sum2 + integer_divide(sum2, n2);

}  