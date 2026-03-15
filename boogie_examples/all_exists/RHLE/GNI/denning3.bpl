/*

// Example adapted from secure information flow lecture notes:
// https://people.cs.vt.edu/~ryder/6304/lectures/10-Denning&Denning-InfoFlow-CACM7-97-KrishnanMurali.pdf

expected: invalid;

forall: denning[A];
exists: denning[E];

pre: (and
        (= denning!A!i_L  denning!E!i_L)
        (= denning!A!e_L  denning!E!e_L));

post: (and
        (= denning!A!i_L  denning!E!i_L)
        (= denning!A!e_L  denning!E!e_L));

fun denning(i_L, e_L, f_L, x_H, sum_H) {
  max_sum := 100;
  oob_error := 0;

  sum_H := 0;
  i_L := 0;
  e_L := 1;
  while ((e_L == 1) && (oob_error == 0)) do
    @inv { (and
             (= denning!A!f1_L  denning!E!f1_L)
             (= denning!A!f2_L  denning!E!f2_L)
             (= denning!A!i denning!E!i))}
    @var { (- 300 (+ denning!A!sum_H denning!E!sum_H)) }
    sum_H := sum_H + x_H;
    i_L := i_L + 1;
    f := i;
    if sum_H > max_sum then
      oob_error := 1;
    endif
  end

  if (oob_error == 1) then
    ret := 0;
  else
    ret := 1;
  endif
  return ret;
}

*/


var i_l_1, i_l_2, e_l_1, e_l_2 : int;
var f_l_1, f_l_2 : int;
var sum_h_1, sum_h_2 : int;


// this should not and does not verify
procedure biprog (x_h_1, x_h_2: int) returns ()
  requires i_l_1 == i_l_2 && e_l_1 == e_l_2;
  ensures i_l_1 == i_l_2 && e_l_1 == e_l_2;
  modifies i_l_1, i_l_2, e_l_1, e_l_2, f_l_1, f_l_2;
  modifies sum_h_1, sum_h_2;
{
  var max_sum_1, max_sum_2: int;
  var oob_error_1, oob_error_2: int;
 
  max_sum_1 := 100; max_sum_2 := 100;
  oob_error_1 := 0; oob_error_2 := 0;
  sum_h_1 := 0; sum_h_2 := 0;
  i_l_1 := 0; i_l_2 := 0;
  e_l_1 := 1; e_l_2 := 1;

  while ((e_l_1 == 1 && (oob_error_1 == 0)) ||
         (e_l_2 == 1 && (oob_error_2 == 0))) 
    invariant i_l_1 == i_l_2 && e_l_1 == e_l_2;
    invariant (e_l_1 == 1 && (oob_error_1 == 0)) <==>
              ( e_l_2 == 1 && (oob_error_2 == 0));
  {
      sum_h_1 := sum_h_1 + x_h_1; sum_h_2 := sum_h_2 + x_h_2;

      i_l_1 := i_l_1 + 1; i_l_2 := i_l_2 + 1;

      f_l_1 := i_l_1; f_l_2 := i_l_2;

      if (sum_h_1 > max_sum_1)
      {
        oob_error_1 := 1;
      }

      if (sum_h_2 > max_sum_2)
      {
        oob_error_2 := 1;
      }
  }

}  