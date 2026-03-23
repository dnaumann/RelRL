/*
https://github.com/rcdickerson/rhle-benchmarks/blob/main/gni/denning3.imp

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