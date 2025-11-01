interface I =

  public i_l : int
  public e_l : int
  public f_l: int
  public sum_h: int

  meth prog (x_h: int) : int
    effects { rw i_l, e_l, f_l, sum_h}
end

module A : I =
  meth prog (x_h: int) : int
/*

*/
end

module B : I =
  meth prog (x_h: int) : int
/*  =

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

pre: (and
        (= denning!A!f1_L  denning!E!f1_L)
        (= denning!A!f2_L  denning!E!f2_L));

post: (and
        (= denning!A!f1_L  denning!E!f1_L)
        (= denning!A!f2_L  denning!E!f2_L));
*/
end

/* should not and does not verify  */
bimodule FREL (A | B) =
  meth prog (x_h: int|x_h : int) : (int |int )
  requires { i_l =:= i_l /\ e_l =:= e_l}
  ensures { i_l =:= i_l /\ e_l =:= e_l }
  effects {  rw i_l, e_l, f_l, sum_h  | rw i_l, e_l, f_l, sum_h}
 =

  Var max_sum : int | max_sum: int in
  Var oob_error: int | oob_error: int in
 
  |_ max_sum := 100 _|; 
  |_ oob_error := 0 _|;
  |_ sum_h := 0 _|; 
  |_ i_l := 0 _|; 
  |_ e_l := 1 _|;

  While ((e_l = 1) and (oob_error = 0)) | (e_l = 1 and oob_error = 0) .  <| false <] | [> false |> do  
    invariant { i_l =:= i_l /\ e_l =:= e_l }
    invariant { <| e_l = 1 /\  oob_error = 0 <] <-> [> e_l = 1 /\ (oob_error = 0) |>}

      |_ sum_h := sum_h + x_h _|; 

      |_ i_l := i_l + 1 _|; 

      |_ f_l := i_l _|; 

      (if (sum_h > max_sum)
       then
        oob_error := 1;
       end | skip );

      (skip | if (sum_h > max_sum)
       then
        oob_error := 1;
       end );
  done; 
end
