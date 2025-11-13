interface I =

  public f1_l : int
  public f2_l : int
  public f3_h: int
  public f4_h: int
  
  meth prog () : int
    effects { rw f1_l, f2_l, f3_h, f4_h}
end

module A : I =
  meth prog () : int
/*

fun denning(f1_L, f2_L, f3_H, f4_H) {
  i   := 1;
  n   := 0;
  sum := 0;
  while (i <= 100) do
    @inv { (and
             (= denning!A!f1_L  denning!E!f1_L)
             (= denning!A!f2_L  denning!E!f2_L)
             (= denning!A!i     denning!E!i)) }
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
  f2_L := n + sum + (sum / n);
  f1_L := f2_L;
  return f1_L;
}

pre: (and
        (= denning!A!f1_L  denning!E!f1_L)
        (= denning!A!f2_L  denning!E!f2_L));

post: (and
        (= denning!A!f1_L  denning!E!f1_L)
        (= denning!A!f2_L  denning!E!f2_L));
*/
end

/* should not and does not verify however the division operation needs the fact n != 0  to go through as well */
bimodule FREL (A | A) =
  meth prog (|) : (int |int )
  requires { f1_l =:= f1_l /\ f2_l =:= f2_l}
  ensures { f1_l =:= f1_l /\ f2_l =:= f2_l }
  effects { rw f1_l, f2_l, f3_h, f4_h | rw f1_l, f2_l, f3_h, f4_h}
 =

  Var i : int | i: int in
  Var n : int | n: int in
  Var sum: int | sum: int in
  Var flag: int | flag: int in
  Var x: int | x: int in

  |_ i := 1 _|;
  |_ n := 0 _|;
  |_ sum := 0 _|; 

  While (i <= 100) | (i <= 100) .  <| false <] | [> false |> do 
    invariant { f1_l =:= f1_l /\ f2_l =:= f2_l}
    invariant { i =:= i }
  
      |_ flag := f1_l _|; 

      |_ f2_l := flag _|; 

      |_ x := f3_h _|; 


    ( if ((flag <> 0)) then
      n := n + 1;
      sum := sum + x;
    end | skip );

     (skip | if ((flag <> 0)) then
      n := n + 1;
      sum := sum + x;
    end );
      
      |_ i := i + 1 _|; 
  done;

    |_ f2_l := n + sum +  (sum / n) _|; 
    |_ f1_l := f2_l _|;

end
