interface I =
  meth prog () : int
    effects {  }
end

module A : I =
  meth prog () : int
/*
aspecs:
  biggerRand() {
    post: (and (<= 0 ret!) (< ret! 11));
  }


fun refinement() {
  sum := 0;
  while (sum <= 100) do
    @inv { (= original!sum refinement!sum) }
    r := biggerRand();
    sum := sum + r;
  end
  return sum;
}
*/
end

module B : I =
  meth prog () : int
/*  =
especs:
  rand() {
    choiceVars: n;
    pre:  (and (<= 0 n) (< n 10));
    post: (= ret! n);
  }

fun original() {
  sum := 0;
  while (sum <= 100) do
    @inv { (= original!sum refinement!sum) }
    r := rand();
    sum := sum + r;
  end
  return sum;
}


  pre:  true;
  post: (= original!sum refinement!sum);
*/
end

/* should not and does not verify */
bimodule FREL (A | B) =
  meth prog (|) : (int | int)
  ensures { result =:= result }
 =
  
  Var r: int | r: int in
  Var sum: int | sum : int in
  
  |_ sum := 0 _|; 

  While (sum <= 100) | (sum <= 100) .  <| false <] | [> false |> do
   invariant {sum =:= sum} 
  
    
    (havoc r | skip ); 
    (assume { 0 <= r && r < 11 } | skip);
    
    (sum := sum + r | skip);

    HavocR r { [> 0 <= r /\   r  < 10 |> /\ [< r <] = [> r >]}; 

    (skip | sum := sum + r);
  done;

  |_ result := sum _|;
end
