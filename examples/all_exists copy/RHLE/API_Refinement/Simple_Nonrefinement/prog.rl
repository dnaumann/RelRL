interface I =
  meth prog () : int
    effects {  }
end

module A : I =
  meth prog () : int
/*
aspecs:
  refinedRand() {
      pre:  true;
      post: (and (>= ret! 0) (< ret! 25));
  }

fun refinement() {
  x := refinedRand();
  return x;
}

*/
end

module B : I =
  meth prog () : int
/*  =
especs:
  originalRand() {
      choiceVars: n;
      pre:  (and (>= n 0) (< n 20));
      post: (= ret! n);
  }

fun original() {
  x := originalRand();
  return x;
}
  pre:  true;
  post: (= original!x refinement!x);
*/
end

/* should not and does not verify */
bimodule FREL (A | B) =
  meth prog (|) : (int | int)
  ensures { result =:= result }
 =
  
  Var z: int | z: int in

  (havoc z | skip ); 
  (assume { 0 <= z /\ z < 25 } | skip);


  HavocR z { [> 0 <= z /\   z  < 20 |> /\ [< z <] = [> z >]}; 

  |_ result := z _|;
end
