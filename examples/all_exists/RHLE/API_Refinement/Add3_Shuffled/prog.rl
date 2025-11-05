interface I =

  meth prog (l:intList) : intList
    effects { rd n }
end

module A : I =
  meth prog (l:intList) : intList
end

module B : I =
  meth prog (l:intList) : intList
end


bimodule FREL (A | B) =

  import List3

  meth prog (l: intList|  l: intList) : (intList | intList)
  requires { equals3( [< l <], [> l >] ) }
  ensures { equals3( [< result <] , [> result >] ) }
 =

    Var shuffle_ret: intList | sort_ret : intList in
    Var | n0 : int in
    Var | n1 : int in
    Var | n2 : int in
    Var temp : int | temp : int in

     /* left program calls shuffle with universal spec */
    (havoc shuffle_ret; assume { is_permutation3(l, shuffle_ret) } | skip);

     /* right program calls sort with existential spec instantiated with shuffle_ret */
    (skip | n0 := shuffle_ret[0];
     n1 := shuffle_ret[1];
     n2 := shuffle_ret[2]);

     Assert { [< is_permutation3(l, shuffle_ret) <]};
     (skip | assume {n0 <= n1 /\ n1 <= n2 });
     HavocR sort_ret {[> sorted3(sort_ret) >]  /\ [> is_permutation3(sort_ret, l) >]  };
     Assert { let x | x = shuffle_ret | sort_ret in x =:= x};

     (l := shuffle_ret | l := sort_ret);
     
     |_ temp := l[0] _|;  
     |_ l[0] := temp + 3 _|;  
     |_ temp := l[1] _|;  
     |_ l[1] := temp + 3 _|;  
     |_ temp := l[2] _|;  
     |_ l[2] := temp + 3 _|;  

     |_ result := l _|; 

end