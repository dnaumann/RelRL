interface I =
  meth counter_diff(t: int) : int
    effects { rd t }
end

module A : I =
  meth counter_diff (t: int) : int
  =
  var k: int in 
  var x: int in
  
  k := t; 
  result := 0; 
  
  havoc x;
  while(k > 0) do
      k := k - 1;
      result := result + x;
  done;
end


bimodule FREL (A | A) =
  meth counter_diff (t: int | t: int) : (int | int)
    requires { t =:= t }
    ensures  { [< result <] = [> -result >] }                 
  = 
    Var k: int | k: int in
    Var x: int | x: int in
    
    |_ k := t _|; 
    |_ result := 0 _|;
    
    (havoc x | skip);
    HavocR x { [> x >] = [< -x <] };

    While(k > 0) |  (k > 0) .  [> false |> | [> false |> do
          invariant { result =:= -result }
          invariant { k =:= k }
          invariant { t =:= t }
      |_ k := k - 1 _|;
      |_ result := result + x _|
    done;

end
