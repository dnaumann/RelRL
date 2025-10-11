interface I =
end

module A : I =

  meth test (n: int) : int
    effects { rd n }
  = var x: int in
    x := n;
    result := x;

end

module B : I =

  meth test (n: int) : int
    effects { rd n }
  = var x: int in
    var b: int in
    x := 0;
    havoc b;
    while b <> 0 do
      x := x+1;
      havoc b;
    done;
    result := x

end

bimodule AB (A | B) =

  meth test (n: int | n: int) : (int | int)
    requires { Both (n >= 0) }
    ensures { Agree result }
    effects { rd n | rd n }
  = Var x: int | x: int in
    Var | b: int in
    ( x := n | x := 0 );
    HavocR b { [> b >] = [< x <] - [> x >] };

    WhileR b <> 0 do
      invariant { [< x <] >= [> x >] }
      invariant { [> b >] = [< x <] - [> x >] }
      variant { [> b >] }

      (skip | x := x+1);
      HavocR b { [> b >] = [< x <] - [> x >] }

    done;
    |_ result := x _|;

end


