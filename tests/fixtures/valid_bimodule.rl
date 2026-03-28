/* Valid program with a bimodule: two equivalent increment implementations */

interface I =
  meth inc (n: int) : int
    ensures { result = n + 1 }
    effects { rd n }
end

module A : I =
  meth inc (n: int) : int =
    result := n + 1;
end

module B : I =
  meth inc (n: int) : int =
    var x: int in
    x := 1;
    result := n + x;
end

bimodule AB (A | B) =
  meth inc (n: int | n: int) : (int | int)
    requires { n =:= n }
    ensures  { result =:= result }
end
