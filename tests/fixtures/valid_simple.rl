/* Minimal valid program: a simple identity method */

interface I =
  meth id_int (n: int) : int
    ensures { result = n }
    effects { rd n }
end

module M : I =
  meth id_int (n: int) : int =
    result := n;
end
