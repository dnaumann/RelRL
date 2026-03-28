/* This file has a type error: method body returns wrong type (int vs unit) */

interface I =
  meth f (n: int) : unit
    effects { rd n }
end

module M : I =
  meth f (n: int) : unit =
    result := n + 1;
end
