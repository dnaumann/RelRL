interface A =
  public err: bool

end


module M : A =

  meth errAssert(b: bool) : unit
  requires {not err}
  ensures {err = not b}
  effects {rw err}

  meth main (hi: int, lo: int) : unit

end

bimodule MM (M | M) =

  meth main (hi: int, lo: int | hi: int, lo: int) : (int | int)
    requires { <| err = false <] /\ [>  err = false |> }
    requires { lo =:= lo }
    ensures  { err =:= err }
    effects  { rw err | rw err }
  = 
    Var temp: bool | temp: bool in

    (if (hi > 0) then temp := not (lo < 0); errAssert (temp) end;
      if (not err) then 
          if (lo < 0) then temp:= false; errAssert(temp) end 
      end |
    if (hi > 0) then temp := not (lo < 0); errAssert (temp) end;
      if (not err) then 
          if (lo < 0) then temp:= false; errAssert(temp) end 
      end);


end
