interface EMPTY =
end

module E : EMPTY =
  /* Example from Beutner'24: Automated software verification of hyperliveness */
  meth noninterference2 (h: int, l: int) : int
    effects { rd h, l }
  = var o: int in
    var x: int in
    if h > l then
      havoc x;
      o := l + x
    else
      havoc x; /* x := any nat */
      if (x > l) then
        o := x;
      else
        o := l
      end;
    end;
    result := o;

end

/* FIXME: Does not verify */
bimodule EREL (E | E) =

  meth noninterference2 (h: int, l: int | h: int, l: int) : (int | int)
    requires { Agree l }
    ensures { Agree result }
    effects { rd h, l | rd h, l }
  = Var o: int | o: int in
    Var x: int | x: int in

    If4 (h > l) | (h > l)

    thenThen
      ( havoc x | skip ); HavocR x { Agree x }; |_ o := l + x _|;

    thenElse

      ( havoc x; o := l+x
      | havoc x;
        if (x > l) then o := x else o := l end );

    elseThen
      ( havoc x;
        if (x > l) then o := x else o := l end
      | skip );
      HavocR x { Agree x };
      ( skip | o := l + x );

    elseElse
      ( havoc x;
        if (x > l) then o := x else o := l end
      | havoc x;
        if (x > l) then o := x else o := l end );
    end;
    |_ result := o _|;

end