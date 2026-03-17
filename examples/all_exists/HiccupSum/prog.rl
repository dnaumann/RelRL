interface A =
    import theory HiccupSum_Theory

    extern bool2int(bool) : int

    meth main (n: int): int

end

module M: A =

    meth main (n: int): int

end

bimodule MM (M | M) =

    import theory HiccupSum_Theory

    meth main (n: int | n: int ) : (int |int)
        requires {n =:= n}
        ensures {result =:= result}
    =
     Var i : int | i: int in
     Var h: bool | h: bool in

     |_ i := 0 _|;
     |_ result := 0 _|;
     (havoc h | skip); HavocR h { h =:= h };

     While (i < n) | (i < n) . <| h <] | [> h |>  do
        invariant {i =:= i}
        invariant {result =:= result}
        variant {[> bool2int(h) >]}

        If (not h) | (not h) then
            |_ result := result + i _|;
            |_ i := i + 1 _|;
        end;
        (havoc h | skip);
        HavocR h { h =:= h };

    done;

    end



