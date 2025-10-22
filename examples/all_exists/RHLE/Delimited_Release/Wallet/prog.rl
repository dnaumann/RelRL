interface I =

  public funds: int
  public spent: int
  public cost: int
  
  meth prog () : int
    effects { rw funds, spent, cost}
end

module A : I =
  meth prog () : int
/*

*/
end

module B : I =
  meth prog () : int
/*  =



fun buy(funds, spent, cost) {
  if (funds >= cost) then
    funds := funds - cost;
    spent := spent + cost;
  else
    skip;
  endif
  return 0;
}

pre: (and
       (= buy!1!spent buy!2!spent)
       (= buy!1!cost buy!2!cost)

       // Delimited Release
       (and (>= buy!1!funds buy!1!cost) (>= buy!2!funds buy!2!cost)));

post: (= buy!1!spent buy!2!spent);
*/
end

/* verifies */
bimodule FREL (A | B) =
  meth prog (|) : (int |int )
  requires { spent =:= spent }
  requires { <| funds >= cost <] /\ [> funds >= cost |> } /* delimited release */
  requires { cost =:= cost }
  effects {rw funds, spent, cost | rw funds, spent, cost } 
  ensures { spent =:= spent }
 =

  (if (funds >= cost) then
    funds := funds - cost;
    spent := spent + cost;
  else
    skip;
  end | skip);

  (skip | if (funds >= cost) then
    funds := funds - cost;
    spent := spent + cost;
  else
    skip;
  end);

end
