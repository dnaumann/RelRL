interface I =
end

module A : I =
/*
*/
end

/* Should and does verify */
bimodule FREL (A | A) =
  meth prog (|) : (int |int )
 =
  Var flipcoin_ret: int | flipcoin_ret: int in
  
  HavocR flipcoin_ret {( [> True |> -> [> True |>) /\
                       ([> True |> -> [> True |>)};
    
end
