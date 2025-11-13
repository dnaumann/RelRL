interface I =


  public cs: int
  public cr: int
  public ci: int
  public ct: int
  public ccs: int
  public ccr: int
  public cci: int
  public cct: int
  public res: int

  meth prog () : int
end

module A : I =
  meth prog () : int

end



/* verifies */
bimodule FREL (A | A) =
  meth prog (|) : (int |int )
  requires {(cs =:= ccs) /\
            (cr =:= ccr) /\
            (ci =:= cci) /\
            (ct =:= cct) /\
            (ccs =:= cs) /\
            (ccr =:= cr) /\
            (cci =:= ci) /\
            (cct =:= ct)}
  ensures { Both (result = 0) \/
            (<| result < 0 <] /\ [> result > 0 |> ) \/
             (<| result > 0 <] /\ [> result < 0 |> )}
 =
   
    |_ result := cs - ccs _|; 

    (if (result = 0) then
        result := cr - ccr;
     end | if (result = 0) then
        result := cr - ccr;
     end );

    (if (result = 0) then
        result := ci - cci;
     end | if (result = 0) then
        result := ci - cci;
     end );

    (if (result = 0) then
        result := ct - cct;
     end | if (result = 0) then
        result := ct - cct;
     end );


end
