interface I =


  public l: int
  public h: int

  meth prog () : int
    effects { rw l, h}
end

module A : I =
  meth prog () : int
/*
aspecs:
  parity(val) {
    pre: true;
    post: (= ret! (mod val 2));
  }

*/
end

module B : I =
  meth prog () : int
/*  =

especs:
  parity(val) {
    pre: true;
    post: (= ret! (mod val 2));
  }

fun run() {
  p := parity(h);
  if (p == 1) then
    l := 1;
    h := 1;
  else
    l := 0;
    h := 0;
  endif
  return 0;
}

pre: (and
        (= run!1!l run!2!l)

        // Delimited Release
        (= (mod run!1!h 2) (mod run!2!h 2)));

post: (= run!1!l run!2!l);
*/
end

/* verifies */
bimodule FREL (A | B) =
  meth prog (|) : (int |int )
  requires {l =:= l}
  requires { [< h mod 2 <] = [> h mod 2 >] } /* delimited release */
  effects {rw l, h | rw l, h}
  ensures { l =:= l }
 =

  Var p: int | p: int in

  /* left prog calls with universal spec */
  (havoc p | skip ); 
  (assume { h mod 2 = p } | skip);

  /* right prog calls with existential spec */
  HavocR p { [> h mod 2 = p |> /\  p  =:=  p }; 

  (if (p = 1) then
    l := 1;
    h := 1;
  else
    l := 0;
    h := 0;
  end | skip);

  (skip | if (p = 1) then
            l := 1;
            h := 1;
          else
            l := 0;
            h := 0;
          end);
end
