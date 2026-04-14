/* Semantic Program Alignment for Equivalence Checking
   Churchill et al. PLDI'19

   int f (uint n, uint m) {
     int k = 0;
     for (uint i = 0; i < n; ++i) {
       for (uint j = 0; j < m; ++j) {
         k++;
       }
     }
     return k;
   }

   int g (uint n, uint m) {
     int k = 0;
     for (uint i = 0; i < n; ++i) {
       k += m;
     }
     return k;
   }

 */

interface I =
  meth multiply (n: int, m: int) : int
    requires { n >= 0 /\ m >= 0 }
    ensures { result = n * m }
    effects { rd n, m }
end

module M1 : I =

  meth multiply (n: int, m: int) : int =
    var i : int in
    var j : int in
    /* The ghost variable below is needed to express an invariant in the
       biprogram.  It keeps track of the value of result before executing the
       inner while loop.  See the biprogram below for details.
     */
    var ghost tmp : int in
    i := 0;
    while (i < n) do
      invariant { 0 <= i /\ i <= n}
      invariant { result = i*m }
      j := 0;
      tmp := result;
      while (j < m) do
        invariant { 0 <= j /\ j <= m }
        invariant { result = i*m + j }
        result := result + 1;
        j := j + 1;
      done;
      i := i + 1;
    done;

end

module M2 : I =

  meth multiply (n: int, m: int) : int =
    var i : int in
    i := 0;
    while (i < n) do
      invariant { 0 <= i /\ i <= n }
      invariant { result = i*m }
      result := result + m;
      i := i + 1;
    done;

end

bimodule MREL (M1 | M2) =

  meth multiply (n: int, m: int | n: int, m: int) : (int | int)
    requires { Both (n >= 0) /\ Both (m >= 0) }
    requires { n =:= n /\ m =:= m }
    ensures { result =:= result }
  = Var i : int | i : int in
    Var j : int | j : int in
    Var ghost tmp : int | ghost tmp : int in
    |_ i := 0 _|;
    While (i < n) | (i < n) . <| false <] | [> false |> do
      invariant { Both (0 <= i /\ i <= n) }
      invariant { i =:= i }
      invariant { result =:= result }
      ( j := 0 | skip );
      ( tmp := result;
        /* Ideally, the invariant in the while loop below should be:

             result = old(result) + j

           However, old r in a loop invariant in Why3 refers to the value of r
           at the start of the function and not right before the loop.  To get
           around this, we use the tmp ghost variable to keep track of the value
           of result before executing the loop below.

           Another approach would be to use a Why3 label right before the loop.
           At this point, WhyRel does not support user-defined labels so we
           cannot follow this approach.

           Since WhyRel does not have a notion of "bicode", unary ghost code
           that can refer to values in both programs, the (unary) left
           implementation must be polluted with the tmp variable.
         */
        while (j < m) do
          invariant { 0 <= j /\ j <= m }
          invariant { result = tmp + j }
          result := result + 1;
          j := j + 1;
        done;
      | result := result + m );
      {{ result =:= result }};
      |_ i := i + 1 _|
    done;

end
