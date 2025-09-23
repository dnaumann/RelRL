/* Fig 5 in Itzhaky et al

Original code (in boogie syntax)

  sum1 := 0;
  havoc b1;
  if (b1 > 0)
  { i1 := 0;
    while (i1 < n1 - 1)
    { sum1 := sum1 + A1[i1]; i1 := i1 + 1; }
  } else {
    i1 := 1;
    while (i1 < n1)
    { havoc y1; sum1 := sum1 + A1[i1] + y1; i1 := i1 + 1; } 
  }

Their spec is in OHyperLTL and asserts alignment of iterations.
We use postcondition that describes after last iteration, see below.
*/

/* Hack to trigger instantiation. */
function inst<a>(x: a) : bool { true }  

procedure p (A1: [int] int, A2: [int] int, n1: int, n2: int) 
          returns (sum1: int, sum2: int, b1: int, b2: int)
          requires A1 == A2 && n1 == n2;
          ensures b2 < 0 && sum1 == sum2; 
{ 
  var i1: int; var i2: int;  var y1: int; var y2: int;

  sum1 := 0;
  havoc b1;
  sum2 := 0;
  havoc b2;
  assume b2 < 0; 

  if (b1 > 0 && b2 > 0) { // unreachable 
    i1 := 0;
    while (i1 < n1 - 1)
    { sum1 := sum1 + A1[i1]; i1 := i1 + 1; }
    i2 := 0;
    while (i2 < n2 - 2)
    { sum2 := sum2 + A2[i2]; i2 := i2 + 1; }
  } else {
  if (b1 > 0 && b2 <= 0) { 
    i1 := 0; i2 := 1;
    while (i1 < n1 - 1 && i2 < n2)
       invariant i1 < n1 - 1 <==> i2 < n2; 
       invariant i1 + 1 == i2;
       invariant sum1 == sum2; 
    { sum1 := sum1 + A1[i1]; 
      i1 := i1 + 1; 
      assert inst( - A2[i2] - sum2 + sum1 ); // alert prover about instantiation candidate
      assert (exists v:int :: { inst(v) } v == - A2[i2] - sum2 + sum1); // inserted by chk; with trigger 
      havoc y2; 
//      assume y2 == A1[i1] - A2[i2];  // elegant but fails to verify 
      assume y2 == - A2[i2] - sum2 + sum1;
      sum2 := sum2 + A2[i2] + y2; 
      i2 := i2 + 1; 
    } 
  } else { 
  if (b1 <= 0 && b2 > 0) { // unreachable 
    i1 := 1;
    while (i1 < n1)
    { havoc y1; sum1 := sum1 + A1[i1] + y1; i1 := i1 + 1; } 
    i2 := 0;
    while (i2 < n2 - 2)
    { sum2 := sum2 + A2[i2]; i2 := i2 + 1; }
  } else { // (b1 <= 0 && b2 < 0) 
    i1 := 1; i2 := 1;
    while (i1 < n1 && i2 < n2)
      invariant i1 < n1 <==> i2 < n2;
       invariant i1 == i2;
       invariant sum1 == sum2; 
    { havoc y1; 
      sum1 := sum1 + A1[i1] + y1; 
      i1 := i1 + 1;  
      assert inst( - A2[i2] - sum2 + sum1 ); 
      assert (exists v:int :: { inst(v) } v == - A2[i2] - sum2 + sum1); // inserted by chk
      havoc y2; 
      assume y2 == - A2[i2] - sum2 + sum1;
      sum2 := sum2 + A2[i2] + y2; 
      i2 := i2 + 1; 
} 
}}}}

