/* // https://github.com/veracity-lang/veracity2g/blob/main/benchmarks/global_commutativity/simple-vector.vcy  */

interface A =
  class IntArray { length: int; slots: int array; }

  public x : IntArray
  public y : IntArray
  public z : IntArray

  meth main () : unit
    requires { x <> null /\ y <> null /\ z <> null }
    requires { x.length = 1000 /\ y.length = 1000 /\ z.length = 1000 }
    requires { x <> y /\ y <> z /\ x <> z}
    requires {x[999] = 1}
    ensures { forall i:int. 0 <= i /\ i < 1000 ->
                let xi = x[i] in y[i] = xi * xi }
    ensures { forall k:int. 0 <= k /\ k < 1000 ->
                let v = x[999 - k] in z[k] = v }
    effects { rd x, {x}`any, y, z; wr {y}`slots, {z}`slots }
end

/* f1; f2 */
module AB : A =
  class IntArray { length: int; slots: int array; }

  meth main () : unit =
    var i: int in var k: int in var tmp: int in
    
    /* f1 */
    i := 0;
    while (i < 1000) do
      invariant { 0 <= i /\ i <= 1000 }
      invariant { forall m:int. 0 <= m /\ m < i ->
                    let xm = x[m] in y[m] = xm * xm }
        
      effects { wr {y}`slots }
      
      tmp := x[i];
      y[i] := tmp * tmp;
      i := i + 1;
    
    done;
    
    /* f2 */
    
    k := 0;
    while (k < 1000) do
      invariant { 0 <= k /\ k <= 1000 }
      invariant { forall m:int. 0 <= m /\ m < k ->
                    let v = x[999 - m] in z[m] = v }
      invariant { forall m:int. 0 <= m /\ m < 1000 ->
                    let xm = x[m] in y[m] = xm * xm }
      effects { wr {z}`slots, {y}`slots  }
      
      tmp := x[999 - k];
      z[k] := tmp;
      k := k + 1;
    
    done;
end

/* f2; f1 */
module BA : A =
  class IntArray { length: int; slots: int array; }

  meth main () : unit =
    var i: int in var k: int in var tmp: int in
    
    /* f2 */
    k := 0;
    while (k < 1000) do
      invariant { 0 <= k /\ k <= 1000 }
      invariant { forall m:int. 0 <= m /\ m < k ->
                    let v = x[999 - m] in z[m] = v }
      effects { wr {z}`slots }
      
      tmp := x[999 - k];
      z[k] := tmp;
      k := k + 1;
    
    done;
    
    /* f1 */
    i := 0;
    while (i < 1000) do
      invariant { 0 <= i /\ i <= 1000 }
      invariant { forall m:int. 0 <= m /\ m < i ->
                    let xm = x[m] in y[m] = xm * xm }
      invariant { forall m:int. 0 <= m /\ m < 1000 ->
                    let v = x[999 - m] in z[m] = v }
      effects { wr {z}`slots, {y}`slots  }
      
      tmp := x[i];
      y[i] := tmp * tmp;
      i := i + 1;
    
    done;
end

/* Verify f1;f2 = f2;f1
   Both start from the same x and produce the same y, z. */
bimodule COMMUTE (AB | BA) =

  meth main (|) : (unit | unit)
    requires { Both (x <> null /\ y <> null /\ z <> null) }
    requires { Both (x <> y /\ y <> z /\ z <> x) }
    requires { Both (x.length = 1000 /\ y.length = 1000 /\ z.length = 1000) }
    requires { Both (x[999] = 1) }
    requires { Agree x /\ Agree y /\ Agree z }
    requires { Agree {x}`any }
    ensures  { (forall i:int|i:int. Both (0 <= i /\ i < 1000) -> (Agree i) -> let yi|yi = y[i]|y[i] in yi =:= yi) }
    ensures  { (forall i:int|i:int. Both (0 <= i /\ i < 1000) -> (Agree i) -> let zi|zi = z[i]|z[i] in zi =:= zi) }
    effects  { rd x, {x}`any, y, z; wr {y}`slots, {z}`slots
             | rd x, {x}`any, y, z; wr {y}`slots, {z}`slots }
  = Var i: int | i: int in
    Var k: int | k: int in
    Var tmp: int | tmp: int in
   
    /* f1 | skip */
      (
      i := 0;
      while (i < 1000) do
        invariant { 0 <= i /\ i <= 1000 }
        invariant { forall m:int. 0 <= m /\ m < i ->
                      let xm = x[m] in y[m] = xm * xm }
        effects { wr {y}`slots }
     
          tmp := x[i];
          y[i] := tmp * tmp;
          i := i + 1;
      done | skip);

    /* f2 | f2 */
      |_ k := 0 _|;
       While (k < 1000) | (k < 1000) .  <| false <] | [> false |> do
        invariant { Both ( 0 <= k /\ k <= 1000 ) }
        invariant {  k =:= k }
        invariant { Agree {x}`any }
        invariant { Both (forall m:int. 0 <= m /\ m < k ->
                      let v = x[999 - m] in z[m] = v) }
        invariant { (forall i:int|i:int. Both (0 <= i /\ i < k) -> (Agree i) ->  let zi|zi = z[i]|z[i] in zi =:= zi) }
        invariant { <| forall m:int. 0 <= m /\ m < 1000 ->
                      let xm = x[m] in y[m] = xm * xm <]}
        effects { wr {z}`slots, {y}`slots | wr {z}`slots }
        
        |_ tmp := x[999 - k] _|;
        |_ z[k] := tmp _|;
        |_ k := k + 1 _|;
      done;
      Assert { <| forall i:int. 0 <= i /\ i < 1000 ->
                    let xi = x[i] in y[i] = xi * xi <] };
      Assert { <| forall k:int. 0 <= k /\ k < 1000 ->
                    let v = x[999 - k] in z[k] = v <] };

    /* skip | f1 */
    (skip | i := 0);
    WhileR (i < 1000) do
      invariant { [> 0 <= i /\ i <= 1000 |> }
      invariant { [> forall m:int. 0 <= m /\ m < i ->
                      let xm = x[m] in y[m] = xm * xm |> }
        invariant { (forall k:int|k:int. Both (0 <= k /\ k < 1000) -> (Agree k) -> let zk|zk = z[k]|z[k] in zk =:= zk) }
        invariant { (forall k:int|k:int. Both (0 <= k /\ k < i) -> (Agree k) -> let yk|yk = y[k]|y[k] in yk =:= yk) } 
      invariant { <| forall m:int. 0 <= m /\ m < 1000 ->
                      let xm = x[m] in y[m] = xm * xm <] }
      invariant { Agree {x}`any }
      effects { wr {y}`slots, {z}`slots | wr {y}`slots, {z}`slots }

      (skip |
        tmp := x[i];
        y[i] := tmp * tmp;
        i := i + 1);
    done;
end
