/* https://github.com/veracity-lang/veracity2g/blob/main/benchmarks/global_commutativity/simple-io.vcy */

/* File system model:
   file_system : int -> int -> int     (filename -> line_number -> content)
   cp_file(from, to, fs)               copies entire file: fs[to] := fs[from]
   write_at(fname, line, v, fs)        writes v at fs[fname][line]
   content(fs, f, l)                   reads fs[f][l]

   f1(fname_1, fname_2): cp(fname_1, fname_2) repeated 20 times
   f2(fname_3, fname_4): read line 0 of fname_3, write to line 0 of fname_4, repeated 10 times

   Commutativity condition:
     fname_2 <> fname_3  (f1's writes don't affect f2's reads)
     fname_1 <> fname_4  (f2's writes don't affect f1's reads)
     fname_2 <> fname_4  (f1 and f2 write to different files)
     fname_3 <> fname_4  (f2 reads and writes different files) */

interface SIMPLEIO =
  import theory Simple_IO_Theory
  extern type file_system with default = empty_fs
  extern const empty_fs : file_system
  extern content(file_system, int, int) : int
  extern cp_file(int, int, file_system) : file_system
  extern write_at(int, int, int, file_system) : file_system

  public fs : file_system

  meth simpleio (fname_1: int, fname_2: int, fname_3: int, fname_4: int) : unit
    requires { fname_2 <> fname_3 /\ fname_1 <> fname_4 /\ fname_2 <> fname_4 }
    requires { fname_3 <> fname_4 }
    ensures { let ofs = old(fs) in
              forall l:int. content(fs, fname_2, l) = content(ofs, fname_1, l) }
    ensures { let ofs = old(fs) in
              content(fs, fname_4, 0) = content(ofs, fname_3, 0) }
    ensures { let ofs = old(fs) in
              forall f:int, l:int. f <> fname_2 /\ f <> fname_4 ->
                content(fs, f, l) = content(ofs, f, l) }
    ensures { let ofs = old(fs) in
              forall l:int. l <> 0 ->
                content(fs, fname_4, l) = content(ofs, fname_4, l) }
    effects { rw fs; rd fname_1, fname_2, fname_3, fname_4 }
end

/* Left execution: f1 then f2 */
module M0 : SIMPLEIO =
  meth simpleio (fname_1: int, fname_2: int, fname_3: int, fname_4: int) : unit =
    var k: int in var z: int in var temp: int in var zero: int in
    zero := 0;
    /* f1: cp(fname_1, fname_2) repeated 20 times */
    k := 0;
    while (k < 20) do
      invariant { 0 <= k /\ k <= 20 }
      invariant { let ofs = old(fs) in
                  forall f:int, l:int. f <> fname_2 ->
                    content(fs, f, l) = content(ofs, f, l) }
      invariant { let ofs = old(fs) in
                  forall l:int. content(fs, fname_1, l) = content(ofs, fname_1, l) }
      invariant { let ofs = old(fs) in
                  k > 0 -> forall l:int.
                    content(fs, fname_2, l) = content(ofs, fname_1, l) }
      fs := cp_file(fname_1, fname_2, fs);
      k := k + 1;
    done;
    /* f2: read line 0 of fname_3, write to line 0 of fname_4, repeated 10 times */
    z := 0;
    while (z < 10) do
      invariant { 0 <= z /\ z <= 10 }
      invariant { let ofs = old(fs) in
                  forall f:int, l:int. f <> fname_2 /\ f <> fname_4 ->
                    content(fs, f, l) = content(ofs, f, l) }
      invariant { let ofs = old(fs) in
                  forall l:int. content(fs, fname_2, l) = content(ofs, fname_1, l) }
      invariant { let ofs = old(fs) in
                  z > 0 -> content(fs, fname_4, 0) = content(ofs, fname_3, 0) }
      invariant { let ofs = old(fs) in
                  forall l:int. l <> 0 ->
                    content(fs, fname_4, l) = content(ofs, fname_4, l) }
      temp := content(fs, fname_3, zero);
      fs := write_at(fname_4, zero, temp, fs);
      z := z + 1;
    done;
end

/* Right execution: f2 then f1 */
module M1 : SIMPLEIO =
  meth simpleio (fname_1: int, fname_2: int, fname_3: int, fname_4: int) : unit =
    var k: int in var z: int in var temp: int in var zero: int in
    zero := 0;
    /* f2: read line 0 of fname_3, write to line 0 of fname_4, repeated 10 times */
    z := 0;
    while (z < 10) do
      invariant { 0 <= z /\ z <= 10 }
      invariant { let ofs = old(fs) in
                  forall f:int, l:int. f <> fname_4 ->
                    content(fs, f, l) = content(ofs, f, l) }
      invariant { let ofs = old(fs) in
                  z > 0 -> content(fs, fname_4, 0) = content(ofs, fname_3, 0) }
      invariant { let ofs = old(fs) in
                  forall l:int. l <> 0 ->
                    content(fs, fname_4, l) = content(ofs, fname_4, l) }
      temp := content(fs, fname_3, zero);
      fs := write_at(fname_4, zero, temp, fs);
      z := z + 1;
    done;
    /* f1: cp(fname_1, fname_2) repeated 20 times */
    k := 0;
    while (k < 20) do
      invariant { 0 <= k /\ k <= 20 }
      invariant { let ofs = old(fs) in
                  forall f:int, l:int. f <> fname_2 /\ f <> fname_4 ->
                    content(fs, f, l) = content(ofs, f, l) }
      invariant { let ofs = old(fs) in
                  forall l:int. content(fs, fname_1, l) = content(ofs, fname_1, l) }
      invariant { let ofs = old(fs) in
                  k > 0 -> forall l:int.
                    content(fs, fname_2, l) = content(ofs, fname_1, l) }
      invariant { let ofs = old(fs) in
                  content(fs, fname_4, 0) = content(ofs, fname_3, 0) }
      invariant { let ofs = old(fs) in
                  forall l:int. l <> 0 ->
                    content(fs, fname_4, l) = content(ofs, fname_4, l) }
      fs := cp_file(fname_1, fname_2, fs);
      k := k + 1;
    done;
end

bimodule COMMUTE (M0 | M1) =

  meth simpleio (fname_1:int, fname_2:int, fname_3:int, fname_4:int
                | fname_1:int, fname_2:int, fname_3:int, fname_4:int) : (unit | unit)
    requires { Agree fs }
    requires { fname_1 =:= fname_1 /\ fname_2 =:= fname_2 }
    requires { fname_3 =:= fname_3 /\ fname_4 =:= fname_4 }
    requires { Both (fname_2 <> fname_3 /\ fname_1 <> fname_4 /\ fname_2 <> fname_4) }
    requires { Both (fname_3 <> fname_4) }
    ensures  { forall f:int, l:int | f:int, l:int. (f =:= f) -> (l =:= l) ->
                 content(fs, f, l) =:= content(fs, f, l) }
    effects  { rw fs | rw fs }
  = Var k: int | k: int in
    Var z: int | z: int in
    Var temp: int | temp: int in
    Var zero: int | zero: int in
    |_ zero := 0 _|;
    ( /* Left: f1 then f2 */
      k := 0;
      while (k < 20) do
        invariant { 0 <= k /\ k <= 20 }
        invariant { let ofs = old(fs) in
                    forall f:int, l:int. f <> fname_2 ->
                      content(fs, f, l) = content(ofs, f, l) }
        invariant { let ofs = old(fs) in
                    forall l:int. content(fs, fname_1, l) = content(ofs, fname_1, l) }
        invariant { let ofs = old(fs) in
                    k > 0 -> forall l:int.
                      content(fs, fname_2, l) = content(ofs, fname_1, l) }
        fs := cp_file(fname_1, fname_2, fs);
        k := k + 1;
      done;
      z := 0;
      while (z < 10) do
        invariant { 0 <= z /\ z <= 10 }
        invariant { let ofs = old(fs) in
                    forall f:int, l:int. f <> fname_2 /\ f <> fname_4 ->
                      content(fs, f, l) = content(ofs, f, l) }
        invariant { let ofs = old(fs) in
                    forall l:int. content(fs, fname_2, l) = content(ofs, fname_1, l) }
        invariant { let ofs = old(fs) in
                    z > 0 -> content(fs, fname_4, 0) = content(ofs, fname_3, 0) }
        invariant { let ofs = old(fs) in
                    forall l:int. l <> 0 ->
                      content(fs, fname_4, l) = content(ofs, fname_4, l) }
        temp := content(fs, fname_3, zero);
        fs := write_at(fname_4, zero, temp, fs);
        z := z + 1;
      done
    | /* Right: f2 then f1 */
      z := 0;
      while (z < 10) do variant {10 - z }
        invariant { 0 <= z /\ z <= 10 }
        invariant { let ofs = old(fs) in
                    forall f:int, l:int. f <> fname_4 ->
                      content(fs, f, l) = content(ofs, f, l) }
        invariant { let ofs = old(fs) in
                    z > 0 -> content(fs, fname_4, 0) = content(ofs, fname_3, 0) }
        invariant { let ofs = old(fs) in
                    forall l:int. l <> 0 ->
                      content(fs, fname_4, l) = content(ofs, fname_4, l) }
        temp := content(fs, fname_3, zero);
        fs := write_at(fname_4, zero, temp, fs);
        z := z + 1;
      done;
      k := 0;
      while (k < 20) do variant { 20 -  k }
        invariant { 0 <= k /\ k <= 20 }
        invariant { let ofs = old(fs) in
                    forall f:int, l:int. f <> fname_2 /\ f <> fname_4 ->
                      content(fs, f, l) = content(ofs, f, l) }
        invariant { let ofs = old(fs) in
                    forall l:int. content(fs, fname_1, l) = content(ofs, fname_1, l) }
        invariant { let ofs = old(fs) in
                    k > 0 -> forall l:int.
                      content(fs, fname_2, l) = content(ofs, fname_1, l) }
        invariant { let ofs = old(fs) in
                    content(fs, fname_4, 0) = content(ofs, fname_3, 0) }
        invariant { let ofs = old(fs) in
                    forall l:int. l <> 0 ->
                      content(fs, fname_4, l) = content(ofs, fname_4, l) }
        fs := cp_file(fname_1, fname_2, fs);
        k := k + 1;
      done
    );

    Assert { Both (let ofs = old(fs) in
              forall f:int, l:int. f <> fname_2 /\ f <> fname_4 ->
                content(fs, f, l) = content(ofs, f, l)) };
    Assert { Both (let ofs = old(fs) in
              forall l:int. content(fs, fname_2, l) = content(ofs, fname_1, l)) };
    Assert { Both (let ofs = old(fs) in
              content(fs, fname_4, 0) = content(ofs, fname_3, 0)) };
    Assert { Both (let ofs = old(fs) in
              forall l:int. l <> 0 ->
                content(fs, fname_4, l) = content(ofs, fname_4, l)) };
end


bimodule COMMUTE_Lockstep (M0 | M1) =

  meth simpleio (fname_1:int, fname_2:int, fname_3:int, fname_4:int
                | fname_1:int, fname_2:int, fname_3:int, fname_4:int) : (unit | unit)
    requires { Agree fs }
    requires { fname_1 =:= fname_1 /\ fname_2 =:= fname_2 }
    requires { fname_3 =:= fname_3 /\ fname_4 =:= fname_4 }
    requires { Both (fname_2 <> fname_3 /\ fname_1 <> fname_4 /\ fname_2 <> fname_4) }
    /* requires { Both (fname_3 <> fname_4) } */
    ensures  { forall f:int, l:int | f:int, l:int. (f =:= f) -> (l =:= l) ->
                 content(fs, f, l) =:= content(fs, f, l) }
    effects  { rw fs | rw fs }
  = Var k: int | k: int in
    Var z: int | z: int in
    Var temp: int | temp: int in
    Var zero: int | zero: int in
    |_ zero := 0 _|;
    ( /* Left: f1 then f2 */
      k := 0;
      while (k < 20) do
        invariant { 0 <= k /\ k <= 20 }
        invariant { let ofs = old(fs) in
                    forall f:int, l:int. f <> fname_2 ->
                      content(fs, f, l) = content(ofs, f, l) }
        invariant { let ofs = old(fs) in
                    forall l:int. content(fs, fname_1, l) = content(ofs, fname_1, l) }
        invariant { let ofs = old(fs) in
                    k > 0 -> forall l:int.
                      content(fs, fname_2, l) = content(ofs, fname_1, l) }
        fs := cp_file(fname_1, fname_2, fs);
        k := k + 1;
      done | skip);
      |_ z := 0 _|;
      While (z < 10) | (z < 10) . <| false <] | [> false |> do variant { [> 10 - z >]}
        invariant { Agree z }
        invariant { <| let ofs = old(fs) in
                    forall l:int. content(fs, fname_1, l) = content(ofs, fname_1, l) <] }
        invariant { Both (let ofs = old(fs) in
                    forall l:int. content(fs, fname_1, l) = content(ofs, fname_1, l)) }
        invariant { <| let ofs = old(fs) in
                      forall l:int.
                      content(fs, fname_2, l) = content(ofs, fname_1, l) <] }
        invariant { forall f:int, l:int | f:int, l:int. (f =:= f) -> (l =:= l) -> Both (f <> fname_2) ->
                 content(fs, f, l) =:= content(fs, f, l) }
        |_ temp := content(fs, fname_3, zero) _|;
        |_ fs := write_at(fname_4, zero, temp, fs) _|;
        |_ z := z + 1 _|;
      done;
    (skip | k := 0);
    WhileR (k < 20) do  variant { [> 20 - k >] }
        invariant { [> 0 <= k /\ k <= 20 |> }
        invariant { forall f:int, l:int | f:int, l:int. (f =:= f) -> (l =:= l) -> Both (f <> fname_2) ->
                 content(fs, f, l) =:= content(fs, f, l) }
        invariant { Both (let ofs = old(fs) in
                    forall l:int. content(fs, fname_1, l) = content(ofs, fname_1, l)) }
        invariant { <| let ofs = old(fs) in
                      forall l:int.
                      content(fs, fname_2, l) = content(ofs, fname_1, l) <] }
        invariant {[> let ofs = old(fs) in
                    k > 0 -> forall l:int.
                      content(fs, fname_2, l) = content(ofs, fname_1, l) |> }
        (skip | fs := cp_file(fname_1, fname_2, fs));
        (skip | k := k + 1);
      done;
end
