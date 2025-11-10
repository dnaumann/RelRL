interface LIST =

  import theory Sumpub_theory

  extern type intList with default = nil
  extern hd (intList) : int
  extern tl (intList) : intList
  extern cons (int,intList) : intList
  extern sumList (intList) : int
  extern listLength (intList) : int

  class Node { value : int; pub : bool; nxt : Node; }

  class List { head : Node; rep : rgn; }


  

  predicate rep_closed (xs:List) =
    xs <> null ->
    let hd = xs.head in
    let rep = xs.rep in
    Type(rep,Node) /\ rep`nxt subset rep /\ null in rep /\ hd in rep

  lemma rep_closed_prop : forall xs:List.
    rep_closed(xs) ->
    let rep = xs.rep in
    forall n:Node in rep.
      let nxt = n.nxt in
      nxt in rep

  inductive listpub (n: Node, l: intList) =
    | listpub_nil : listpub(null,nil)
    | listpub_del : forall n: Node, l: intList.
      n.pub = false -> let nxt = n.nxt in listpub(nxt,l) -> listpub(n,l)
    | listpub_pub : forall n: Node, l: intList.
      n.pub = true  -> let nxt = n.nxt in listpub(nxt,l) -> let v = n.value in listpub(n,cons(v,l))

   predicate listpubL (xs:List, ls:intList) =
    xs <> null ->
    let hd = xs.head in
    listpub(hd, ls)

  lemma listpub_nxt : forall n:Node,xs:intList.
    listpub(n,xs) ->
    let nxt = n.nxt in
    exists xs':intList. listpub(nxt,xs')

  lemma listpub_unique : forall xs:intList,n:Node.
    listpub(n,xs) -> forall ys:intList. listpub (n,ys) -> xs = ys

  lemma listpub_nexists : forall n:Node.
    n.nxt = n ->
    ~ (exists ls:intList. listpub(n,ls))

  meth sum (self:List) : int
    requires { exists ls:intList. listpubL(self,ls) }
    requires { rep_closed (self) }
    reads { self, {self}`any, {self}`rep`any, result }
    writes { result }

end


module List : LIST =

  class Node { value : int; pub : bool; nxt : Node; }

  class List { head : Node; rep : rgn; }

  meth sum (self:List) : int
  = var ghost xs : intList in
    assume { listpubL(self,xs) };
    var p : Node in
    p := self.head;
    result := 0;
    while (p <> null) do
      invariant { listpub(p,xs) }
      invariant { let rep = self.rep in p in rep }
      invariant { rep_closed (self) }
      var pub : bool in
      pub := p.pub;
      if pub then
        var v:int in
        v := p.value;
        result := result + v;
        xs := tl(xs);
      end;
      p := p.nxt;
    done;

end

bimodule BiList (List | List) =

  import theory Sumpub_theory

  meth sum (self:List | self:List) : (int | int)
    requires { exists ls:intList | ls:intList.
                 Both (listpubL(self,ls)) /\ ls =:= ls }
    ensures  { result =:= result }
    effects  { rd {self}`any, {self}`rep`any
             | rd {self}`any, {self}`rep`any }
  = Var ghost xs : intList | ghost xs : intList in
    Assume { Both (listpubL(self,xs)) };
    Var p : Node | p : Node in
    |_ p := self.head _|;
    |_ result := 0 _|;
    While (p <> null) | (p <> null) . <| p.pub = false <] | [> p.pub = false |> do
      invariant { Both (listpub(p,xs)) }
      invariant { result =:= result }
      invariant { xs =:= xs }
      variant {[> listLength(xs) >]}

      Var pub : bool | pub : bool in
      |_ pub := p.pub _|;

      ( if pub then
          var v : int in
          v := p.value; { v = hd(xs) };
          result := result + v;
          xs := tl(xs);
        end;
        p := p.nxt

      | if pub then
          var v : int in
          v := p.value; { v = hd(xs) };
          result := result + v;
          xs := tl(xs);
        end;
        p := p.nxt );
    done;

  /* Another version that uses different alignment guards */
  meth sum2 (self:List | self:List) : (int | int)
    requires { exists ls:intList | ls:intList.
                 Both (listpubL(self,ls)) /\ ls =:= ls }
    ensures  { result =:= result }
    effects  { rd alloc, {self}`any, {self}`rep`any
             | rd alloc, {self}`any, {self}`rep`any }
  = Var ghost xs : intList | ghost xs : intList in
    Assume { Both (listpubL(self,xs)) };
    Var p : Node | p : Node in
    |_ p := self.head _|;
    |_ result := 0 _|;
    While (p <> null) | (p <> null) .
        <| p.pub = false <] /\ [> p <> null -> p.pub = true |>
      | [> p.pub = false |> /\ <| p <> null -> p.pub = true <] do
      invariant { Both (listpub(p,xs)) }
      invariant { result =:= result }
      invariant { xs =:= xs }
      variant {[> listLength(xs) >]}

      Var pub : bool | pub : bool in
      |_ pub := p.pub _|;

      ( if pub then
          var v : int in
          v := p.value; { v = hd(xs) };
          result := result + v;
          xs := tl (xs);
        end;
        p := p.nxt

      | if pub then
          var v : int in
          v := p.value; { v = hd(xs) };
          result := result + v;
          xs := tl (xs);
        end;
        p := p.nxt );
    done;

end
