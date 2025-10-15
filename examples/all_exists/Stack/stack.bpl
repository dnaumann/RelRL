
type Stack;
type Element;

const unique null: Element;

var stack: [Stack] seq<Element>;

procedure Init(s: Stack)
    modifies stack;
    ensures stack[s] == [];
{
    stack[s] := [];
}

procedure Push(s: Stack, e: Element)
    modifies stack;
    requires e != null;
    ensures stack[s] == old(stack[s]) + [e];
{
    stack[s] := stack[s] + [e];
}

procedure Pop(s: Stack) returns (e: Element)
    modifies stack;
    requires stack[s] != [];
    ensures stack[s] == old(stack[s])[0..|old(stack[s])|-1];
    ensures e == old(stack[s])[|old(stack[s])|-1];
{
    e := stack[s][|stack[s]|-1];
    stack[s] := stack[s][0..|stack[s]|-1];
}

procedure Top(s: Stack) returns (e: Element)
    requires stack[s] != [];
    ensures e == stack[s][|stack[s]|-1];
{
    e := stack[s][|stack[s]|-1];
}

procedure IsEmpty(s: Stack) returns (b: bool)
    ensures b <==> stack[s] == [];
{
    b := (stack[s] == []);
}

procedure example()
{
    var s1, s2: Stack;
    var b1, b2: bool;
    var e1, e2: Element;

    havoc b1;

    while (b1) {
        
        assume e != null;
        call Init(s1);
        call Init(s2);
        call Push(s1, e);
        call Push(s2, e);
        var top1: Element;
        var top2: Element;
        call Top(s1) returns (top1);
        call Top(s2) returns (top2);
        assert top1 == top2;
        var popped1: Element;
        var popped2: Element;
        call Pop(s1) returns (popped1);
        call Pop(s2) returns (popped2);
        assert popped1 == popped2;
        var empty1: bool;
        var empty2: bool;
        call IsEmpty(s1) returns (empty1);
        call IsEmpty(s2) returns (empty2);
        assert empty1 == empty2;
    }

    // get content of s1
    var content1: seq<Element>;
    content1 := stack[s1];

    havoc b2;
    while (b2) {

}