// File: examples/all_exists/Stack/test_stack.bpl

type Stack;
type Element;

const unique null: Element;

var stack: [Stack] seq<Element>;

procedure Init(s: Stack)
    modifies stack;
    ensures stack[s] == [];

procedure Push(s: Stack, e: Element)
    requires e != null;
    modifies stack;
    ensures stack[s] == [e] + old(stack[s]);

procedure Pop(s: Stack) returns (popped: Element)
    requires |stack[s]| > 0;
    modifies stack;
    ensures popped == old(stack[s])[0];
    ensures stack[s] == old(stack[s])[1..];

procedure Top(s: Stack) returns (top: Element)
    requires |stack[s]| > 0;
    ensures top == stack[s][0];

procedure IsEmpty(s: Stack) returns (b: bool)
    ensures b <==> |stack[s]| == 0;


procedure {:test} TestInit()
{
    var s: Stack;
    call Init(s);
    assert stack[s] == [];
}

procedure {:test} TestPush()
{
    var s: Stack;
    var e: Element;
    assume e != null;
    call Init(s);
    call Push(s, e);
    assert stack[s] == [e];
}

procedure {:test} TestPop()
{
    var s: Stack;
    var e: Element;
    var popped: Element;
    assume e != null;
    call Init(s);
    call Push(s, e);
    call Pop(s) returns (popped);
    assert popped == e;
    assert stack[s] == [];
}

procedure {:test} TestTop()
{
    var s: Stack;
    var e: Element;
    var top: Element;
    assume e != null;
    call Init(s);
    call Push(s, e);
    call Top(s) returns (top);
    assert top == e;
    assert stack[s] == [e];
}

procedure {:test} TestIsEmpty()
{
    var s: Stack;
    var b: bool;
    call Init(s);
    call IsEmpty(s) returns (b);
    assert b;

    var e: Element;
    assume e != null;
    call Push(s, e);
    call IsEmpty(s) returns (b);
    assert !b;
}