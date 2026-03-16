type ref;
const unique null : ref;

type field a; // field int, field bool, etc...

type heap = <a>[ref, field a] a; // polymorphic maps

var $heap : heap;

function update <a>(h: heap, f: field a, x: ref, v: a) : heap
{
  h[x, f := v]
}

function read <a>(h: heap, x: ref, f: field a) : a
{
  h[x, f]
}

// class Cell { public value : int }

const unique alloc : field bool;
const unique value : field int;


procedure testing () returns ()
  modifies $heap;
{
  var x: ref;
  var arr: [int] int; // int array
  var n: int;

  assume (forall i: int :: 0 <= i && i < n ==> arr[i] == 0);

  arr[0] := 1;

  // assume x is a cell
  assume $heap[x, alloc];
  assume $heap[x, value] == 1; // x.value == 1

  // x.value := 2
  $heap := $heap[x, value := 2];

  assert $heap[x, value] == old($heap)[x, value] + 1;
}

