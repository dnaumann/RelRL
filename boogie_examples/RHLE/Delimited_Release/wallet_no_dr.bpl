/*

// From:
//   Sabelfeld, Andrei & Myers, Andrew. (2004).
//   A Model for Delimited Information Release.
//   Lecture Notes in Computer Science. 10.1007/978-3-540-37621-7_9.

expected: invalid;

forall: buy[1];
exists: buy[2];

// High:
//   funds
// Low:
//   spent
//   cost

pre: (and
       (= buy!1!spent buy!2!spent)
       (= buy!1!cost buy!2!cost));

post: (= buy!1!spent buy!2!spent);


fun buy(funds, spent, cost) {
  if (funds >= cost) then
    funds := funds - cost;
    spent := spent + cost;
  else
    skip;
  endif
  return 0;
}

*/

var funds1, spent1, cost1, funds2, spent2, cost2 : int;

procedure skip () returns ();

// should not and does not verify.
procedure biprog () returns ()
  requires spent1 == spent2 && cost1 == cost2;
  modifies funds1, spent1, cost1, funds2, spent2, cost2; 
  ensures spent1 == spent2;
{
    if (funds1 >= cost1)
    {
      funds1 := funds1 - cost1;
      spent1 := spent1 + cost1;
    }
    else
    {
      call skip();
    }

    if (funds2 >= cost2)
    {
      funds2 := funds2 - cost2;
      spent2 := spent2 + cost2;
    }
    else
    {
      call skip();
    }
}