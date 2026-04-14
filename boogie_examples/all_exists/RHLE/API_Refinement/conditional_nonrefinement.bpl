// An invalid refinement involving a simple conditional.
/* https://github.com/rcdickerson/rhle-benchmarks/blob/main/api-refinement/conditional-nonrefinement.imp

*/

function inst <a>(arg: a) returns (bool) {true}

// should not and deos not verify
procedure biprog () returns (o_ref: int, o_orig: int)
  requires true;
  ensures o_ref == o_orig;
{
  var choice_var : int;
  var flipret_ref : int;
  var flipret_orig : int;

  havoc flipret_ref;
  assume flipret_ref == 0 || flipret_ref == 1; // universal spec
  
  if (flipret_ref == 0) 
  {  o_ref := 10;}
  else
  {  o_ref := 30;}

  // existential spec instantiated with flipret_ref
  choice_var := flipret_ref;
  assert (exists v: int ::  (v == choice_var));
  havoc flipret_orig;
  assume (choice_var == flipret_orig); 

  if (flipret_orig == 0)
  { 
      o_orig := 10;
  }
  else
  {  
     o_orig := 20;
  }
}