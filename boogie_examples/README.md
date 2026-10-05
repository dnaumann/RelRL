## boogie_examples

This directory contains examples for the boogie tool which 
can be found here: https://github.com/boogie-org/boogie

They are forall-forall examples corresponding to some WhyRel examples
that are in ../examples/all_all,
and forall-exists examples corresponding to many in ../examples/all_exists.
 
The file ./all_exists/catalog.md lists the original sources (RHLE, ForEx, etc).
It also mention examples in the original sources which are not included here
because the property is not forall-exists.

To run the examples simply invoke `boogie filename.bpl`.
They were tested using boogie version 3.5.8 but likely run
on other versions.  Boogie requires the Z3 SMT solver.

The python files and burden_bpl.md are WIP about annotation statistics
and should probably be deleted.  





