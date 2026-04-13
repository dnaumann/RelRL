## Examples

This directory contains examples used to evaluate WhyRel.  Each example is
placed in a directory that includes source files, WhyML files, and Why3 session
files.  Current proofs were done with alt-ergo 2.6.2. You can install it using
the following command:

`opam install alt-ergo.2.6.2`

Run `why3 config detect` to make why3 aware of the prover.

Each example comes with a makefile with the following options

- `make`: builds whyml file
- `make ide`: launches why3 ide with current session if it exists else a new one.
- `make replay`: launches why3 replay for the currently saved session.

There is a master makefile present in the directory which allows replay
on all the examples and outputs a summary. 

- `make replay`: Runs make replay for all examples rooted from this directory.
- `make replay DIR=path`: Runs make replay for all examples in the listed path.
- `make summary`: Outputs a summary of all the replays resulting from make replay.

The all_all directory has examples on all all property verification. And
similarly for all_exists directory.