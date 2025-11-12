# WhyRel

WhyRel is a tool for reasoning about relational properties of object-based
programs.  It has been used to verify equivalence of ADTs, simple
noninterference examples and program transformations.  WhyRel is built on top
of the [Why3](http://why3.lri.fr) platform for deductive program verification
and relies on it to generate and discharge verification conditions (VCs).

Source files are written in a syntax similar to ML/WhyML but the language
contains features most familiar in Java-like contexts; e.g., mutable locals,
implicit dereferencing, and the presence of a null reference.  WhyRel
translates source programs to WhyML programs that explicitly act on a model of
the heap.  The program logic WhyRel implements is based on relational region
logic and VCs pertinent to this logic are encoded in pre- and post-conditions
and as additional lemmas for the user to establish.  Note that WhyRel also
provides a full implementation of unary region logic and can be used to verify
programs in this setting.  See the `examples/` directory for some case studies
done using WhyRel.

This repository contains the sources for a new version of WhyRel.  The previous
version was used to evaluate a rich set of case studies but is no longer
maintained.  The current version is a reimplementation intended to be used for
experimenting with encodings and additional features.

This research has been partially supported by grants NSF CNS 1718713 and ONR
N00014-17-1-2787


## State of this repository

The `encoding` branch contains in progress work on all-exists verification. The
tag `stable` points to a stable release of WhyRel that works with Why3 version
1.7.0.


## Documentation

The relational program logic and a high level description of the current version
of WhyRel can be found [here](http://arxiv.org/abs/1910.14560).


## Installation

The dependencies for WhyRel are:

- Why3 1.7.0
- OCamlbuild 0.14.0

Please refer to Why3's [installation
instructions](http://why3.lri.fr/doc/install.html#installing-why3). If you
install Why3 from source, make sure to also install the OCaml API.
OCamlbuild is required to build WhyRel.  The sources are expected to
compile using OCaml 4.09.1 and above.

The recommended way of installing dependencies is by using an
[opam](https://opam.ocaml.org) switch.

```
opam switch create whyrel 4.09.1
opam install why3.1.3.3 ocamlbuild
```

You may also consider installing the `why-ide` package.


### Compilation

To compile, `cd` to the directory where you cloned this repository (referred
to as `<WHYREL>` from here on) and run `make`.  To test out your installation
you can run `<WHYREL>/bin/whyrel -version`.  There is no `make install`
option; simply add `<WHYREL>/bin` to your `PATH` variable if desired.  Run
`whyrel -help` to learn about supported command line flags.


### External provers

Why3 supports a wide range of automated and interactive provers.  In developing
and testing examples for WhyRel, the emphasis has been on using SMT solvers to
discharge VCs.  These include Alt-Ergo, Z3, CVC3, and CVC4.  Please refer to the
Why3 installation documentation for instructions on how to install these and
other supported provers.


## Usage

At its present state, WhyRel can be used to translate a series of source files
to WhyML modules.  The experimental `-locEq` option can be used to derive the
local equivalence spec for a given method.

To compile a file called `foo.rl` run

```
whyrel foo.rl -o foo.mlw
```

The resulting `foo.mlw` will include WhyML modules for each interface, module,
and bimodule in `foo.rl`, along with an additional module that encodes program
states.  For (relational) reasoning with encapsulation and hidden invariants,
WhyRel also generates a module with lemmas encoding proof obligations of the
(relational) modular linking rule.

To compile multiple files, simply list them (the order does not matter)

```
whyrel foo1.rl foo2.rl foo3.rl -o foo.mlw
```

Note that only one mlw file will be produced. To verify, using Why3's IDE for
instance, run

```
why3 ide -L <WHYREL>/stdlib foo.mlw
```

It is important to include WhyRel's standard library by using the `-L` option.


### Minor issues

WhyRel relies on Why3's pretty printer.  As of Why3 1.3.3 there is an issue with
how lemmas and axioms are printed.  What should be `lemma bar : P` is instead
printed as `lemma bar = P`.  To fix, simply replace the `=` with `:`.  The sed
file `post-process.sed` in the `util` directory can be used to apply this change
uniformly.

```
sed -f <WHYREL>/util/post-process.sed -i .bak path/to/mlw/file
```


## Examples

See the `examples` directory for a few case studies.  Each example is placed
in a directory that includes source files, WhyML files, and Why3 session
files.  To replay an example using Why3's IDE, it should be sufficient to run
`make && make ide` in the example's directory.
