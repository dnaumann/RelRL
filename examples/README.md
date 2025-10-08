## Examples

This directory contains examples used to evaluate WhyRel.  Why3 session files
are included.  To replay an example, it should be sufficient to `cd' to its
directory and run:

```
make
make ide
```

Please consult the `Makefile` in each directory to learn about any additional
options.  Replaying the examples may require the following SMT solvers to be
installed on your system: Alt-Ergo, Z3, CVC3, and CVC4.

Included examples are:

- **Cell**: Equivalence of two modules implementing boxed integers in
  different ways.
- **SSSP**: Establishes equivalence of two priority queue modules with similar
  internals.  Client program is Dijkstra's single source shortest paths
  algorithm.
- **Kruskal**: Equivalence of two union-find implementations; one based on
  QuickFind and another based on QuickUnion.  Client program is Kruskal's
  algorithm for computing the minimum spanning tree of a graph.
- **sumpub**: Information flow case study.  Verifies that a program summing up
  public elements in a list with public and non-public elements does not leak
  information about non-public values.
- **tabulate**: Introductory example that shows how specs in region logic can be
  formulated.  Shows relational reasoning without encapsulation.
- **determinism**: Example from [*Modular Product
  Programs*](https://dl.acm.org/doi/10.1145/3324783), Eilers et al.
- **equiv-check**: Example from [*Semantic Program Alignment for Equivalence
    Checking*](https://dl.acm.org/doi/10.1145/3314221.3314596), Churchill et
    al.
- **majorization**: Example from [*Thirty-seven years of relational Hoare
    logic*](https://arxiv.org/abs/2007.06421), D. A. Naumann.
- **factorial**: Introductory example illustrating biprograms.  Equivalence of
  two methods that compute factorial.
- **swap**: Minimal example of program equivalence: commuting two calls to two
  methods acting on different parts of the heap.
- **tiling**: Loop tiling compiler optimization example.  Taken from
    [*Relational Logic with Framing and Hypotheses: Technical
    Report*](https://arxiv.org/abs/1611.08992), Banerjee et al.

- **all_exists**: contains forall exists examples.