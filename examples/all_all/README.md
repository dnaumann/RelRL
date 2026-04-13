# All All Examples


- **Cell**: Equivalence of two modules implementing boxed integers in
  different ways.
- **SSSP**: Establishes equivalence of two priority queue modules with similar
  internals.  Client program is Dijkstra's single source shortest paths
  algorithm. Yet to be verified for current WhyRel.
- **Kruskal**: Equivalence of two union-find implementations; one based on
  QuickFind and another based on QuickUnion.  Client program is Kruskal's
  algorithm for computing the minimum spanning tree of a graph. Yet to be
  verified for current WhyRel

- **stack**: Equivalence to two stack implementations. Yet to be verified for
  current WhyRel
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
- **Veracity**: Contains challenge problems that were not verifiable
  using veracity framework. They deal with commutativity checking. See
  https://github.com/veracity-lang/veracity/
