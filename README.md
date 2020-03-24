Plotkin's program reduction algorithm
=====================================

Gordon Plotkin gives the following algorithm for reduction of a set of
(arbitrary) clauses:

```
Given a set of clauses H, find a reduction H' of H:
1) Set H' to H
2) Stop if every clause in H' is marked
3) Choose an unmarked clause, C, in H'
4) If H' \{C} =< {C}, change H' to H' \ {C}
   Otherwise, mark C
5) Repeat from (2)
```

The algorithm is described in Plotkin's doctoral thesis, "Automatic
methods of inductive inference" (thesis, The University of Edinburgh,
1972). It is listed as theorem 3.3.1.2 (on page 76 of the thesis).

This module implements Plotkin's algorithm restricted to Horn clauses.

See `program_reduction/3` and `subsumes/2` for implementation details.

Running tests
-------------

Tests accompanying this module are given in `program_reduction.plt`. Tests
can be loaded with:

```
?- ['program_reduction.plt'].
```

Once loaded, tests can be run with:

```
?- run_tests.
```

Consulting the file load.pl at the root of this directory will also load
the test suite.

