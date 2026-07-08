# sat-hs

Various SAT solving algorithms implemented in Haskell.

These programs each have their own executable, and the project is built with ghc
and cabal.

```sh
cabal build
```

Will create both executables in the `dist-newstyle/build/...` directory [TODO].


## DP (Davis-Putnam) or Directional Resolution

```sh
sat-dp [CNF_FILE] [-R VAR_ORDER] [--help]

CNF_FILE : Input DIMACS CNF file, if not provided reads from stdin.

-R : Variable bucket order heuristic, VAR_ORDER in {numeric, fewest, jw}.

Outputs log messages SAT/UNSAT, and list of satisfying variable assignments.
```

The DP algorithm uses the resolution rule to eliminate (existentially quantify)
variables until it derives an empty clause (contradiction), at which point it
can conclude the formula is unsatisfiable. If no contradiction can be derived,
it concludes the formula is satisfiable and generates a satisfying variable
assignment using the original formula and generated resolvents.

The algorithm is implemented using the "Bucket Elimination" technique described
in "The DP Algorithm" section of the "Handbook of Satisfiability" 2nd edition.


## DPLL (Davis-Putnam-Logemann-Loveland) Algorithm

```sh
sat-dpll [CNF_FILE] [-R SPLIT_ORDER] [-p] [-u] [--help]

CNF_FILE : Input DIMACS CNF file, if not provided reads from stdin.

-R : Variable splitting order heuristic, SPLIT_ORDER in {numeric, fewest, jw}.
-p : Enable pure literal elimination as preprocessing step.
-u : Enable unit clause propagation at each node of the search tree.

Outputs log messages SAT/UNSAT, and list of satisfying variable assignments.
```
