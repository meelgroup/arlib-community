# CV18 model audit surface

A reader can audit the formal statement of CV18 Theorem 1.1 by reading this
directory, in this order:

1. `Prelude.lean` holds the definitions:
   - the problem: parameters, the convex body with its unit-ball promise, the
     membership oracle, the volume, and what counts as an accurate estimate;
   - the language programs are written in (`MembershipOracleProgram`, with
     `do` notation and the primitives `isMember`, `drawPoint`, `drawReal`)
     and its output law (`runEstimate`);
   - the cooling schedule, the sampling laws, the acceptance probabilities and
     estimator weights;
   - every numeric parameter and complexity expression, including the query
     rate of Theorem 1.1 (`queryRate`) and its constant
     (`queryConstant`).
2. `Pseudocode.lean` holds the cost model and the algorithm:
   - `queryCost`: the worst-case number of membership calls, each costing
     exactly `1`;
   - `cv18Program`: Figure 1 in `do` notation, followed by the median of
     independent runs.  The header shows Figure 1 and lists the three places
     where the program differs from it; each difference is marked
     **Deviation** in the code.
3. `Theorem.lean` states Theorem 1.1 for `cv18Program`: accuracy with
   probability at least `1 - p`, and `queryCost` at most
   `⌈queryConstant · queryRate q⌉`.  The theorem has no
   hypotheses beyond the input promise, and `#print axioms` shows only Lean's
   standard axioms.

`Theorem.lean` runs `#modelClosureOfType cv18TheoremOneOne`, and
`Pseudocode.lean` runs `#modelClosure cv18Program`.  The build fails if
unfolding either reaches a declaration from any other module of this package.
Membership is decided by the defining module, so vendored background files
that declare names in foreign namespaces (such as `Arlib.MarkovChains`) are
caught too.  The proof is allowed to use `Analysis/`; that is precisely the
separation between a small statement audit and the supporting derivation.

The proof was developed against the same algorithm written with the program
constructors (`Analysis/ScheduledProgram.lean`);
`Analysis/PseudocodeBridge.lean` proves it equal to `cv18Program`.  Other
definitions used only by the proof (the query-counting interpreter `run`, the
syntax-level `QueryBound` certificate, the general Figure 1 skeleton, and
measurability helpers) live in `Analysis/ModelSupport.lean`.
