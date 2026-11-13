# CV18 model audit surface

A reader can audit the formal statement of CV18 Theorem 1.1 by reading this
directory, in this order:

1. `Prelude.lean` defines the parameters, convex-body input, membership
   oracle, accuracy predicate, oracle-program syntax, and headline rates.
2. `Pseudocode.lean` defines the interpreter, the Figure 1 cooling schedule,
   the shape of one Figure 1 run with abstract sampling primitives, and the
   exact parameter-only query rate.  Its public worst-case membership cost is
   derived with `Arlib.Computation.Charged`, using the membership operation of
   the sealed `Roster` carrier.  Its final part fills in the primitives and
   defines `cv18Program`, the concrete membership-oracle algorithm the theorem
   is about: sampling laws, every numeric parameter, the lazy Metropolis ball
   walk with a proper-step clock, speedy-to-target rejection, the per-phase
   estimator, the global query cap, and median amplification.  Its only proofs
   are the side conditions the definitions need to type-check.
3. `Theorem.lean` states Theorem 1.1 for `cv18Program`.  The theorem has no
   hypotheses beyond the input promise, and `#print axioms` shows only Lean's
   standard axioms.

`Theorem.lean` runs `#modelClosureOfType cv18TheoremOneOne`, and
`Pseudocode.lean` runs `#modelClosure cv18Program`.  The build fails if
unfolding either reaches a declaration from any other module of this package.
Membership is decided by the defining module, so vendored background files
that declare names in foreign namespaces (such as `Arlib.MarkovChains`) are
caught too.  The proof is allowed to use `Analysis/`; that is precisely the
separation between a small statement audit and the supporting derivation.

The directory contains only what the statement reaches.  Supporting
definitions used solely by the proof (the query-counting interpreter `run`,
the syntax-level `QueryBound` certificate, the general Figure 1 skeleton, and
measurability helpers) live in `Analysis/ModelSupport.lean`.
