# CV18 model audit surface

A reader can audit the formal statement of CV18 Theorem 1.1 by reading this
directory, in this order:

1. `Prelude.lean` defines the parameters, convex-body input, membership
   oracle, accuracy predicate, oracle-program syntax, and headline rates.
2. `Pseudocode.lean` defines the interpreter, Figure 1 pseudocode, and the exact
   parameter-only query rate.  Its public worst-case membership cost is derived
   with `Arlib.Computation.Charged`, using the membership operation of the
   sealed `Roster` carrier.  Cooling schedules remain internal construction
   data and are not quantified by the headline theorem.
3. `Prior.lean` records imported mathematical assumptions.  It is empty: the
   headline theorem has no project-specific axioms or unproved premises.
4. `Theorem.lean` states Theorem 1.1 and selects the verified implementation.

`Theorem.lean` runs `#modelClosureOfType cv18TheoremOneOne`.  The build fails
if unfolding the theorem statement reaches any CV18 declaration outside this
directory.  The proof is allowed to use `Analysis/`; that is precisely the
separation between a small statement audit and the supporting derivation.
