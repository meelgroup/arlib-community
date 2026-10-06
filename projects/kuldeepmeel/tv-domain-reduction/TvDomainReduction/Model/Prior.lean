import TvDomainReduction.Model.Prelude

/-!
# What this development assumes

The results this proof takes from prior work — cited, standard, or folklore —
stated as the hypotheses they are. `Prior` is a field per borrowed result, and the
theorem carries it as `(hprior : Prior)`, so what was granted is in the statement
rather than in a `sorry` somewhere under it.

When a later theorem needs assumptions the earlier theorems do not need, this
file may also hold another theorem-specific structure. Existing structures are
not widened just to state a new result.

It is empty because nothing has been surveyed yet. The pass that reads the
paper for what the proof leans on fills it in; until then the theorem assumes
nothing and `hprior` is discharged by `⟨⟩`.
-/

namespace TvDomainReduction

/-- Every result this development takes from prior work rather than proving. -/
-- TEX2LEAN: external-prior fields
structure Prior : Prop where

/-! ## A theorem-specific bundle: uniformity of the cited solver's constants

`thm:main_fptas`'s complexity claim (main.tex:794) is that the running time is
"polynomial in `n, k, 1/ε, log(1/η)`, and the maximum domain size `max_t |Ω_t|`".
That is a claim about **one** polynomial, uniform over instances *and* over
`(ε, η)`; an existential constant quantified after the instance is vacuous for a
run whose operation count is a fixed number, which is exactly what the handoff
notes at the bottom of `Model/Theorem.lean` already record about
`pc_fpras_time`.

`SparsifyPrior` is indexed by `(δ, η')`, and its suppressed constants
(`sizeConst`, `costConst`, `polylog`, `mmExp`) are **fields of that record**, so
they may differ for every `(δ, η')`.  So a uniform polynomial claim can only be
stated against a bundle of constants that every call's prior is required to
respect.  `SparsifyFamily` is that bundle and `SparsifyFamily.Member` is the
requirement.  Nothing about the accuracy claim needs it — that is still a single
`SparsifyPrior` binder — and `Prior` is **not** widened: these are new
declarations, used only by the new theorem.

The paper never says in which parameters its `Õ` hides logarithms.  That silence
is what `plConst` and `plDeg` record: the suppressed factor is *demanded* to be
at worst polynomial, rather than assumed to be polylogarithmic, because the
latter is not available from anything the paper states. -/

/-- **The suppressed constants of the cited Lewis-weight solver, shared across
all `(δ, η')`** (main.tex:745–752, cited to Cohen–Peng with the running time from
Lee–Sidford Thm 5.3.1 and Jambulapati et al. Lemma 2.5).

`sizeConst` and `costConst` bound the `O(·)` in `m = O(d log d/δ² · log(1/η))`
and the `Õ(·)` in `Õ(N d + d^ω)`; `plConst` and `plDeg` bound the solver's
suppressed `Õ` factor by a polynomial.  All four are plain naturals fixed
*before* any instance, which is the whole point. -/
structure SparsifyFamily where
  /-- A uniform bound on the constant suppressed by the `O(·)` in `m`. -/
  sizeConst : ℕ
  /-- A uniform bound on the constant suppressed by the `Õ(·)` in the solver's
  running time. -/
  costConst : ℕ
  /-- The coefficient of the polynomial bounding the solver's suppressed `Õ`
  factor. -/
  plConst : ℕ
  /-- The degree of that polynomial.  A fixed natural: it may not absorb the
  instance. -/
  plDeg : ℕ

/-- **`prior` is a member of the family `fam`**: its suppressed constants are
bounded by the family's, and its suppressed `Õ` factor is bounded by the
family's polynomial.

This is what makes the time claim's single `(c, D)` legitimate.  `SparsifyPrior`
already carries `2 ≤ mmExp ≤ 2.4` as a field of its own, uniformly in
`(δ, η')`, so `ω` needs nothing here. -/
structure SparsifyFamily.Member (fam : SparsifyFamily) {δ η' : ℝ}
    (prior : SparsifyPrior δ η') : Prop where
  /-- the prior's `O(·)` constant in `m` is at most the family's. -/
  sizeConst_le : prior.sizeConst ≤ fam.sizeConst
  /-- the prior's `Õ(·)` constant in the solver cost is at most the family's. -/
  costConst_le : prior.costConst ≤ fam.costConst
  /-- the prior's suppressed `Õ` factor is at worst polynomial, with the
  family's coefficient and degree. -/
  polylog_le : ∀ N : ℕ,
    (prior.polylog N : ℝ) ≤ fam.plConst * ((N : ℝ) + 2) ^ fam.plDeg

end TvDomainReduction
