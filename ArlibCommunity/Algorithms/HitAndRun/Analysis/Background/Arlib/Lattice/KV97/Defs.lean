/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Kannan–Vempala, *Sampling Lattice Points*: the constants

Vocabulary shared by the modules that build up Theorem 2 and its corollary. Only
the scalars and their arithmetic live here — no measure theory, no geometry — so
that the files proving the analytic and geometric halves can be developed
independently and still agree on what `κ`, `c` and the loss term mean.

## The statement being aimed at

> **Theorem 2** (Kannan–Vempala, STOC '97). Suppose `p` is drawn from a
> distribution on `P' = {x : Ax ≤ b + κ‖A‖}`, with `κ = c + √(2 log r)`, whose
> total-variation distance to the uniform distribution on `P'` is at most `ε`.
> Then for every lattice point `x ∈ P ∩ ℤⁿ`,
> `(1 − 2e^{−c²} − ε)/Vol(P') ≤ Pr[rnd p = x] ≤ 1/Vol(P')`.

`Arlib.KV97.kappaOf` is that `κ`, and `Arlib.KV97.lossOf` the loss `2e^{−c²} + ε`
subtracted in the lower bound.

## Which rendering of the exponent this development uses

The scanned original prints the loss as `1 − 2e^{−c}`. Its own proof applies
Azuma to the martingale `Zⱼ = ∑_{k≤j} A_{ik}Yₖ` with increments bounded by
`|A_{ij}|`, which yields `e^{−c²/2}` per facet — the printed `c` is missing a
square. The consuming paper's restatement (`sections/proof-appendix.tex:153`,
`claim:linf`) silently corrects it to `2e^{−c²}` and folds the facet count into
`κ` rather than carrying a factor `r` out front.

**Neither printed rendering is what comes out.** `Arlib.KV97.mul_exp_kappaOf_le`
(`Arlib/Lattice/KV97/Escape.lean`) proves that at the paper's own inflation
`κ = c + √(2·log r)`, the union bound over `r` facets gives

```
r · exp(−κ²/2)  ≤  exp(−c²/2).
```

So the loss is `e^{−c²/2}`, not `2e^{−c²}`: the paper's inflation and its stated
loss are inconsistent by a factor of `2` in the exponent. (Reaching `e^{−c²}`
needs the larger inflation `√2·c + √(2 log r)`, which is also available as
`Arlib.KV97.mul_exp_kappaOf_sqrt_two_le`.) The leading `2` is unnecessary too —
the escape event is one-sided per facet, and the union bound already accounts for
multiplicity.

`Arlib.KV97.lossOf` is therefore defined as `e^{−c²/2} + ε`, matching what is
proved rather than what is printed. See `AUDIT-KV97.md` §4a.

## The corollary's choice of `c`

`Arlib.KV97.cOf ε = √(2·log(4/ε))` is the value that makes the exponential half
of the loss exactly `ε/4` (`Arlib.KV97.exp_cOf`); paired with a sampler whose
density deviates from uniform by at most `ε/4` it gives a total loss of `ε/2`
(`Arlib.KV97.lossOf_cOf`), which is `≤ 1/2` and so admissible for the
`1/(1−θ) ≤ 1 + 2θ` step of `Arlib.Rejection.ratio_bounds_of_window`.

Note "deviates by `ε/4`" means **pointwise**, not in total variation —
`AUDIT-KV97.md` §4b explains why the total-variation reading does not work.
-/

namespace Arlib.KV97

open Real

/-- **The facet displacement `κ = c + √(2 log r)`.** `P` is inflated by `κ‖Aᵢ‖` on
each facet to form `P'`; the `√(2 log r)` term is what pays for the union bound
over `r` facets, and `c` is the free parameter that tunes the loss. -/
noncomputable def kappaOf (c r : ℝ) : ℝ := c + Real.sqrt (2 * Real.log r)

/-- **The loss `e^{−c²/2} + ε`** subtracted from `1` in Theorem 2's lower bound:
`e^{−c²/2}` for the chance that the rounded point escapes `P'`
(`Arlib.KV97.escape_prob_le_exp`), and `ε` for the sampler's deviation from
uniform.

**The exponent is `c²/2`, not `c²`, and there is no factor of `2`** — see the
"discrepancy" section of the module docstring. -/
noncomputable def lossOf (c ε : ℝ) : ℝ := Real.exp (-c ^ 2 / 2) + ε

/-- **The corollary's choice `c = √(2·log(4/ε))`**, tuned so that the exponential
half of the loss is exactly `ε/4`. -/
noncomputable def cOf (ε : ℝ) : ℝ := Real.sqrt (2 * Real.log (4 / ε))

section Arith

variable {ε : ℝ}

/-- `log(4/ε) ≥ 0` for `ε ∈ (0,1]` — what lets `√` and `·²` cancel in `cOf`. -/
theorem log_four_div_nonneg (hε0 : 0 < ε) (hε1 : ε ≤ 1) : 0 ≤ Real.log (4 / ε) := by
  refine Real.log_nonneg ?_
  rw [le_div_iff₀ hε0]
  linarith

/-- `cOf ε ^ 2 = 2·log(4/ε)`. -/
theorem cOf_sq (hε0 : 0 < ε) (hε1 : ε ≤ 1) : cOf ε ^ 2 = 2 * Real.log (4 / ε) :=
  Real.sq_sqrt (by have := log_four_div_nonneg hε0 hε1; linarith)

/-- `cOf ε` is nonnegative. -/
theorem cOf_nonneg : 0 ≤ cOf ε := Real.sqrt_nonneg _

/-- **The tuning identity: `e^{−(cOf ε)²/2} = ε/4`.** This is the whole point of
the choice `c = √(2·log(4/ε))`, and it is exactly the escape probability
`Arlib.KV97.escape_prob_le_exp` delivers at that `c`. -/
theorem exp_cOf (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    Real.exp (-(cOf ε) ^ 2 / 2) = ε / 4 := by
  have h : -(cOf ε) ^ 2 / 2 = -Real.log (4 / ε) := by
    rw [cOf_sq hε0 hε1]; ring
  rw [h, Real.exp_neg, Real.exp_log (by positivity)]
  field_simp

/-- **The corollary's total loss is `ε/2`**: `ε/4` from the escape probability and
`ε/4` from the sampler's total-variation error. -/
theorem lossOf_cOf (hε0 : 0 < ε) (hε1 : ε ≤ 1) : lossOf (cOf ε) (ε / 4) = ε / 2 := by
  rw [lossOf, exp_cOf hε0 hε1]; ring

/-- **The loss clears the `θ ≤ 1/2` bar** that `Arlib.Rejection.ratio_mem_relErr`
needs for `1/(1−θ) ≤ 1 + 2θ`. -/
theorem lossOf_cOf_le_half (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    lossOf (cOf ε) (ε / 4) ≤ 1 / 2 := by
  rw [lossOf_cOf hε0 hε1]; linarith

/-- The loss is nonnegative, so the lower bound of Theorem 2 is never claimed to
exceed the upper one. -/
theorem lossOf_nonneg {c : ℝ} (hε : 0 ≤ ε) : 0 ≤ lossOf c ε := by
  have : 0 < Real.exp (-c ^ 2 / 2) := Real.exp_pos _
  unfold lossOf; linarith

end Arith

section Kappa

variable {c r : ℝ}

/-- `κ` is nonnegative when `c` is. No hypothesis on `r` is needed: `Real.sqrt` is
nonnegative on all of `ℝ`, including where `log r < 0`. -/
theorem kappaOf_nonneg (hc : 0 ≤ c) : 0 ≤ kappaOf c r := by
  have h : 0 ≤ Real.sqrt (2 * Real.log r) := Real.sqrt_nonneg _
  unfold kappaOf; linarith

/-- `c ≤ κ` — inflating by `κ` inflates by at least `c`. -/
theorem le_kappaOf : c ≤ kappaOf c r := by
  have h : 0 ≤ Real.sqrt (2 * Real.log r) := Real.sqrt_nonneg _
  unfold kappaOf; linarith

end Kappa

end Arlib.KV97
