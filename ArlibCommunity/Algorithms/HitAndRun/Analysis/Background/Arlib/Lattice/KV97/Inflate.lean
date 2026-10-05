/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.Polytope
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Lattice.KV97.Defs

/-!
# Kannan–Vempala's inflated polytope `P'`, and the volume it costs

Kannan–Vempala's Theorem 2 samples from the **inflated** polytope

  `P' = {x | A x ≤ b + (c + √(2 log r)) ‖A‖}`

and rounds the sample to a lattice point. This file packages `P'` as
`Arlib.KV97.inflated` — the `Arlib.Polytope.inflate` of `body A b` by the
displacement `Arlib.KV97.kappaOf c r` — and records the volume facts the rest of
the development consumes.

## Main results

* `Arlib.KV97.inflated` — the set `P'`, together with `convex_inflated`,
  `isClosed_inflated`, `measurableSet_inflated` and `body_subset_inflated`.
* `Arlib.KV97.volume_body_ne_zero`, `Arlib.KV97.volume_inflated_ne_zero` — an
  inscribed ball of radius `γ > 0` makes both volumes nonzero.
* `Arlib.KV97.volume_inflated_le` — `vol P' ≤ (1 + κ/γ)ⁿ · vol P`, the
  specialisation of `Arlib.Polytope.volume_inflate_le` to `κ = kappaOf c r`.
* `Arlib.KV97.volume_inflated_ne_top` — `vol P' ≠ ∞`, **given** `vol P ≠ ∞`.
* `Arlib.KV97.toReal_volume_inflated_pos`,
  `Arlib.KV97.toReal_volume_inflated_le` — the real-valued forms, which are what
  Theorem 2's `1/Vol(P')` actually needs.
* `Arlib.KV97.inv_pow_le_toReal_volume_ratio` — **Lemma 1's shape**: the
  acceptance probability of the rejection step is bounded below,
  `vol P / vol P' ≥ (1 + κ/γ)^{-n}`. This is the inequality
  `sections/proof-appendix.tex:183` uses to say the rejection step is cheap.

## Implementation notes

**Finiteness is a hypothesis, not a theorem.** An unbounded polytope genuinely
has infinite volume, and nothing in `body A b` rules that out (the index type
`ι` is arbitrary and may even be empty). So every statement that needs
`vol P' < ∞`, and every `toReal` statement, carries `volume (body A b) ≠ ⊤` as
an explicit hypothesis. Similarly `0 < γ` and the inscribed ball are carried
explicitly: with `γ = 0` the ratio `κ/γ` collapses to `0` under Lean's
`x / 0 = 0` convention and the bound would be green but vacuous.

**On the parameter `r`.** `kappaOf c r` is stated for an arbitrary real `r`; no
lemma here interprets it as a facet count. KV97's `r` is the *maximum number of
facets meeting any unit cube around a lattice point* — a local quantity — while
the consuming paper's `cor:linf` uses the *total* facet count. The total
upper-bounds the local one, so substituting it only weakens the bound, but the
two are not the same number; see `AUDIT-KV97.md` §4d. Nothing in this file
asserts they are equal.
-/

namespace Arlib.KV97

open MeasureTheory Set
open scoped InnerProductSpace ENNReal

variable {n : ℕ} {ι : Type*} {A : ι → EuclideanSpace ℝ (Fin n)} {b : ι → ℝ}
  {cen : EuclideanSpace ℝ (Fin n)} {γ c r : ℝ}

/-! ## The inflated polytope `P'` -/

/-- **The inflated polytope `P'` of Kannan–Vempala's Theorem 2**: the body
`{x | A x ≤ b}` with every facet pushed outwards by the metric displacement
`κ = c + √(2 log r)`. -/
noncomputable def inflated (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ) (c r : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  Arlib.Polytope.inflate A b (kappaOf c r)

/-- Membership in `P'`, unfolded to the defining inequalities. -/
theorem mem_inflated {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ inflated A b c r ↔ ∀ i, ⟪A i, x⟫_ℝ ≤ b i + kappaOf c r * ‖A i‖ :=
  Iff.rfl

/-- `P'` is convex. -/
theorem convex_inflated (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ) (c r : ℝ) :
    Convex ℝ (inflated A b c r) :=
  Arlib.Polytope.convex_inflate A b _

/-- `P'` is closed. -/
theorem isClosed_inflated (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ) (c r : ℝ) :
    IsClosed (inflated A b c r) :=
  Arlib.Polytope.isClosed_inflate A b _

/-- `P'` is measurable, so its volume is meaningful. -/
theorem measurableSet_inflated (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ) (c r : ℝ) :
    MeasurableSet (inflated A b c r) :=
  Arlib.Polytope.measurableSet_inflate A b _

/-- **`P ⊆ P'`.** Inflating by a nonnegative displacement only grows the body;
`0 ≤ c` suffices, since `√(2 log r) ≥ 0` unconditionally. -/
theorem body_subset_inflated (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ) {c : ℝ}
    (r : ℝ) (hc : 0 ≤ c) : Arlib.Polytope.body A b ⊆ inflated A b c r :=
  Arlib.Polytope.body_subset_inflate A b (kappaOf_nonneg hc)

/-! ## Positivity and finiteness of the two volumes -/

/-- **A body with an inscribed ball has positive volume.** The ball is open and
nonempty, and Lebesgue measure is positive on nonempty open sets. -/
theorem volume_body_ne_zero (hγ : 0 < γ)
    (hball : Metric.ball cen γ ⊆ Arlib.Polytope.body A b) :
    volume (Arlib.Polytope.body A b) ≠ 0 := by
  have hpos : 0 < volume (Metric.ball cen γ) :=
    Metric.measure_ball_pos volume cen hγ
  exact (hpos.trans_le (measure_mono hball)).ne'

/-- **`P'` has positive volume**, since it contains `P`, which contains a ball of
radius `γ > 0`. -/
theorem volume_inflated_ne_zero (hγ : 0 < γ) (hc : 0 ≤ c)
    (hball : Metric.ball cen γ ⊆ Arlib.Polytope.body A b) :
    volume (inflated A b c r) ≠ 0 := by
  have hsub : Metric.ball cen γ ⊆ inflated A b c r :=
    hball.trans (body_subset_inflated A b r hc)
  have hpos : 0 < volume (Metric.ball cen γ) :=
    Metric.measure_ball_pos volume cen hγ
  exact (hpos.trans_le (measure_mono hsub)).ne'

/-- **The volume cost of inflating (`ℝ≥0∞` form).**

`vol P' ≤ (1 + κ/γ)ⁿ · vol P` whenever `P` contains a ball of radius `γ > 0`.
This is `Arlib.Polytope.volume_inflate_le` at `κ = kappaOf c r`; the hypothesis
`0 ≤ c` is what makes that displacement nonnegative. -/
theorem volume_inflated_le (hγ : 0 < γ) (hc : 0 ≤ c)
    (hball : Metric.ball cen γ ⊆ Arlib.Polytope.body A b) :
    volume (inflated A b c r) ≤
      ENNReal.ofReal ((1 + kappaOf c r / γ) ^ n) * volume (Arlib.Polytope.body A b) :=
  Arlib.Polytope.volume_inflate_le hγ (kappaOf_nonneg hc) hball

/-- **`P'` has finite volume as soon as `P` does.** Finiteness of `P` is a genuine
hypothesis: an unbounded polytope has infinite volume, and `body A b` may well be
unbounded. -/
theorem volume_inflated_ne_top (hγ : 0 < γ) (hc : 0 ≤ c)
    (hball : Metric.ball cen γ ⊆ Arlib.Polytope.body A b)
    (hfin : volume (Arlib.Polytope.body A b) ≠ ⊤) :
    volume (inflated A b c r) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (volume_inflated_le (r := r) hγ hc hball)
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin

/-! ## The real-valued forms

Theorem 2 divides by `Vol(P')`, so what it actually consumes is a *real* number
that is positive. These are the `ENNReal.toReal` transfers of the three facts
above; each needs both `≠ 0` and `≠ ⊤`, which is why `hfin` reappears. -/

/-- **`Vol(P) > 0` as a real number.** -/
theorem toReal_volume_body_pos (hγ : 0 < γ)
    (hball : Metric.ball cen γ ⊆ Arlib.Polytope.body A b)
    (hfin : volume (Arlib.Polytope.body A b) ≠ ⊤) :
    0 < (volume (Arlib.Polytope.body A b)).toReal :=
  ENNReal.toReal_pos (volume_body_ne_zero hγ hball) hfin

/-- **`Vol(P') > 0` as a real number** — the quantity Theorem 2 inverts. -/
theorem toReal_volume_inflated_pos (hγ : 0 < γ) (hc : 0 ≤ c)
    (hball : Metric.ball cen γ ⊆ Arlib.Polytope.body A b)
    (hfin : volume (Arlib.Polytope.body A b) ≠ ⊤) :
    0 < (volume (inflated A b c r)).toReal :=
  ENNReal.toReal_pos (volume_inflated_ne_zero hγ hc hball)
    (volume_inflated_ne_top hγ hc hball hfin)

/-- **The volume cost of inflating (real form).**
`Vol(P') ≤ (1 + κ/γ)ⁿ · Vol(P)` as real numbers. -/
theorem toReal_volume_inflated_le (hγ : 0 < γ) (hc : 0 ≤ c)
    (hball : Metric.ball cen γ ⊆ Arlib.Polytope.body A b)
    (hfin : volume (Arlib.Polytope.body A b) ≠ ⊤) :
    (volume (inflated A b c r)).toReal ≤
      (1 + kappaOf c r / γ) ^ n * (volume (Arlib.Polytope.body A b)).toReal := by
  have hk : (0:ℝ) < 1 + kappaOf c r / γ := by
    have : (0:ℝ) ≤ kappaOf c r / γ := div_nonneg (kappaOf_nonneg hc) hγ.le
    linarith
  have hpow : (0:ℝ) ≤ (1 + kappaOf c r / γ) ^ n := pow_nonneg hk.le n
  have htop : ENNReal.ofReal ((1 + kappaOf c r / γ) ^ n) *
      volume (Arlib.Polytope.body A b) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have h := ENNReal.toReal_mono htop (volume_inflated_le (r := r) hγ hc hball)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hpow] at h

/-! ## Lemma 1's shape: the acceptance probability is bounded below -/

/-- **The rejection step is cheap.**

`Vol(P) / Vol(P') ≥ (1 + κ/γ)^{-n}` whenever `P` contains a ball of radius
`γ > 0` and has finite volume. This is the form the acceptance-probability
argument of `sections/proof-appendix.tex:183` uses: a draw from `P'` lands in `P`
with probability at least `(1 + κ/γ)^{-n}`, which is bounded below by a constant
as soon as `κ/γ = O(1/n)`.

It is `Arlib.KV97.toReal_volume_inflated_le` divided through; the positivity of
`Vol(P')` (`Arlib.KV97.toReal_volume_inflated_pos`) is what makes the division
legitimate rather than a `x / 0 = 0` artefact. -/
theorem inv_pow_le_toReal_volume_ratio (hγ : 0 < γ) (hc : 0 ≤ c)
    (hball : Metric.ball cen γ ⊆ Arlib.Polytope.body A b)
    (hfin : volume (Arlib.Polytope.body A b) ≠ ⊤) :
    ((1 + kappaOf c r / γ) ^ n)⁻¹ ≤
      (volume (Arlib.Polytope.body A b)).toReal / (volume (inflated A b c r)).toReal := by
  have hk : (0:ℝ) < 1 + kappaOf c r / γ := by
    have : (0:ℝ) ≤ kappaOf c r / γ := div_nonneg (kappaOf_nonneg hc) hγ.le
    linarith
  have hpow : (0:ℝ) < (1 + kappaOf c r / γ) ^ n := pow_pos hk n
  have hW : 0 < (volume (inflated A b c r)).toReal :=
    toReal_volume_inflated_pos hγ hc hball hfin
  have hle := toReal_volume_inflated_le (r := r) hγ hc hball hfin
  rw [le_div_iff₀ hW]
  calc ((1 + kappaOf c r / γ) ^ n)⁻¹ * (volume (inflated A b c r)).toReal
      ≤ ((1 + kappaOf c r / γ) ^ n)⁻¹ *
          ((1 + kappaOf c r / γ) ^ n * (volume (Arlib.Polytope.body A b)).toReal) :=
        mul_le_mul_of_nonneg_left hle (inv_nonneg.2 hpow.le)
    _ = (volume (Arlib.Polytope.body A b)).toReal :=
        inv_mul_cancel_left₀ hpow.ne' _

/-- The same bound with the inverse taken facet-wise,
`((1 + κ/γ)⁻¹)ⁿ ≤ Vol(P)/Vol(P')`. Notationally this is the `(1 + κ/γ)^{-n}` of
the paper; it is `Arlib.KV97.inv_pow_le_toReal_volume_ratio` rewritten by
`inv_pow`. -/
theorem inv_pow_le_toReal_volume_ratio' (hγ : 0 < γ) (hc : 0 ≤ c)
    (hball : Metric.ball cen γ ⊆ Arlib.Polytope.body A b)
    (hfin : volume (Arlib.Polytope.body A b) ≠ ⊤) :
    ((1 + kappaOf c r / γ)⁻¹) ^ n ≤
      (volume (Arlib.Polytope.body A b)).toReal / (volume (inflated A b c r)).toReal := by
  rw [inv_pow]
  exact inv_pow_le_toReal_volume_ratio hγ hc hball hfin

end Arlib.KV97
