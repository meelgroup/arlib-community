/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Rejection sampling: conditioning, and the arithmetic of the accept/reject ratio

An algorithm that can sample from a superset `S'` of the set `S` it really wants,
with only *approximately* uniform mass on `S`, turns that into a sampler for `S`
by the oldest trick there is: draw, and repeat until the draw lands in `S`.  This
module proves the two facts such a loop needs.

## What is proved

**1. Conditioning (`condOn`).**  `condOn μ S` is the law of a `μ`-draw conditioned
on landing in `S`: the restriction of `μ` to `S`, renormalised.  Its event
probabilities are `condOn_apply`, `μ (T ∩ S) / μ S`; it is a probability measure
as soon as `μ S` is neither `0` nor `∞` (`isProbabilityMeasure_condOn`); and it
is supported in `S` (`condOn_compl_eq_zero`).  This is what "repeat until the draw
lands in `S`" produces.

**2. The ratio bound (`Rejection.ratio_mem_relErr`).**  This is the arithmetic
core, and it is stated over plain reals and a `Finset` sum so that it is reusable
independently of any measure-theoretic packaging.  Let `ι` be a nonempty
`Fintype` with `N = Fintype.card ι`, let `V > 0`, let `0 ≤ θ ≤ 1/2`, and suppose
the unnormalised weights `w : ι → ℝ` satisfy

    (1 - θ) / V ≤ w i ≤ 1 / V     for every `i`.

Then for every `i`,

    (1 - θ) / N ≤ w i / (∑ j, w j) ≤ (1 + 2θ) / N.

The proof is exactly the paper's.  Summing the hypothesis over the `N` indices
bounds the acceptance mass, `(1-θ)N/V ≤ ∑ w ≤ N/V` (`Rejection.sum_bounds`);
dividing the smaller numerator by the larger denominator gives the lower bound
(`Rejection.ratio_lower`) and the other pairing gives `1/((1-θ)N)`, which is at
most `(1+2θ)/N` because `1/(1-θ) ≤ 1 + 2θ` for `θ ≤ 1/2`
(`Rejection.one_div_one_sub_le`, `Rejection.ratio_upper`).

The shape a caller wants is `Rejection.ratio_mem_relErr_of_eps`: with a relative
error budget `0 < ε ≤ 1` and the per-index bound at `θ = ε/2`, the normalised
weights are within a multiplicative `1 ± ε` of uniform on `ι`.

**3. Termination (`Rejection.sum_pos`).**  The same hypotheses give
`0 < ∑ j, w j`, i.e. the acceptance probability is positive, so the repetition
ends with probability `1`.

## Note on scope

Part 2 and Part 3 live in the namespace `Arlib.Rejection` rather than directly in
`Arlib`, because names such as `sum_pos` and `sum_bounds` are far too generic to
sit at the top of a shared staging namespace.
-/

namespace Arlib

open MeasureTheory
open scoped BigOperators ENNReal

/-! ## Part 1: conditioning a measure on an event -/

section Conditioning

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The law of a `μ`-distributed draw **conditioned on landing in `S`**: the
restriction of `μ` to `S`, renormalised by `μ S`.

With the Mathlib convention `x / 0 = 0` (and `(∞)⁻¹ = 0`) this is the zero
measure when `μ S` is `0` or `∞`; the interesting hypotheses `μ S ≠ 0` and
`μ S ≠ ∞` are carried explicitly by the lemmas that need them. -/
noncomputable def condOn (μ : Measure Ω) (S : Set Ω) : Measure Ω :=
  (μ S)⁻¹ • μ.restrict S

/-- Unfolding lemma for `condOn`. -/
theorem condOn_def (μ : Measure Ω) (S : Set Ω) :
    condOn μ S = (μ S)⁻¹ • μ.restrict S := rfl

/-- **Conditional probability.**  `condOn μ S` assigns to an event `T` the mass
`μ (T ∩ S) / μ S`. -/
theorem condOn_apply (μ : Measure Ω) {S T : Set Ω} (_hS : MeasurableSet S)
    (hT : MeasurableSet T) : condOn μ S T = μ (T ∩ S) / μ S := by
  rw [condOn_def, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hT,
    ENNReal.div_eq_inv_mul]

/-- The total mass of `condOn μ S` is `1` as soon as `μ S` is neither `0` nor
`∞`, so conditioning really does produce a probability measure. -/
theorem condOn_univ (μ : Measure Ω) {S : Set Ω} (h0 : μ S ≠ 0) (htop : μ S ≠ ⊤) :
    condOn μ S Set.univ = 1 := by
  rw [condOn_def, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ,
    ENNReal.inv_mul_cancel h0 htop]

/-- **`condOn μ S` is a probability measure** when `μ S ∉ {0, ∞}`. -/
theorem isProbabilityMeasure_condOn (μ : Measure Ω) {S : Set Ω} (h0 : μ S ≠ 0)
    (htop : μ S ≠ ⊤) : IsProbabilityMeasure (condOn μ S) :=
  ⟨condOn_univ μ h0 htop⟩

/-- **`condOn μ S` is supported in `S`**: the complement of `S` is null. -/
theorem condOn_compl_eq_zero (μ : Measure Ω) {S : Set Ω} (hS : MeasurableSet S) :
    condOn μ S Sᶜ = 0 := by
  rw [condOn_def, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hS.compl,
    Set.compl_inter_self, measure_empty, mul_zero]

end Conditioning

/-! ## Part 2: the arithmetic of the accept/reject ratio -/

namespace Rejection

variable {ι : Type*} [Fintype ι]

/-- **The acceptance mass is pinned between `(1-θ)N/V` and `N/V`.**  This is the
paper's step "summing the hypothesis over the `N` points of `P ∩ L^n`". -/
theorem sum_bounds (w : ι → ℝ) (V θ : ℝ)
    (hlow : ∀ i, (1 - θ) / V ≤ w i) (hhigh : ∀ i, w i ≤ 1 / V) :
    (1 - θ) * (Fintype.card ι : ℝ) / V ≤ ∑ j, w j ∧
      ∑ j, w j ≤ (Fintype.card ι : ℝ) / V := by
  constructor
  · calc (1 - θ) * (Fintype.card ι : ℝ) / V
        = ∑ _j : ι, (1 - θ) / V := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ ∑ j, w j := Finset.sum_le_sum fun i _ => hlow i
  · calc ∑ j, w j
        ≤ ∑ _j : ι, 1 / V := Finset.sum_le_sum fun i _ => hhigh i
    _ = (Fintype.card ι : ℝ) / V := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- **`1/(1-θ) ≤ 1 + 2θ` for `0 ≤ θ ≤ 1/2`.**  The final step of the paper's
upper bound: `(1+2θ)(1-θ) = 1 + θ(1-2θ) ≥ 1`. -/
theorem one_div_one_sub_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1 / 2) :
    1 / (1 - θ) ≤ 1 + 2 * θ := by
  have hpos : (0 : ℝ) < 1 - θ := by linarith
  rw [div_le_iff₀ hpos]
  nlinarith

/-- **The acceptance mass is positive**, so the rejection loop terminates with
probability `1`.  Positivity comes from the lower bound `(1-θ)N/V` of
`sum_bounds`, which is a product of three positive factors. -/
theorem sum_pos [Nonempty ι] (w : ι → ℝ) {V θ : ℝ} (hV : 0 < V) (hθ : θ ≤ 1 / 2)
    (hlow : ∀ i, (1 - θ) / V ≤ w i) (hhigh : ∀ i, w i ≤ 1 / V) :
    0 < ∑ j, w j := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hnum : (0 : ℝ) < (1 - θ) * (Fintype.card ι : ℝ) := by nlinarith
  exact lt_of_lt_of_le (div_pos hnum hV) (sum_bounds w V θ hlow hhigh).1

/-- **Lower bound on the normalised weight.**  Dividing the smaller numerator
`(1-θ)/V` by the larger denominator `N/V` gives `(1-θ)/N`. -/
theorem ratio_lower [Nonempty ι] (w : ι → ℝ) {V θ : ℝ} (hV : 0 < V) (_h0 : 0 ≤ θ)
    (hθ : θ ≤ 1 / 2) (hlow : ∀ i, (1 - θ) / V ≤ w i) (hhigh : ∀ i, w i ≤ 1 / V)
    (i : ι) : (1 - θ) / (Fintype.card ι : ℝ) ≤ w i / (∑ j, w j) := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hS : 0 < ∑ j, w j := sum_pos w hV hθ hlow hhigh
  have hwi : 0 ≤ w i :=
    le_trans (div_nonneg (by linarith) hV.le) (hlow i)
  -- `V`-cleared forms of the two hypotheses actually used.
  have h1 : 1 - θ ≤ w i * V := by
    have := hlow i; rwa [div_le_iff₀ hV] at this
  have h2 : (∑ j, w j) * V ≤ (Fintype.card ι : ℝ) := by
    have := (sum_bounds w V θ hlow hhigh).2; rwa [le_div_iff₀ hV] at this
  rw [div_le_div_iff₀ hcard hS]
  nlinarith [mul_le_mul_of_nonneg_right h1 hS.le, mul_le_mul_of_nonneg_left h2 hwi]

/-- **Upper bound on the normalised weight.**  Dividing the larger numerator
`1/V` by the smaller denominator `(1-θ)N/V` gives `1/((1-θ)N)`, which is at most
`(1+2θ)/N` by `one_div_one_sub_le`. -/
theorem ratio_upper [Nonempty ι] (w : ι → ℝ) {V θ : ℝ} (hV : 0 < V) (h0 : 0 ≤ θ)
    (hθ : θ ≤ 1 / 2) (hlow : ∀ i, (1 - θ) / V ≤ w i) (hhigh : ∀ i, w i ≤ 1 / V)
    (i : ι) : w i / (∑ j, w j) ≤ (1 + 2 * θ) / (Fintype.card ι : ℝ) := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hS : 0 < ∑ j, w j := sum_pos w hV hθ hlow hhigh
  -- `V`-cleared forms of the two hypotheses actually used.
  have h3 : w i * V ≤ 1 := by
    have := hhigh i; rwa [le_div_iff₀ hV] at this
  have h4 : (1 - θ) * (Fintype.card ι : ℝ) ≤ (∑ j, w j) * V := by
    have := (sum_bounds w V θ hlow hhigh).1; rwa [div_le_iff₀ hV] at this
  rw [div_le_div_iff₀ hS hcard]
  -- multiply through by `V > 0` and use `(1+2θ)(1-θ) ≥ 1`
  refine le_of_mul_le_mul_right ?_ hV
  have step1 : w i * (Fintype.card ι : ℝ) * V ≤ (Fintype.card ι : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left h3 hcard.le]
  have step2 : (Fintype.card ι : ℝ) ≤ (1 + 2 * θ) * (∑ j, w j) * V := by
    nlinarith [mul_le_mul_of_nonneg_left h4 (show (0:ℝ) ≤ 1 + 2 * θ by linarith),
      mul_nonneg (mul_nonneg hcard.le h0) (show (0:ℝ) ≤ 1 - 2 * θ by linarith)]
  linarith

/-- **The headline.**  Under `(1-θ)/V ≤ w i ≤ 1/V` for all `i`, with `V > 0` and
`0 ≤ θ ≤ 1/2`, every normalised weight `w i / ∑ w` lies within
`[(1-θ)/N, (1+2θ)/N]`, where `N = Fintype.card ι`.

This is Corollary "cor:linf" of the paper, in its arithmetic form. -/
theorem ratio_mem_relErr [Nonempty ι] (w : ι → ℝ) {V θ : ℝ} (hV : 0 < V)
    (h0 : 0 ≤ θ) (hθ : θ ≤ 1 / 2) (hlow : ∀ i, (1 - θ) / V ≤ w i)
    (hhigh : ∀ i, w i ≤ 1 / V) (i : ι) :
    (1 - θ) / (Fintype.card ι : ℝ) ≤ w i / (∑ j, w j) ∧
      w i / (∑ j, w j) ≤ (1 + 2 * θ) / (Fintype.card ι : ℝ) :=
  ⟨ratio_lower w hV h0 hθ hlow hhigh i, ratio_upper w hV h0 hθ hlow hhigh i⟩

/-- **The headline, in the shape the caller wants.**  With a relative error
budget `0 < ε ≤ 1` and the per-index bound holding at `θ = ε/2`, the normalised
weights are within a multiplicative `1 ± ε` of uniform on `ι`:

    (1 - ε) / N ≤ w i / (∑ j, w j) ≤ (1 + ε) / N.

The lower bound is slack — `(1 - ε/2)/N` is what the argument actually gives —
and is stated at `1 - ε` only to match the caller's interface. -/
theorem ratio_mem_relErr_of_eps [Nonempty ι] (w : ι → ℝ) {V ε : ℝ} (hV : 0 < V)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hlow : ∀ i, (1 - ε / 2) / V ≤ w i)
    (hhigh : ∀ i, w i ≤ 1 / V) (i : ι) :
    (1 - ε) / (Fintype.card ι : ℝ) ≤ w i / (∑ j, w j) ∧
      w i / (∑ j, w j) ≤ (1 + ε) / (Fintype.card ι : ℝ) := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  obtain ⟨hl, hu⟩ :=
    ratio_mem_relErr w hV (by linarith) (by linarith) hlow hhigh i
  refine ⟨le_trans ?_ hl, ?_⟩
  · gcongr
    linarith
  · calc w i / (∑ j, w j) ≤ (1 + 2 * (ε / 2)) / (Fintype.card ι : ℝ) := hu
    _ = (1 + ε) / (Fintype.card ι : ℝ) := by ring_nf

/-! ## Part 4: two-sided weights

The lemmas above take the weights bounded *above by exactly* `1/V`, which is the
shape Kannan–Vempala's Theorem 2 has **if** its `ε` is read as an additive error.
That reading does not survive contact with the corollary — see `AUDIT-KV97.md`
§4b — and under the reading that does, the weights are pinned two-sidedly,
`(1−a)/V ≤ w i ≤ (1+b)/V`, with a genuine `(1+b)` on top.

This section is that version. It is stated for arbitrary bounds `L ≤ w i ≤ U`,
which is both more general and easier to use than carrying `V` around: the
normalising `V` cancels out of a ratio of weights, so it need not appear at all.
-/

/-- **The ratio of a weight to the total, from two-sided bounds.**

If every weight lies in `[L, U]` with `L > 0`, then each normalised weight lies in
`[L/(N·U), U/(N·L)]`, where `N` is the number of weights.

No normalising constant appears: `V` cancels, which is exactly why the accept /
reject step of a rejection sampler is insensitive to the volume of the region it
rejects from. -/
theorem ratio_bounds [Nonempty ι] (w : ι → ℝ) {L U : ℝ} (hL : 0 < L)
    (hlow : ∀ i, L ≤ w i) (hhigh : ∀ i, w i ≤ U) (i : ι) :
    L / ((Fintype.card ι : ℝ) * U) ≤ w i / (∑ j, w j) ∧
      w i / (∑ j, w j) ≤ U / ((Fintype.card ι : ℝ) * L) := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hU : 0 < U := lt_of_lt_of_le hL (le_trans (hlow (Classical.arbitrary ι))
    (hhigh (Classical.arbitrary ι)))
  -- the total is pinned between `N·L` and `N·U`
  have hsum_lo : (Fintype.card ι : ℝ) * L ≤ ∑ j, w j := by
    calc (Fintype.card ι : ℝ) * L = ∑ _j : ι, L := by
          rw [Finset.sum_const, Finset.card_univ]; ring
      _ ≤ ∑ j, w j := Finset.sum_le_sum fun j _ => hlow j
  have hsum_hi : ∑ j, w j ≤ (Fintype.card ι : ℝ) * U := by
    calc ∑ j, w j ≤ ∑ _j : ι, U := Finset.sum_le_sum fun j _ => hhigh j
      _ = (Fintype.card ι : ℝ) * U := by rw [Finset.sum_const, Finset.card_univ]; ring
  have hsum_pos : 0 < ∑ j, w j := lt_of_lt_of_le (by positivity) hsum_lo
  constructor
  · rw [div_le_div_iff₀ (by positivity) hsum_pos]
    nlinarith [hlow i, hsum_hi]
  · rw [div_le_div_iff₀ hsum_pos (by positivity)]
    -- `w i · (N·L) ≤ U · (N·L) ≤ U · ∑ w`
    have hNL : (0 : ℝ) ≤ (Fintype.card ι : ℝ) * L := by positivity
    calc w i * ((Fintype.card ι : ℝ) * L)
        ≤ U * ((Fintype.card ι : ℝ) * L) := mul_le_mul_of_nonneg_right (hhigh i) hNL
      _ ≤ U * (∑ j, w j) := mul_le_mul_of_nonneg_left hsum_lo hU.le

/-- **The two-sided corollary, in `(1±ε)` form.**

If every weight lies in `[(1−a)/V, (1+b)/V]` — the shape a *pointwise*
almost-uniform density gives — then each normalised weight lies in
`[(1−a)/((1+b)·N), (1+b)/((1−a)·N)]`.

`V` has cancelled. This is what Kannan–Vempala's `cor:linf` consumes, and the
asymmetry `(1−a)` vs `(1+b)` is what lets the two error sources (the escape
probability and the sampler's own deviation from uniform) be tracked separately
rather than merged into one `θ`. -/
theorem ratio_bounds_of_window [Nonempty ι] (w : ι → ℝ) {V a b : ℝ}
    (hV : 0 < V) (ha : a < 1) (hlow : ∀ i, (1 - a) / V ≤ w i)
    (hhigh : ∀ i, w i ≤ (1 + b) / V) (i : ι) :
    (1 - a) / ((1 + b) * (Fintype.card ι : ℝ)) ≤ w i / (∑ j, w j) ∧
      w i / (∑ j, w j) ≤ (1 + b) / ((1 - a) * (Fintype.card ι : ℝ)) := by
  have ha' : 0 < 1 - a := by linarith
  have hL : 0 < (1 - a) / V := by positivity
  obtain ⟨h1, h2⟩ := ratio_bounds w hL hlow hhigh i
  constructor
  · refine le_trans (le_of_eq ?_) h1
    field_simp
  · refine le_trans h2 (le_of_eq ?_)
    field_simp

end Rejection

end Arlib
