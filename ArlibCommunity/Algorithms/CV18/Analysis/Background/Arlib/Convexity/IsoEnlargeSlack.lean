/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.Convexity.OneDimSharp

/-!
# `thm:iso` from *approximate* open enlargements

`Arlib.gaussianRestricted_isoperimetry_of_openClosed_enlargement`
(`Arlib/Convexity/IsoOpenClosed.lean:1114`) reduces the measurable case of Cousins–Vempala's
`thm:iso` to the open/closed case, but it demands **exact** open supersets `S₁ ⊆ U₁`, `S₂ ⊆ U₂`
holding the separation at the *same* `d` — and
`Arlib.exists_separated_no_disjoint_open_enlargement` (`Arlib/Convexity/IsoOpenClosed.lean:1205`)
shows such supersets need not exist.

This file supplies the reduction that consumes the enlargements one can actually build: open sets
that cover `S₁, S₂` only up to `ε` of `h`-mass, leave a residual `(U₁ ∪ U₂)ᶜ` no larger than `S₃`
up to `2ε`, and hold the separation only at a strictly smaller parameter `d' < d`.

## Main results

* `Arlib.gaussianRestricted_isoperimetry_of_enlargement_slack` — the slack-tolerant reduction.
  From disjoint open `U₁, U₂` with `∫_{S₁}h − ε ≤ ∫_{U₁}h`, `∫_{S₂}h − ε ≤ ∫_{U₂}h`,
  `∫_{(U₁∪U₂)ᶜ}h ≤ ∫_{S₃}h + 2ε` and the separation at `d`, it gives
  `(d/σ)·max 0 (∫_{S₁}h − ε)·max 0 (∫_{S₂}h − ε) ≤ (∫h)·(∫_{S₃}h + 2ε)`.
  Pure monotonicity on top of `Arlib.gaussianRestricted_isoperimetry_openClosed_logTwo`, applied to
  the open/closed partition `U₁, U₂, (U₁ ∪ U₂)ᶜ`.  The `max 0 (·)` truncations make the statement
  unconditionally true — no positivity of `∫_{Sᵢ}h − ε` is assumed — and the consumer discharges
  them by `max_eq_right` once `ε ↓ 0`.
* `Arlib.gaussianRestricted_isoperimetry_measurable_of_enlargements` — the limit.  If enlargements
  of the above kind exist for **every** `ε > 0` and **every** `d' ∈ (0, d)`, then `thm:iso` holds
  for the (arbitrary — not even measurable) sets `S₁, S₂, S₃` at the full parameter `d`.  Both
  limits are elementary: `ε ↓ 0` along `𝓝[>] 0` and `d' ↑ d` along `𝓝[<] d`, each by
  `le_of_tendsto_of_tendsto'` against a continuous function of the parameter.
* `Arlib.exists_enlargements_witness` — non-vacuity.  The standard Gaussian (`σ = 1`, `f ≡ 1`) and
  the **closed** slab partition `S₁ = {⟪e,x⟫ ≤ −1/4}`, `S₂ = {1/4 ≤ ⟪e,x⟫}`, `S₃` the open middle,
  at `d = log 2 / 4`, satisfy the whole hypothesis bundle of the previous theorem — `henl`
  included, discharged by the fixed open slabs `U₁ = {⟪e,x⟫ < −1/8}`, `U₂ = {1/8 < ⟪e,x⟫}` — with
  a strictly positive left-hand side.  Note `S₁, S₂` are *not* open there, so the open/closed
  capstone does not apply to this data directly; the enlargement route is doing real work.

## What is assumed

**Nothing beyond the imported results.**  No `def`, `structure` or named `Prop` below asserts any
part of `thm:iso` or of the Localization Lemma.  Both reductions are monotonicity and limits over
`Arlib.gaussianRestricted_isoperimetry_openClosed_logTwo`, whose own hypotheses (`h = f·γ_σ` with
`f` log-concave and nonnegative, `h` continuous, bounded, integrable, `0 < ∫h`) are threaded
through unchanged.  In particular `h ≥ 0` is *derived* from `hh` and `hf₀`, which is what makes
every set integral below nonnegative and the monotonicity go through.

The existence of the enlargements is **not** proved here: it is the hypothesis `henl` of the
second theorem, and the third theorem only shows that hypothesis is inhabited.
-/

open MeasureTheory Set Filter Metric

open scoped ENNReal Topology

namespace Arlib

section Slack

variable {n : ℕ}

set_option linter.unusedVariables false in
/-- **The measurable case from *approximate* disjoint open enlargements, at the same `d`.**

The slack-tolerant form of `Arlib.gaussianRestricted_isoperimetry_of_openClosed_enlargement`:
`U₁, U₂` need not contain `S₁, S₂`, only capture their `h`-mass up to `ε`, and the residual
`(U₁ ∪ U₂)ᶜ` need not sit inside `S₃`, only carry no more than `2ε` extra mass.  No partition
hypothesis on `S₁, S₂, S₃` is needed — the three sets enter only through their integrals.

The proof is `Arlib.gaussianRestricted_isoperimetry_openClosed_logTwo` on the honest open/closed
partition `U₁, U₂, (U₁ ∪ U₂)ᶜ`, then three monotonicities:
`max 0 (∫_{S₁}h − ε) ≤ ∫_{U₁}h` (by `hsl₁` and nonnegativity of the right side), likewise for
`S₂`, and `∫_{(U₁∪U₂)ᶜ}h ≤ ∫_{S₃}h + 2ε` (`hres`) against the nonnegative factor `∫h`.

`hε : 0 ≤ ε` is accepted and **not used**: the `max 0 (·)` truncations already make the statement
true for every real `ε`, `hres` being the only place `ε` enters on the right.  It is kept in the
signature because every consumer has it and its absence would be a surprise. -/
theorem gaussianRestricted_isoperimetry_of_enlargement_slack (hn : 2 ≤ n) {σ d B : ℝ}
    (hσ : 0 < σ) (hd : 0 < d)
    {f h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf₀ : ∀ x, 0 ≤ f x) (hfc : IsLogConcave f)
    (hh : ∀ x, h x = f x * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))
    (hhc : Continuous h) (hhB : ∀ x, h x ≤ B) (hhi : Integrable h)
    {S₁ S₂ S₃ U₁ U₂ : Set (EuclideanSpace ℝ (Fin n))}
    (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hUdisj : Disjoint U₁ U₂)
    (hmass : 0 < ∫ x, h x)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hsl₁ : (∫ x in S₁, h x) - ε ≤ ∫ x in U₁, h x)
    (hsl₂ : (∫ x in S₂, h x) - ε ≤ ∫ x in U₂, h x)
    (hres : (∫ x in (U₁ ∪ U₂)ᶜ, h x) ≤ (∫ x in S₃, h x) + 2 * ε)
    (hsep : ∀ u ∈ U₁, ∀ v ∈ U₂,
      d / Real.log 2 ≤ ‖u - v‖ ∨ 4 * (d / σ) * Real.sqrt n ≤ densDist h u v) :
    d / σ * (max 0 ((∫ x in S₁, h x) - ε) * max 0 ((∫ x in S₂, h x) - ε))
      ≤ (∫ x, h x) * ((∫ x in S₃, h x) + 2 * ε) := by
  have h0 : ∀ x, 0 ≤ h x := fun x => by
    rw [hh]; exact mul_nonneg (hf₀ x) (Real.exp_pos _).le
  have hdσ : 0 ≤ d / σ := (div_pos hd hσ).le
  have hpart' : IsPartition3 Set.univ U₁ U₂ (U₁ ∪ U₂)ᶜ :=
    { union := Set.union_compl_self (U₁ ∪ U₂)
      disjoint₁₂ := hUdisj
      disjoint₁₃ := Set.disjoint_left.mpr fun a ha hc => hc (Or.inl ha)
      disjoint₂₃ := Set.disjoint_left.mpr fun a ha hc => hc (Or.inr ha) }
  have hmain := gaussianRestricted_isoperimetry_openClosed_logTwo hn hσ hf₀ hfc hh hhc hhB hhi
    hpart' hU₁ hU₂ (hU₁.union hU₂).isClosed_compl hmass hsep
  have hq₁ : 0 ≤ ∫ x in U₁, h x := integral_nonneg fun x => h0 x
  have hq₂ : 0 ≤ ∫ x in U₂, h x := integral_nonneg fun x => h0 x
  have hle₁ : max 0 ((∫ x in S₁, h x) - ε) ≤ ∫ x in U₁, h x := max_le hq₁ hsl₁
  have hle₂ : max 0 ((∫ x in S₂, h x) - ε) ≤ ∫ x in U₂, h x := max_le hq₂ hsl₂
  calc d / σ * (max 0 ((∫ x in S₁, h x) - ε) * max 0 ((∫ x in S₂, h x) - ε))
      ≤ d / σ * ((∫ x in U₁, h x) * ∫ x in U₂, h x) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hle₁ hle₂ (le_max_left _ _) hq₁) hdσ
    _ ≤ (∫ x, h x) * ∫ x in (U₁ ∪ U₂)ᶜ, h x := hmain
    _ ≤ (∫ x, h x) * ((∫ x in S₃, h x) + 2 * ε) :=
        mul_le_mul_of_nonneg_left hres hmass.le

/-- **`thm:iso` for arbitrary `S₁, S₂, S₃`, from a family of approximate open enlargements.**

`henl` asks, for every mass slack `ε > 0` and every separation parameter `d' ∈ (0, d)`, for a pair
of disjoint open sets capturing `∫_{S₁}h, ∫_{S₂}h` up to `ε`, leaving a residual of mass at most
`∫_{S₃}h + 2ε`, and separated at `d'`.  Given that family, the conclusion holds at the full `d`
with no slack at all.

The proof is `Arlib.gaussianRestricted_isoperimetry_of_enlargement_slack` at each `(ε, d')`
followed by two elementary limits:

* `ε ↓ 0` along `𝓝[>] 0` at fixed `d'`, where the left side tends to
  `(d'/σ)·(∫_{S₁}h)(∫_{S₂}h)` — this is where `max 0 (∫_{Sᵢ}h − ε) → ∫_{Sᵢ}h` uses `h ≥ 0` — and
  the right side to `(∫h)·∫_{S₃}h`;
* `d' ↑ d` along `𝓝[<] d`, where the left side is linear in `d'` and the right side constant.

No measurability, and no partition hypothesis, is required of `S₁, S₂, S₃`: they enter only
through their integrals and through `henl`. -/
theorem gaussianRestricted_isoperimetry_measurable_of_enlargements (hn : 2 ≤ n) {σ d B : ℝ}
    (hσ : 0 < σ) (hd : 0 < d)
    {f h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf₀ : ∀ x, 0 ≤ f x) (hfc : IsLogConcave f)
    (hh : ∀ x, h x = f x * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))
    (hhc : Continuous h) (hhB : ∀ x, h x ≤ B) (hhi : Integrable h)
    {S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))}
    (hmass : 0 < ∫ x, h x)
    (henl : ∀ ε > (0 : ℝ), ∀ d' : ℝ, 0 < d' → d' < d →
      ∃ U₁ U₂ : Set (EuclideanSpace ℝ (Fin n)),
        IsOpen U₁ ∧ IsOpen U₂ ∧ Disjoint U₁ U₂ ∧
        ((∫ x in S₁, h x) - ε ≤ ∫ x in U₁, h x) ∧
        ((∫ x in S₂, h x) - ε ≤ ∫ x in U₂, h x) ∧
        ((∫ x in (U₁ ∪ U₂)ᶜ, h x) ≤ (∫ x in S₃, h x) + 2 * ε) ∧
        (∀ u ∈ U₁, ∀ v ∈ U₂,
          d' / Real.log 2 ≤ ‖u - v‖ ∨ 4 * (d' / σ) * Real.sqrt n ≤ densDist h u v)) :
    d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x) ≤ (∫ x, h x) * ∫ x in S₃, h x := by
  have h0 : ∀ x, 0 ≤ h x := fun x => by
    rw [hh]; exact mul_nonneg (hf₀ x) (Real.exp_pos _).le
  have hP₁ : 0 ≤ ∫ x in S₁, h x := integral_nonneg fun x => h0 x
  have hP₂ : 0 ≤ ∫ x in S₂, h x := integral_nonneg fun x => h0 x
  -- the conclusion at every `d' < d`, obtained by letting `ε ↓ 0`
  have step : ∀ d' : ℝ, 0 < d' → d' < d →
      d' / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x) ≤ (∫ x, h x) * ∫ x in S₃, h x := by
    intro d' hd'0 hd'd
    have hslack : ∀ ε : ℝ, 0 < ε →
        d' / σ * (max 0 ((∫ x in S₁, h x) - ε) * max 0 ((∫ x in S₂, h x) - ε))
          ≤ (∫ x, h x) * ((∫ x in S₃, h x) + 2 * ε) := by
      intro ε hε
      obtain ⟨U₁, U₂, hU₁, hU₂, hUdisj, hsl₁, hsl₂, hres, hsep⟩ := henl ε hε d' hd'0 hd'd
      exact gaussianRestricted_isoperimetry_of_enlargement_slack hn hσ hd'0 hf₀ hfc hh hhc hhB hhi
        hU₁ hU₂ hUdisj hmass hε.le hsl₁ hsl₂ hres hsep
    have hL : Tendsto (fun ε : ℝ =>
        d' / σ * (max 0 ((∫ x in S₁, h x) - ε) * max 0 ((∫ x in S₂, h x) - ε)))
        (𝓝[>] (0 : ℝ)) (𝓝 (d' / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x))) := by
      have hc : Continuous fun ε : ℝ =>
          d' / σ * (max 0 ((∫ x in S₁, h x) - ε) * max 0 ((∫ x in S₂, h x) - ε)) :=
        continuous_const.mul
          ((continuous_const.max (continuous_const.sub continuous_id)).mul
            (continuous_const.max (continuous_const.sub continuous_id)))
      have ht := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa [max_eq_right hP₁, max_eq_right hP₂] using ht
    have hR : Tendsto (fun ε : ℝ => (∫ x, h x) * ((∫ x in S₃, h x) + 2 * ε))
        (𝓝[>] (0 : ℝ)) (𝓝 ((∫ x, h x) * ∫ x in S₃, h x)) := by
      have hc : Continuous fun ε : ℝ => (∫ x, h x) * ((∫ x in S₃, h x) + 2 * ε) := by fun_prop
      have ht := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using ht
    refine le_of_tendsto_of_tendsto hL hR ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε using hslack ε hε
  -- now `d' ↑ d`
  have hL2 : Tendsto (fun t : ℝ => t / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x)) (𝓝[<] d)
      (𝓝 (d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x))) := by
    have hc : Continuous fun t : ℝ => t / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x) := by fun_prop
    exact (hc.tendsto d).mono_left (nhdsWithin_le_nhds (s := Set.Iio d))
  refine le_of_tendsto hL2 ?_
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hd)]
    with t ht1 ht2 using step t ht2 ht1

end Slack

/-! ### Non-vacuity: the enlargement hypothesis is inhabited -/

section Witness

variable {n : ℕ}

/-- **The closed-slab partition.**  For a vector `e` and `c > 0`, the two *closed* half-spaces
`⟪e,x⟫ ≤ −c` and `c ≤ ⟪e,x⟫` together with the open slab between them partition `ℝⁿ`.

The mirror image of `Arlib.isPartition3_slab`, which puts the two half-spaces open and the slab
closed.  This is the shape for which the open/closed capstone
`Arlib.gaussianRestricted_isoperimetry_openClosed_logTwo` does **not** apply directly. -/
theorem isPartition3_closedSlab (e : EuclideanSpace ℝ (Fin n)) {c : ℝ} (hc0 : 0 < c) :
    IsPartition3 Set.univ {x | (inner ℝ e x : ℝ) ≤ -c} {x | c ≤ (inner ℝ e x : ℝ)}
      {x | -c < (inner ℝ e x : ℝ) ∧ (inner ℝ e x : ℝ) < c} where
  union := by
    ext x
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    rcases le_or_gt (inner ℝ e x : ℝ) (-c) with h | h
    · exact Or.inl (Or.inl h)
    · rcases le_or_gt c (inner ℝ e x : ℝ) with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr ⟨h, h'⟩
  disjoint₁₂ := by
    rw [Set.disjoint_left]
    rintro x hx hx'
    simp only [Set.mem_setOf_eq] at hx hx'
    linarith
  disjoint₁₃ := by
    rw [Set.disjoint_left]
    rintro x hx hx'
    simp only [Set.mem_setOf_eq] at hx hx'
    linarith [hx'.1]
  disjoint₂₃ := by
    rw [Set.disjoint_left]
    rintro x hx hx'
    simp only [Set.mem_setOf_eq] at hx hx'
    linarith [hx'.2]

/-- A closed half-space bounded by a unit normal is **not** open: its boundary point `c·e` is a
limit of points just outside. -/
theorem not_isOpen_inner_le {e : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1) (c : ℝ) :
    ¬ IsOpen {x : EuclideanSpace ℝ (Fin n) | (inner ℝ e x : ℝ) ≤ c} := by
  have hee : (inner ℝ e e : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  intro hopen
  have hmem : (c • e : EuclideanSpace ℝ (Fin n)) ∈ {x : EuclideanSpace ℝ (Fin n) |
      (inner ℝ e x : ℝ) ≤ c} := by
    simp only [Set.mem_setOf_eq, real_inner_smul_right, hee, mul_one]
    exact le_rfl
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen _ hmem
  have hy : (c • e + (r / 2) • e : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball (c • e) r := by
    rw [Metric.mem_ball, dist_eq_norm]
    have : (c • e + (r / 2) • e : EuclideanSpace ℝ (Fin n)) - c • e = (r / 2) • e := by abel
    rw [this, norm_smul, Real.norm_eq_abs, he, mul_one, abs_of_nonneg (by linarith)]
    linarith
  have := hball hy
  simp only [Set.mem_setOf_eq, inner_add_right, real_inner_smul_right, hee, mul_one] at this
  linarith

/-- The mirror of `Arlib.not_isOpen_inner_le` for the opposite half-space. -/
theorem not_isOpen_le_inner {e : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1) (c : ℝ) :
    ¬ IsOpen {x : EuclideanSpace ℝ (Fin n) | c ≤ (inner ℝ e x : ℝ)} := by
  have hee : (inner ℝ e e : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  intro hopen
  have hmem : (c • e : EuclideanSpace ℝ (Fin n)) ∈ {x : EuclideanSpace ℝ (Fin n) |
      c ≤ (inner ℝ e x : ℝ)} := by
    simp only [Set.mem_setOf_eq, real_inner_smul_right, hee, mul_one]
    exact le_rfl
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen _ hmem
  have hy : (c • e - (r / 2) • e : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball (c • e) r := by
    rw [Metric.mem_ball, dist_eq_norm]
    have : (c • e - (r / 2) • e : EuclideanSpace ℝ (Fin n)) - c • e = (-(r / 2)) • e := by
      rw [neg_smul]; abel
    rw [this, norm_smul, Real.norm_eq_abs, he, mul_one, abs_of_nonpos (by linarith)]
    linarith
  have := hball hy
  simp only [Set.mem_setOf_eq, inner_sub_right, real_inner_smul_right, hee, mul_one] at this
  linarith

/-- **Non-vacuity of `Arlib.gaussianRestricted_isoperimetry_measurable_of_enlargements`** — in
particular of its enlargement hypothesis `henl`, which is the only strong one.

The data is `σ = 1`, `f ≡ 1` — so `h` is the standard Gaussian, continuous, bounded by `1`,
integrable, of positive total mass — the **closed** slab partition orthogonal to the first
coordinate axis,

  `S₁ = {⟪e,x⟫ ≤ −1/4}`,  `S₂ = {1/4 ≤ ⟪e,x⟫}`,  `S₃ = {−1/4 < ⟪e,x⟫ < 1/4}`,

and `d = log 2 / 4`.  `henl` is discharged, for **every** `ε > 0` and every `d' ∈ (0, d)`, by the
single pair of open half-spaces

  `U₁ = {⟪e,x⟫ < −1/8}`,  `U₂ = {1/8 < ⟪e,x⟫}`,

which are disjoint, contain `S₁, S₂` (so the two mass clauses hold with slack to spare, for every
`ε > 0`), leave the residual `(U₁ ∪ U₂)ᶜ = {|⟪e,x⟫| ≤ 1/8} ⊆ S₃`, and are separated by
`1/4 = 2·(1/8) ≤ ‖u − v‖ ≥ d'/log 2`, the last inequality because `d' < log 2/4`.

Two clauses are recorded beyond the theorem's hypotheses: `S₁` and `S₂` are **not open**
(`Arlib.not_isOpen_inner_le`, `Arlib.not_isOpen_le_inner`), so
`Arlib.gaussianRestricted_isoperimetry_openClosed_logTwo` does not apply to this data directly and
the enlargement really is what carries it; and the conclusion is a **strictly positive** lower
bound, so the instance is not the trivial `0 ≤ 0`. -/
theorem exists_enlargements_witness (hn : 2 ≤ n) :
    ∃ (f h : EuclideanSpace ℝ (Fin n) → ℝ)
      (S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))) (σ d B : ℝ),
      0 < σ ∧ 0 < d ∧ (∀ x, 0 ≤ f x) ∧ IsLogConcave f ∧
      (∀ x, h x = f x * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) ∧
      Continuous h ∧ (∀ x, h x ≤ B) ∧ Integrable h ∧
      IsPartition3 Set.univ S₁ S₂ S₃ ∧
      (0 < ∫ x, h x) ∧
      (∀ ε > (0 : ℝ), ∀ d' : ℝ, 0 < d' → d' < d →
        ∃ U₁ U₂ : Set (EuclideanSpace ℝ (Fin n)),
          IsOpen U₁ ∧ IsOpen U₂ ∧ Disjoint U₁ U₂ ∧
          ((∫ x in S₁, h x) - ε ≤ ∫ x in U₁, h x) ∧
          ((∫ x in S₂, h x) - ε ≤ ∫ x in U₂, h x) ∧
          ((∫ x in (U₁ ∪ U₂)ᶜ, h x) ≤ (∫ x in S₃, h x) + 2 * ε) ∧
          (∀ u ∈ U₁, ∀ v ∈ U₂,
            d' / Real.log 2 ≤ ‖u - v‖ ∨ 4 * (d' / σ) * Real.sqrt n ≤ densDist h u v)) ∧
      ¬ IsOpen S₁ ∧ ¬ IsOpen S₂ ∧
      0 < d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x) := by
  classical
  set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ) with hedef
  have he : ‖e‖ = 1 := by rw [hedef, PiLp.norm_single]; norm_num
  set h : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => Real.exp (-‖x‖ ^ 2 / (2 * (1 : ℝ) ^ 2)) with hhdef
  have h0 : ∀ x, 0 ≤ h x := fun x => (Real.exp_pos _).le
  have hhc : Continuous h := by rw [hhdef]; fun_prop
  have hhB : ∀ x, h x ≤ 1 := by
    intro x
    rw [hhdef]
    simp only
    refine Real.exp_le_one_iff.mpr ?_
    have hx : (0 : ℝ) ≤ ‖x‖ ^ 2 := sq_nonneg _
    have h2 : (2 : ℝ) * 1 ^ 2 = 2 := by norm_num
    rw [h2]
    linarith
  have hhi : Integrable h := by
    have heq : h = fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-(‖x‖ ^ 2) / (2 * 1)) := by
      funext x; rw [hhdef]; norm_num
    rw [heq]
    exact Arlib.GaussianCooling.integrable_gaussian_eucl one_pos
  -- balls of radius `1/8` about `r·e`, for `|r| ≤ 1/2`, sit in the unit ball
  have hballs : ∀ r : ℝ, |r| ≤ 1 / 2 → ∀ x ∈ Metric.ball (r • e) (1 / 8),
      ‖x‖ ≤ 1 ∧ |(inner ℝ e x : ℝ) - r| < 1 / 8 := by
    intro r hr x hx
    rw [Metric.mem_ball, dist_eq_norm] at hx
    have hre : ‖r • e‖ ≤ 1 / 2 := by
      rw [norm_smul, Real.norm_eq_abs, he, mul_one]; exact hr
    refine ⟨?_, ?_⟩
    · have hle : ‖x‖ ≤ ‖x - r • e‖ + ‖r • e‖ := by
        simpa using norm_add_le (x - r • e) (r • e)
      linarith
    · have hip := abs_real_inner_le_norm e (x - r • e)
      rw [he, one_mul, inner_sub_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq, he] at hip
      simpa using hip.trans_lt hx
  have hlow : ∀ r : ℝ, |r| ≤ 1 / 2 → ∀ x ∈ Metric.ball (r • e) (1 / 8),
      Real.exp (-(1 : ℝ) / 2) ≤ h x := by
    intro r hr x hx
    obtain ⟨hx1, -⟩ := hballs r hr x hx
    rw [hhdef]
    simp only
    refine Real.exp_le_exp.mpr ?_
    have hx2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
    have h2 : (2 : ℝ) * 1 ^ 2 = 2 := by norm_num
    rw [h2]
    linarith
  set S₁ : Set (EuclideanSpace ℝ (Fin n)) := {x | (inner ℝ e x : ℝ) ≤ -(1 / 4 : ℝ)} with hS₁def
  set S₂ : Set (EuclideanSpace ℝ (Fin n)) := {x | (1 / 4 : ℝ) ≤ (inner ℝ e x : ℝ)} with hS₂def
  set S₃ : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | -(1 / 4 : ℝ) < (inner ℝ e x : ℝ) ∧ (inner ℝ e x : ℝ) < 1 / 4} with hS₃def
  set U₁ : Set (EuclideanSpace ℝ (Fin n)) := {x | (inner ℝ e x : ℝ) < -(1 / 8 : ℝ)} with hU₁def
  set U₂ : Set (EuclideanSpace ℝ (Fin n)) := {x | (1 / 8 : ℝ) < (inner ℝ e x : ℝ)} with hU₂def
  have hme : Continuous fun x : EuclideanSpace ℝ (Fin n) => (inner ℝ e x : ℝ) :=
    continuous_const.inner continuous_id
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hmono : ∀ {S T : Set (EuclideanSpace ℝ (Fin n))}, S ⊆ T →
      (∫ x in S, h x) ≤ ∫ x in T, h x := by
    intro S T hST
    exact setIntegral_mono_set hhi.integrableOn (Filter.Eventually.of_forall h0) hST.eventuallyLE
  have hM : 0 < ∫ x, h x := by
    have hpos := setIntegral_pos_of_ball_le (z := ((1 / 2 : ℝ) • e)) (r := 1 / 8)
      (c := Real.exp (-(1 : ℝ) / 2)) hhi h0 (by norm_num) (Real.exp_pos _) (Set.subset_univ _)
      (hlow (1 / 2) (by norm_num))
    rwa [setIntegral_univ] at hpos
  have hp1 : 0 < ∫ x in S₁, h x := by
    refine setIntegral_pos_of_ball_le (z := (-(1 / 2 : ℝ) • e)) (r := 1 / 8)
      (c := Real.exp (-(1 : ℝ) / 2)) hhi h0 (by norm_num) (Real.exp_pos _) ?_
      (hlow (-(1 / 2)) (by norm_num))
    intro x hx
    obtain ⟨-, hx2⟩ := hballs (-(1 / 2)) (by norm_num) x hx
    rw [hS₁def]
    simp only [Set.mem_setOf_eq]
    rw [abs_lt] at hx2
    linarith [hx2.2]
  have hp2 : 0 < ∫ x in S₂, h x := by
    refine setIntegral_pos_of_ball_le (z := ((1 / 2 : ℝ) • e)) (r := 1 / 8)
      (c := Real.exp (-(1 : ℝ) / 2)) hhi h0 (by norm_num) (Real.exp_pos _) ?_
      (hlow (1 / 2) (by norm_num))
    intro x hx
    obtain ⟨-, hx2⟩ := hballs (1 / 2) (by norm_num) x hx
    rw [hS₂def]
    simp only [Set.mem_setOf_eq]
    rw [abs_lt] at hx2
    linarith [hx2.1]
  refine ⟨fun _ => (1 : ℝ), h, S₁, S₂, S₃, 1, Real.log 2 / 4, 1, one_pos, by linarith,
    fun _ => zero_le_one, isLogConcave_const zero_le_one, fun x => by rw [hhdef]; ring,
    hhc, hhB, hhi, isPartition3_closedSlab e (by norm_num : (0 : ℝ) < 1 / 4), hM, ?_, ?_, ?_, ?_⟩
  · -- the enlargement family: the fixed pair of open half-spaces at `±1/8`
    intro ε hε d' hd'0 hd'd
    refine ⟨U₁, U₂, isOpen_lt hme continuous_const, isOpen_lt continuous_const hme, ?_, ?_, ?_,
      ?_, ?_⟩
    · rw [Set.disjoint_left]
      rintro x hx hx'
      rw [hU₁def] at hx
      rw [hU₂def] at hx'
      simp only [Set.mem_setOf_eq] at hx hx'
      linarith
    · have hsub : S₁ ⊆ U₁ := by
        intro x hx
        rw [hS₁def] at hx
        rw [hU₁def]
        simp only [Set.mem_setOf_eq] at hx ⊢
        linarith
      linarith [hmono hsub]
    · have hsub : S₂ ⊆ U₂ := by
        intro x hx
        rw [hS₂def] at hx
        rw [hU₂def]
        simp only [Set.mem_setOf_eq] at hx ⊢
        linarith
      linarith [hmono hsub]
    · have hsub : (U₁ ∪ U₂)ᶜ ⊆ S₃ := by
        intro x hx
        have hx1 : x ∉ U₁ := fun hc => hx (Or.inl hc)
        have hx2 : x ∉ U₂ := fun hc => hx (Or.inr hc)
        rw [hU₁def] at hx1
        rw [hU₂def] at hx2
        simp only [Set.mem_setOf_eq, not_lt] at hx1 hx2
        rw [hS₃def]
        simp only [Set.mem_setOf_eq]
        constructor <;> linarith
      linarith [hmono hsub]
    · intro u hu v hv
      left
      rw [hU₁def] at hu
      rw [hU₂def] at hv
      simp only [Set.mem_setOf_eq] at hu hv
      have hgeo := two_mul_le_norm_sub_of_inner_lt (e := e) he (c := (1 / 8 : ℝ)) hu hv
      have hd'l : d' / Real.log 2 ≤ 1 / 4 := by
        rw [div_le_iff₀ hlog2]
        linarith
      linarith
  · rw [hS₁def]; exact not_isOpen_inner_le he _
  · rw [hS₂def]; exact not_isOpen_le_inner he _
  · have h1 : (0 : ℝ) < Real.log 2 / 4 / 1 := by
      rw [div_one]; linarith
    exact mul_pos h1 (mul_pos hp1 hp2)

end Witness

/-! ### Axiom audit -/

#print axioms Arlib.gaussianRestricted_isoperimetry_of_enlargement_slack
#print axioms Arlib.gaussianRestricted_isoperimetry_measurable_of_enlargements
#print axioms Arlib.isPartition3_closedSlab
#print axioms Arlib.not_isOpen_inner_le
#print axioms Arlib.not_isOpen_le_inner
#print axioms Arlib.exists_enlargements_witness

end Arlib
