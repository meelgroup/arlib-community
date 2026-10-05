/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.MetropolisConductance
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.StarPolar

/-!
# The *sharp* conductance route for the Metropolis-filtered Gaussian ball walk

`Arlib/MarkovChains/Continuous/MetropolisConductance.lean` already proves a conductance
bound for `Arlib.MarkovChains.metropolisGaussian K δ s`, but an **exponentially small** one:
its acceptance floor is the density *sandwich* `α ≤ g(y)`, discharged at
`α = e^{-R²/(2s)}`, which at the Cousins-Vempala parameters (`s = σ²`, `R ≍ σ√n`) is
`e^{-n/2}`.  This file runs the **sharp** route instead — the one that goes through
`Arlib.MarkovChains.conductance_speedyGaussian_ge`, whose conclusion is
`Ω(δ·log 2/(σ·√n))` — and the single change that makes it work is that the acceptance is
bounded below by a **ratio** estimate rather than a sandwich estimate.

## The crux: ratio, not sandwich

`Arlib.MarkovChains.le_metropolisAccept` bounds `min(1, g(y)/g(x))` below by `g(y)` alone,
throwing away `g(x)`.  But a Metropolis step only ever proposes `y` with `‖y − x‖ < δ`, and
along such a step the two weights are *close*:

    g(y)/g(x) = exp((‖x‖² − ‖y‖²)/(2s))  ≥  exp(−(2Rδ + δ²)/(2s))   for ‖x‖ ≤ R, ‖y − x‖ ≤ δ.

So on a body `K ⊆ R·Bₙ` the acceptance probability is at least

    a  :=  exp(−(2Rδ + δ²)/(2s)),

and this is a genuine **constant** in the Cousins-Vempala regime: at `s = σ²`, `R ≍ σ√n`
and `δ ≤ σ/(8√n)` one gets `2Rδ/(2s) = Rδ/σ² ≲ 1/8`, hence `a ≳ e^{-1/8} ≈ 0.88`.
Contrast `e^{-R²/(2s)} = e^{-n/2}`.  That is the whole gain, and it is `metropolisAccept_ge`.

## The obstruction this file does **not** remove: the local-conductance floor is forced

`Arlib.MarkovChains.overlap_speedyWalk_convex` (`StarPolar.lean:518`) proves `cor:overlap`
for the **speedy** walk with *no* floor on the local conductance `ell`.  That argument does
**not** transfer to `metropolisGaussian`, and the reason is structural, not technical:

* `speedyWalk K δ x` normalises by `vol(B(x,δ) ∩ K)` — it *conditions* on the proposal
  landing in `K` — so the small factor `ell` cancels out of the ratio.
* `metropolisGaussian K δ s x` normalises by `vol(B(x,δ))`, the **full** ball, and parks the
  rejected mass on a Dirac atom at `x`.

Concretely, `hoverlap` is **false** for this kernel without a floor.  For `u ∈ T` the Dirac
term contributes nothing to `P_u(Tᶜ)`, so

    P_u(Tᶜ) ≤ vol(δBₙ)⁻¹ · vol(Tᶜ ∩ K ∩ B(u,δ)) ≤ ell K δ u,   and likewise P_v(T) ≤ ell K δ v.

Taking `K` a thin convex cone and `u`, `v` both within `δ/n` of its apex makes both `ell`s
as small as one likes, and `1 ≤ 20·(P_u(Tᶜ) + P_v(T))` fails.  So a floor is unavoidable
here; `metropolisGaussian_overlap_of_convex` carries one.

**What the convex/StarPolar route does still buy** is a much *weaker* floor.
`Arlib.MarkovChains.overlap_speedyWalk`'s floor is `11 ≤ 20·ell`, i.e. `ell ≥ 11/20 > 1/2`,
which fails at **every** boundary point of **every** bounded body (there `ell ≈ 1/2`).  The
floor here is
    1 ≤ 20 · a · (1 − 1/n)ⁿ · θ,    θ a lower bound for `ell` on `K`,
and since `(1 − 1/n)ⁿ ≥ 1/(e+1)`, at `a ≈ 1` this asks only `θ ≳ (e+1)/20 ≈ 0.19` — which a
smooth body does satisfy.  `exists_conductance_metropolisGaussian_sharp_witness` exhibits
a bounded convex body meeting it (there `ell ≡ 1/4` and `a = e^{-1/64}`).

## The other inherited cost: separation `δ/n`, not `δ/√n`

`volume_lens_inter_ge_max` — the convexity input — holds at `‖u − v‖ ≤ δ/n`.  Feeding that
into `conductance_speedyGaussian_ge`, whose `hoverlap` binder is at `δ/√n`, forces the
instantiation `δ_thm := δ/√n`, exactly as `Arlib.MarkovChains.conductance_speedyWalk_ge_of_convex`
(`StarPolar.lean:598`) already does for the speedy walk.  The conclusion is therefore
`Ω(δ·log 2/(σ·n))`, a `√n` worse than the paper's.  **This loss is inherited from the
convexity lemma, not introduced here.**

## Main results

* `metropolisAccept_ge` — **the crux**: the ratio acceptance floor `a = e^{-(2Rδ+δ²)/(2s)}`.
* `mul_volume_le_setLIntegral_metropolisDensity`, `mul_volume_le_metropolisGaussian` — the
  resulting domination of the one-step law by `a · vol(δBₙ)⁻¹ · vol(· ∩ B(x,δ) ∩ K)`.
* `metropolisGaussian_overlap_of_convex` — `cor:overlap` for this kernel, at separation
  `δ/n`, under the weak floor above.
* `integrableOn_gaussianWeightReal`, `withDensity_gaussianWeight_eq_ofReal_setIntegral`,
  `uniformOn_gaussianWeight_eq_div`, `integral_gaussianIndicator_pos` — the `π ↔ h` bridges
  (`hpi`, `hmass`).
* `conductance_metropolisGaussian_sharp_ge` — **the headline**,
  `Φ ≥ δ·log 2/(640·σ·n)`, with `hiso` left as a binder.
* `exists_conductance_metropolisGaussian_sharp_witness` — non-vacuity: every hypothesis of
  the headline *except* `hiso` is jointly satisfiable at a bounded convex body, the bound
  there is `> 0`, and the overlap conclusion genuinely holds.

## What is assumed

`hiso` — Cousins-Vempala's `thm:iso` — is a **binder** of
`conductance_metropolisGaussian_sharp_ge`, shaped to match `conductance_speedyGaussian_ge`'s
binder verbatim (at `δ/√n`), so that it composes with `Arlib.gaussianRestricted_isoperimetry`
without glue.  It is **not** proved here or anywhere in this repository.  Consequently
**nothing in this file is a mixing-time statement or an `O*(n³)` claim, and none of it may
be quoted as one.**  There is no `def`, `structure` or named `Prop` in this file; every
declaration is a `theorem`.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

variable {n : ℕ}

/-! ## 1. The crux: the ratio acceptance floor -/

/-- **The acceptance probability along a `δ`-step from a point of norm `≤ R` is at least
`e^{-(2Rδ+δ²)/(2s)}`.**

This is the estimate that separates the sharp route from
`Arlib/MarkovChains/Continuous/MetropolisConductance.lean`.  There,
`Arlib.MarkovChains.le_metropolisAccept` discards `g(x)` and bounds
`min(1, g(y)/g(x)) ≥ g(y) ≥ e^{-R²/(2s)}` — exponentially small at the Cousins-Vempala
parameters.  Here the ratio is kept:

    g(y)/g(x) = exp((‖x‖² − ‖y‖²)/(2s))  and  ‖y‖² ≤ (‖x‖+δ)² ≤ ‖x‖² + 2Rδ + δ²,

so the loss is only what a step of length `δ` can cost, not what the whole body can cost.
At `s = σ²`, `R ≍ σ√n`, `δ ≤ σ/(8√n)` the bound is `≥ e^{-1/8} ≈ 0.88`: a constant.

Note the hypothesis is on `dist y x`, matching the proposal support `Metric.ball x δ`, and
that `‖x‖ ≤ R` is required — this is the `R`-dependence the ball-walk arguments do not have.
-/
theorem metropolisAccept_ge {s : ℝ} (hs : 0 < s) {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ ≤ R) (hxy : dist y x ≤ δ) :
    ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s))) ≤ metropolisAccept s x y := by
  rw [metropolisAccept_eq_ofReal]
  refine ENNReal.ofReal_le_ofReal (le_min ?_ ?_)
  · rw [← Real.exp_zero]
    refine Real.exp_le_exp.2 ?_
    have h1 : (0:ℝ) ≤ 2 * R * δ + δ ^ 2 := by positivity
    have h2 : (0:ℝ) < 2 * s := by linarith
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) h2.le
  · rw [gaussianWeightReal, gaussianWeightReal, ← Real.exp_sub]
    refine Real.exp_le_exp.2 ?_
    have h2 : (0:ℝ) < 2 * s := by linarith
    have hny : ‖y‖ ≤ ‖x‖ + δ := by
      have := norm_sub_norm_le y x
      rw [← dist_eq_norm] at this
      linarith
    have hnx : (0:ℝ) ≤ ‖x‖ := norm_nonneg x
    have hny0 : (0:ℝ) ≤ ‖y‖ := norm_nonneg y
    have hsq : ‖y‖ ^ 2 ≤ ‖x‖ ^ 2 + (2 * R * δ + δ ^ 2) := by nlinarith
    rw [div_sub_div_same, div_le_div_iff_of_pos_right h2]
    linarith

/-! ## 2. The one-step law dominates a scaled uniform law on any sub-ball region

This is the analogue of the `hdom` step inside `Arlib.MarkovChains.overlap_speedyWalk_convex`
(`StarPolar.lean:538`) — with the crucial difference that the normaliser is `vol(δBₙ)`, the
volume of the **full** ball, and not `vol(B(x,δ) ∩ K)`.  That is precisely why a local
conductance floor cannot be avoided downstream; see the module docstring. -/

/-- **Domination of the Metropolis one-step law.**  For `‖x‖ ≤ R` and any region `C` inside
the proposal ball `B(x,δ)`,

    a · vol(δBₙ)⁻¹ · vol(A ∩ C ∩ K)  ≤  P_x(A),    a = e^{-(2Rδ+δ²)/(2s)}.

The Dirac (rejection) part of the kernel is simply dropped — it can only help. -/
theorem mul_volume_le_setLIntegral_metropolisDensity {s : ℝ} (hs : 0 < s) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : 0 < δ) {K : Set (EuclideanSpace ℝ (Fin n))}
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ ≤ R)
    {C A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A)
    (hCK : MeasurableSet (C ∩ K)) (hC : C ⊆ Metric.ball x δ) :
    ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s))) * volume (A ∩ (C ∩ K))
      ≤ ∫⁻ y in A ∩ K, metropolisDensity s δ x y := by
  set a : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s))) with hadef
  calc a * volume (A ∩ (C ∩ K))
      = ∫⁻ _ in A ∩ (C ∩ K), a := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ y in A ∩ (C ∩ K), metropolisDensity s δ x y := by
        refine setLIntegral_mono' (hA.inter hCK) fun y hy => ?_
        have hyb : y ∈ Metric.ball x δ := hC hy.2.1
        rw [metropolisDensity, Set.indicator_of_mem hyb]
        exact metropolisAccept_ge hs hR hδ.le hx (le_of_lt (Metric.mem_ball.1 hyb))
    _ ≤ ∫⁻ y in A ∩ K, metropolisDensity s δ x y := by
        refine lintegral_mono' (Measure.restrict_mono ?_ le_rfl) le_rfl
        rintro z ⟨hz1, -, hz3⟩
        exact ⟨hz1, hz3⟩

/-- **Domination of the Metropolis one-step law**, as above. -/
theorem mul_volume_le_metropolisGaussian {s : ℝ} (hs : 0 < s) {R δ : ℝ} (hR : 0 ≤ R)
    (hδ : 0 < δ) {K : Set (EuclideanSpace ℝ (Fin n))}
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ ≤ R)
    {C A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A)
    (hCK : MeasurableSet (C ∩ K)) (hC : C ⊆ Metric.ball x δ) :
    ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s)))
        * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ))⁻¹
        * volume (A ∩ (C ∩ K))
      ≤ metropolisGaussian K δ s x A := by
  set a : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s))) with hadef
  have hkey : a * volume (A ∩ (C ∩ K))
      ≤ ∫⁻ y in A ∩ K, metropolisDensity s δ x y :=
    mul_volume_le_setLIntegral_metropolisDensity hs hR hδ hx hA hCK hC
  rw [metropolisGaussian_apply_set K δ s x hA]
  refine le_trans ?_ le_self_add
  calc a * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ))⁻¹
          * volume (A ∩ (C ∩ K))
      = (volume (Metric.ball x δ))⁻¹ * (a * volume (A ∩ (C ∩ K))) := by
        rw [← volume_ball_eq x δ]; ring
    _ ≤ (volume (Metric.ball x δ))⁻¹ * (∫⁻ y in A ∩ K, metropolisDensity s δ x y) :=
        mul_le_mul' le_rfl hkey

/-! ## 3. `cor:overlap` for the Metropolis kernel, at separation `δ/n`

The geometry is `Arlib.MarkovChains.volume_lens_inter_ge_max` (`StarPolar.lean:239`), used
exactly as in `Arlib.MarkovChains.overlap_speedyWalk_convex`.  What differs is the
normalisation: the speedy walk divides by `vol(B(x,δ) ∩ K)`, which cancels the lens bound's
`max` outright; the Metropolis kernel divides by `vol(δBₙ)`, so the `max` survives as a
factor of `ell` and must be bounded below by hypothesis.  See the module docstring for why
that floor is genuinely necessary and not an artefact of this proof. -/

/-- **`cor:overlap` for `metropolisGaussian`**, on a bounded convex body, at separation
`δ/n`:

    1 ≤ 20·(P_u(Tᶜ) + P_v(T))    whenever u ∈ T ∩ K, v ∈ K \ T, ‖u − v‖ < δ/n,

given a floor `θ` on the local conductance satisfying `1 ≤ 20·a·(1 − 1/n)ⁿ·θ`, where
`a = e^{-(2Rδ+δ²)/(2s)}` is the acceptance floor of `metropolisAccept_ge`.

Three hypotheses here have no counterpart in `Arlib.MarkovChains.overlap_speedyWalk_convex`,
and all three are forced by the kernel, not by the proof:

* `hKR : ∀ x ∈ K, ‖x‖ ≤ R` — **the body must be bounded.**  The acceptance ratio degrades
  with the distance from the origin, so without a radius there is no acceptance floor at all.
* `hs : 0 < s` — the Gaussian is a genuine density.
* `hfloor` — the local-conductance floor.  It is *weaker* than
  `Arlib.MarkovChains.overlap_speedyWalk`'s `11 ≤ 20·ell` by roughly a factor of three: since
  `(1 − 1/n)ⁿ ≥ 1/(e+1)`, at `a ≈ 1` it asks only `θ ≳ (e+1)/20 ≈ 0.19`, where
  `overlap_speedyWalk` asks `θ ≥ 11/20 > 1/2` — a demand no bounded body meets, `ell` being
  about `1/2` at a smooth boundary point.

`u ∈ T`, `v ∉ T` and `d_h(u,v) < 1/4` are not used; they are carried so the statement matches
the binder of `Arlib.MarkovChains.conductance_speedyGaussian_ge`. -/
theorem metropolisGaussian_overlap_of_convex (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    {δ s R θ : ℝ} (hδ : 0 < δ) (hs : 0 < s) (hR : 0 ≤ R)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hell : ∀ x ∈ K, ENNReal.ofReal θ ≤ ell K δ x)
    (hfloor : 1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s)) * (1 - 1 / (n : ℝ)) ^ n * θ)
    (h : EuclideanSpace ℝ (Fin n) → ℝ) :
    ∀ T : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet T →
      ∀ u v : EuclideanSpace ℝ (Fin n), u ∈ T → u ∈ K → v ∈ K → v ∉ T →
      ‖u - v‖ < δ / (n : ℝ) → densDist h u v < 1 / 4 →
      1 ≤ 20 * (metropolisGaussian K δ s u Tᶜ + metropolisGaussian K δ s v T) := by
  intro T hT u v _ huK hvK _ hsep _
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hp0 : (0 : ℝ) < 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith
    linarith
  have hppow : (0 : ℝ) < (1 - 1 / (n : ℝ)) ^ n := pow_pos hp0 n
  have hexp : (0 : ℝ) < Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s)) := Real.exp_pos _
  have hθ0 : (0 : ℝ) ≤ θ := by
    by_contra hc
    push Not at hc
    have hpos : (0:ℝ) < 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s))
        * (1 - 1 / (n : ℝ)) ^ n := by positivity
    linarith [mul_neg_of_pos_of_neg hpos hc]
  set vb : ℝ≥0∞ := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ) with hvbdef
  have hvb0 : vb ≠ 0 := (Metric.measure_ball_pos volume 0 hδ).ne'
  have hvbtop : vb ≠ ⊤ := measure_ball_lt_top.ne
  set C : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball u δ ∩ Metric.ball v δ with hCdef
  have hCK : MeasurableSet (C ∩ K) := (measurableSet_ball.inter measurableSet_ball).inter hK
  set a : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s))) with hadef
  -- the two one-step laws each dominate the lens contribution
  have h1 : a * vb⁻¹ * volume (Tᶜ ∩ (C ∩ K)) ≤ metropolisGaussian K δ s u Tᶜ :=
    mul_volume_le_metropolisGaussian hs hR hδ (hKR u huK) hT.compl hCK Set.inter_subset_left
  have h2 : a * vb⁻¹ * volume (T ∩ (C ∩ K)) ≤ metropolisGaussian K δ s v T :=
    mul_volume_le_metropolisGaussian hs hR hδ (hKR v hvK) hT hCK Set.inter_subset_right
  have h3 : volume (Tᶜ ∩ (C ∩ K)) + volume (T ∩ (C ∩ K)) = volume (C ∩ K) := by
    have hm := measure_inter_add_sdiff (μ := volume) (C ∩ K) hT
    rw [Set.inter_comm (C ∩ K) T, Set.sdiff_eq, Set.inter_comm (C ∩ K) Tᶜ] at hm
    rw [add_comm]; exact hm
  have hsum : a * vb⁻¹ * volume (C ∩ K)
      ≤ metropolisGaussian K δ s u Tᶜ + metropolisGaussian K δ s v T := by
    rw [← h3, mul_add]
    exact add_le_add h1 h2
  -- the lens carries a `(1 − 1/n)ⁿ` fraction of the larger ball-slice, which `ell` floors
  have hlens : ENNReal.ofReal ((1 - 1 / (n : ℝ)) ^ n)
        * max (volume (Metric.ball u δ ∩ K)) (volume (Metric.ball v δ ∩ K))
      ≤ volume (C ∩ K) := volume_lens_inter_ge_max hn hKc huK hvK hδ hsep.le
  have hballu : ENNReal.ofReal θ * vb ≤ volume (Metric.ball u δ ∩ K) := by
    rw [hvbdef, ← ell_mul_volume_ball K hδ u]
    exact mul_le_mul' (hell u huK) le_rfl
  have hCKlb : ENNReal.ofReal ((1 - 1 / (n : ℝ)) ^ n) * (ENNReal.ofReal θ * vb)
      ≤ volume (C ∩ K) :=
    le_trans (mul_le_mul' le_rfl (le_trans hballu (le_max_left _ _))) hlens
  have hcancel : a * vb⁻¹ * (ENNReal.ofReal ((1 - 1 / (n : ℝ)) ^ n) * (ENNReal.ofReal θ * vb))
      = a * ENNReal.ofReal ((1 - 1 / (n : ℝ)) ^ n) * ENNReal.ofReal θ := by
    have hvbc : vb⁻¹ * vb = 1 := ENNReal.inv_mul_cancel hvb0 hvbtop
    calc a * vb⁻¹ * (ENNReal.ofReal ((1 - 1 / (n : ℝ)) ^ n) * (ENNReal.ofReal θ * vb))
        = a * ENNReal.ofReal ((1 - 1 / (n : ℝ)) ^ n) * ENNReal.ofReal θ * (vb⁻¹ * vb) := by
          ring
      _ = _ := by rw [hvbc, mul_one]
  have hkey : a * ENNReal.ofReal ((1 - 1 / (n : ℝ)) ^ n) * ENNReal.ofReal θ
      ≤ metropolisGaussian K δ s u Tᶜ + metropolisGaussian K δ s v T := by
    rw [← hcancel]
    exact le_trans (mul_le_mul' le_rfl hCKlb) hsum
  calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
    _ ≤ ENNReal.ofReal
          (20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s)) * (1 - 1 / (n : ℝ)) ^ n * θ) :=
        ENNReal.ofReal_le_ofReal hfloor
    _ = 20 * (a * ENNReal.ofReal ((1 - 1 / (n : ℝ)) ^ n) * ENNReal.ofReal θ) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 20), hadef,
          show ENNReal.ofReal (20 : ℝ) = (20 : ℝ≥0∞) by simp]
        ring
    _ ≤ 20 * (metropolisGaussian K δ s u Tᶜ + metropolisGaussian K δ s v T) :=
        mul_le_mul' le_rfl hkey

/-! ## 4. The `π ↔ h` bridges

`Arlib.MarkovChains.conductance_speedyGaussian_ge` takes its stationary law in the *density*
form `π(A) = ofReal(∫_A h)/ofReal(∫ h)`, whereas
`Arlib.MarkovChains.isReversible_metropolisGaussian` produces it in the *measure* form
`Arlib.uniformOn (volume.withDensity (gaussianWeight s)) K`.  These lemmas identify the two,
at `h = 1_K · e^{-‖x‖²/(2s)}` — which, at `s = σ²`, is exactly the `h` of
`Arlib.gaussianRestricted_isoperimetry` with the log-concave factor `f = 1_K`. -/

/-- The Gaussian weight is integrable on any set of finite volume — it is continuous and
bounded by `1`. -/
theorem integrableOn_gaussianWeightReal {s : ℝ} (hs : 0 < s)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hAtop : volume A ≠ ⊤) :
    IntegrableOn (gaussianWeightReal s) A volume := by
  refine Measure.integrableOn_of_bounded (M := 1) hAtop
    (continuous_gaussianWeightReal s).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [Real.norm_eq_abs, abs_of_pos (gaussianWeightReal_pos s x)]
  exact gaussianWeightReal_le_one hs x

/-- **The measure form equals the density form.**  For `h = 1_K · g`,

    (volume.withDensity g) (A ∩ K)  =  ofReal (∫_A h). -/
theorem withDensity_gaussianWeight_eq_ofReal_setIntegral {s : ℝ} (hs : 0 < s)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKtop : volume K ≠ ⊤)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) :
    ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight s)) (A ∩ K)
      = ENNReal.ofReal (∫ x in A, Set.indicator K (gaussianWeightReal s) x) := by
  have hAKtop : volume (A ∩ K) ≠ ⊤ :=
    ne_top_of_le_ne_top hKtop (measure_mono Set.inter_subset_right)
  rw [withDensity_apply _ (hA.inter hK), setIntegral_indicator hK,
    ofReal_integral_eq_lintegral_ofReal (integrableOn_gaussianWeightReal hs hAKtop)
      (Filter.Eventually.of_forall fun x => (gaussianWeightReal_pos s x).le)]
  rfl

/-- **`hpi` for the Metropolis-Gaussian chain**, in exactly the form
`Arlib.MarkovChains.conductance_speedyGaussian_ge` consumes. -/
theorem uniformOn_gaussianWeight_eq_div {s : ℝ} (hs : 0 < s)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKtop : volume K ≠ ⊤)
    (A : Set (EuclideanSpace ℝ (Fin n))) (hA : MeasurableSet A) :
    Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight s)) K A
      = ENNReal.ofReal (∫ x in A, Set.indicator K (gaussianWeightReal s) x)
        / ENNReal.ofReal (∫ x, Set.indicator K (gaussianWeightReal s) x) := by
  rw [Arlib.uniformOn_apply _ hK hA,
    withDensity_gaussianWeight_eq_ofReal_setIntegral hs hK hKtop hA]
  congr 1
  have h := withDensity_gaussianWeight_eq_ofReal_setIntegral hs hK hKtop
    (MeasurableSet.univ (α := EuclideanSpace ℝ (Fin n)))
  rwa [Set.univ_inter, setIntegral_univ] at h

/-- **`hmass`**: the unnormalised target has positive total mass as soon as `K` does.  The
quantitative floor is `e^{-R²/(2s)}·vol(K)` — exponentially small, but this is only a
non-degeneracy fact, never a rate. -/
theorem integral_gaussianIndicator_pos {s : ℝ} (hs : 0 < s) {R : ℝ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKtop : volume K ≠ ⊤)
    (hK0 : volume K ≠ 0) (hKR : ∀ x ∈ K, ‖x‖ ≤ R) :
    0 < ∫ x, Set.indicator K (gaussianWeightReal s) x := by
  rw [integral_indicator hK]
  have hint : IntegrableOn (gaussianWeightReal s) K volume :=
    integrableOn_gaussianWeightReal hs hKtop
  have hconst : IntegrableOn (fun _ => Real.exp (-R ^ 2 / (2 * s))) K volume :=
    Measure.integrableOn_of_bounded (M := Real.exp (-R ^ 2 / (2 * s))) hKtop
      aestronglyMeasurable_const
      (Filter.Eventually.of_forall fun _ => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)])
  have hmono : ∫ _ in K, Real.exp (-R ^ 2 / (2 * s))
      ≤ ∫ x in K, gaussianWeightReal s x :=
    setIntegral_mono_on hconst hint hK fun x hx =>
      exp_le_gaussianWeightReal hs (hKR x hx)
  refine lt_of_lt_of_le ?_ hmono
  rw [setIntegral_const, smul_eq_mul]
  exact mul_pos (ENNReal.toReal_pos hK0 hKtop) (Real.exp_pos _)

/-! ## 5. The headline -/

/-- **The sharp conductance bound for the Metropolis-filtered Gaussian ball walk on a
bounded convex body.**

    Φ(metropolisGaussian K δ σ²)  ≥  δ·log 2 / (640·σ·n)

with respect to `π = Arlib.uniformOn (volume.withDensity (gaussianWeight σ²)) K`, which by
`Arlib.MarkovChains.isReversible_metropolisGaussian` is exactly the chain's stationary law.

This is `Arlib.MarkovChains.conductance_speedyGaussian_ge` instantiated at
`P := metropolisGaussian K δ σ²` and at the *theorem*-scale `δ/√n`; every hypothesis of that
theorem except `hiso` is discharged here.

**The cost, stated plainly.**

* **The constant.**  `δ·log 2/(640·σ·n) ≥ δ/(924·σ·n)`.  This is a factor `√n` *worse* than
  `conductance_speedyGaussian_ge`'s own `δ·log 2/(640·σ·√n)`.  The loss is entirely in
  `Arlib.MarkovChains.volume_lens_inter_ge_max`, which holds only at separation `δ/n`; it is
  inherited from `Arlib.MarkovChains.conductance_speedyWalk_ge_of_convex`, which pays the
  same `√n` for the same reason, and is not introduced by the Metropolis filter.
* **The acceptance constant is `a = e^{-(2Rδ+δ²)/(2σ²)}`**, and it does *not* degrade the
  displayed constant at all: it enters only through `hfloor`, i.e. it is charged against the
  local-conductance floor `θ` rather than against `Φ`.  In the Cousins-Vempala regime
  (`R ≍ σ√n`, `δ ≤ σ/(8√n)`) it is `≥ e^{-1/8} ≈ 0.88`, a constant — this is the whole point
  of `metropolisAccept_ge`, and the reason this bound is not exponentially small the way
  `Arlib.MarkovChains.conductance_metropolisGaussian_ge`'s is.
* **`R` enters as a genuine extra hypothesis** (`hKR`), which the ball-walk theorems
  `conductance_speedyGaussian_ge` and `conductance_speedyWalk_ge_of_convex` do **not** need.
  It appears in exactly two places — the acceptance floor `a` and, through it, `hfloor`.  It
  imposes **no** relation between `R`, `σ`, `δ`, `n` beyond what `hfloor` states; in
  particular `hδσ : δ ≤ σ/8` is unchanged from the ball-walk version.
* **`hfloor`/`hell` — the local-conductance floor — is a real restriction on `K`** and is
  *not* removable; see the module docstring for why `hoverlap` is outright false without it.

**`hiso` is a hypothesis.**  It is Cousins-Vempala's `thm:iso`, stated here at `d = δ·log 2/√n`
in the *exact* shape `conductance_speedyGaussian_ge` consumes and
`Arlib.gaussianRestricted_isoperimetry` concludes, with
`h = 1_K · e^{-‖x‖²/(2σ²)}` — i.e. that theorem's `h` at the log-concave factor `f = 1_K`.
It is **not proved in this repository**.  Therefore **this theorem is not a mixing-time bound
and not an `O*(n³)` claim, and may not be quoted as either.** -/
theorem conductance_metropolisGaussian_sharp_ge (hn : 2 ≤ n)
    {σ δ R θ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) (hδσ : δ ≤ σ / 8) (hR : 0 ≤ R)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hKtop : volume K ≠ ⊤) (hK0 : volume K ≠ 0)
    (hell : ∀ x ∈ K, ENNReal.ofReal θ ≤ ell K δ x)
    (hfloor : 1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2))
      * (1 - 1 / (n : ℝ)) ^ n * θ)
    (hiso : ∀ S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n)),
      IsPartition3 Set.univ S₁ S₂ S₃ →
      MeasurableSet S₁ → MeasurableSet S₂ → MeasurableSet S₃ →
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        δ / Real.sqrt n * Real.log 2 / Real.sqrt n / Real.log 2 ≤ ‖u - v‖ ∨
          4 * (δ / Real.sqrt n * Real.log 2 / Real.sqrt n / σ) * Real.sqrt n
            ≤ densDist (Set.indicator K (gaussianWeightReal (σ ^ 2))) u v) →
      δ / Real.sqrt n * Real.log 2 / Real.sqrt n / σ
          * ((∫ x in S₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
            * ∫ x in S₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        ≤ (∫ x, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          * ∫ x in S₃, Set.indicator K (gaussianWeightReal (σ ^ 2)) x) :
    ENNReal.ofReal (δ * Real.log 2 / (640 * σ * (n : ℝ)))
      ≤ conductance (metropolisGaussian K δ (σ ^ 2))
          (Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
            (gaussianWeight (σ ^ 2))) K) := by
  have hs : (0 : ℝ) < σ ^ 2 := by positivity
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hnpos.le
  set h : EuclideanSpace ℝ (Fin n) → ℝ :=
    Set.indicator K (gaussianWeightReal (σ ^ 2)) with hhdef
  have hh0 : ∀ x, 0 ≤ h x :=
    fun x => Set.indicator_nonneg (fun y _ => (gaussianWeightReal_pos _ y).le) x
  have hmass : 0 < ∫ x, h x := integral_gaussianIndicator_pos hs hK hKtop hK0 hKR
  -- `cor:overlap` at the theorem-scale `δ/√n`, whose own separation is `δ/√n/√n = δ/n`
  have hov : ∀ T : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet T →
      ∀ u v : EuclideanSpace ℝ (Fin n), u ∈ T → u ∈ K → v ∈ K → v ∉ T →
      ‖u - v‖ < δ / Real.sqrt n / Real.sqrt n → densDist h u v < 1 / 4 →
      1 ≤ 20 * (metropolisGaussian K δ (σ ^ 2) u Tᶜ + metropolisGaussian K δ (σ ^ 2) v T) := by
    intro T hT u v huT huK hvK hvT hsep hd
    refine metropolisGaussian_overlap_of_convex hn hK hKc hδ hs hR hKR hell hfloor h
      T hT u v huT huK hvK hvT ?_ hd
    rwa [div_div, hsq] at hsep
  have hconst : δ * Real.log 2 / (640 * σ * (n : ℝ))
      = δ / Real.sqrt n * Real.log 2 / (640 * σ * Real.sqrt n) := by
    rw [show δ / Real.sqrt n * Real.log 2 / (640 * σ * Real.sqrt n)
        = δ * Real.log 2 / (640 * σ * (Real.sqrt n * Real.sqrt n)) by field_simp, hsq]
  rw [hconst]
  exact conductance_speedyGaussian_ge hn hσ (by positivity)
    (by rw [div_le_div_iff₀ hspos (by positivity)]; nlinarith [hδσ, hspos])
    hh0 hmass hK (metropolisGaussian K δ (σ ^ 2)) _
    (fun A hA => uniformOn_gaussianWeight_eq_div hs hK hKtop A hA)
    (isReversible_metropolisGaussian hK δ (σ ^ 2)) (Arlib.uniformOn_compl_eq_zero _ hK)
    hov hiso

/-! ## 6. Non-vacuity (`CLAUDE.md` §11) -/

/-- **Non-vacuity: every hypothesis of `conductance_metropolisGaussian_sharp_ge` except
`hiso` is jointly satisfiable at a bounded convex body, the conclusion there is not the
trivial `0 ≤ _`, and `metropolisGaussian_overlap_of_convex` really does fire.**

The witness is `n = 2`, `K = B(0,1/2) ⊆ ℝ²`, `δ = 1`, `R = 1/2`, `σ = 8` (so `s = σ² = 64`
and `δ = 1 = σ/8`, the extreme allowed by `hδσ`), `θ = 1/4`, `T = B(0,1/8)`, `u = 0`,
`v = (1/4,0)` — the same body and pair as
`Arlib.MarkovChains.exists_overlap_speedyWalk_convex_witness`, chosen so that the two
witnesses are directly comparable.  There `ℓ ≡ 1/4` on `K` (because `K ⊆ B(x,1)` for every
`x ∈ K`), which is *below* `Arlib.MarkovChains.overlap_speedyWalk`'s floor `11/20`; the floor
here is met because the acceptance constant is `a = e^{-1/64} ≥ 63/64` and
`20·a·(1−1/2)²·(1/4) = 1.25·a ≥ 1.23 > 1`.

**What this does NOT certify.**  `hiso` is a binder of
`conductance_metropolisGaussian_sharp_ge` and is *not* exhibited here — it is not proved
anywhere in this repository.  So this witness shows the theorem is not vacuous *for reasons
of its discharged hypotheses*; it does **not** show the theorem has an unconditional
instance, and it is **not** evidence for any mixing-time or `O*(n³)` claim. -/
theorem exists_conductance_metropolisGaussian_sharp_witness :
    ∃ (K T : Set (EuclideanSpace ℝ (Fin 2))) (σ δ R θ : ℝ)
      (u v : EuclideanSpace ℝ (Fin 2)),
      0 < σ ∧ 0 < δ ∧ δ ≤ σ / 8 ∧ 0 ≤ R ∧
      MeasurableSet K ∧ Convex ℝ K ∧ (∀ x ∈ K, ‖x‖ ≤ R) ∧
      volume K ≠ ⊤ ∧ volume K ≠ 0 ∧
      (∀ x ∈ K, ENNReal.ofReal θ ≤ ell K δ x) ∧
      1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2))
        * (1 - 1 / ((2 : ℕ) : ℝ)) ^ (2 : ℕ) * θ ∧
      0 < ENNReal.ofReal (δ * Real.log 2 / (640 * σ * ((2 : ℕ) : ℝ))) ∧
      MeasurableSet T ∧ u ∈ T ∧ u ∈ K ∧ v ∈ K ∧ v ∉ T ∧
      ‖u - v‖ < δ / ((2 : ℕ) : ℝ) ∧
      1 ≤ 20 * (metropolisGaussian K δ (σ ^ 2) u Tᶜ
        + metropolisGaussian K δ (σ ^ 2) v T) := by
  classical
  set K : Set (EuclideanSpace ℝ (Fin 2)) := Metric.ball 0 (1 / 2) with hKdef
  set v : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single (0 : Fin 2) (1 / 4 : ℝ) with hvdef
  have hvnorm : ‖v‖ = 1 / 4 := by
    rw [hvdef, PiLp.norm_single, Real.norm_eq_abs]; norm_num
  have hVpos : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume 0 (by norm_num)).ne'
  have hVtop : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hKvol : volume K ≠ 0 := (Metric.measure_ball_pos volume 0 (by norm_num)).ne'
  have hKtop : volume K ≠ ⊤ := measure_ball_lt_top.ne
  have hKc : Convex ℝ K := convex_ball _ _
  have hKR : ∀ x ∈ K, ‖x‖ ≤ 1 / 2 := by
    intro x hx
    rw [hKdef, Metric.mem_ball, dist_eq_norm, sub_zero] at hx
    exact hx.le
  -- `ℓ ≡ 1/4` on `K`, exactly as in `exists_overlap_speedyWalk_convex_witness`
  have hell : ∀ x ∈ K, ell K (1 : ℝ) x = ENNReal.ofReal (1 / 4) := by
    intro x hx
    have hxnorm : ‖x‖ < 1 / 2 := by
      rw [hKdef, Metric.mem_ball, dist_eq_norm, sub_zero] at hx; exact hx
    have hsub : K ⊆ Metric.ball x 1 := by
      intro y hy
      rw [hKdef, Metric.mem_ball, dist_eq_norm, sub_zero] at hy
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le _ _
        _ < 1 := by linarith
    have hball : volume K
        = ENNReal.ofReal (1 / 4) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
      rw [hKdef, Measure.addHaar_ball_of_pos volume 0 (by norm_num : (0:ℝ) < 1 / 2),
        finrank_euclideanSpace_fin]
      norm_num
    rw [ell_apply, Set.inter_eq_self_of_subset_right hsub, hball, volume_ball_eq x 1]
    exact ENNReal.mul_div_cancel_right hVpos hVtop
  -- the acceptance constant at these parameters is `e^{-1/64} ≥ 63/64`
  have hexpge : (63 : ℝ) / 64
      ≤ Real.exp (-(2 * (1 / 2 : ℝ) * 1 + (1 : ℝ) ^ 2) / (2 * (8 : ℝ) ^ 2)) := by
    have h := Real.add_one_le_exp (-(1 : ℝ) / 64)
    have heq : -(2 * (1 / 2 : ℝ) * 1 + (1 : ℝ) ^ 2) / (2 * (8 : ℝ) ^ 2) = -(1 : ℝ) / 64 := by
      norm_num
    rw [heq]; linarith
  have hfloor : 1 ≤ 20 * Real.exp (-(2 * (1 / 2 : ℝ) * 1 + (1 : ℝ) ^ 2) / (2 * (8 : ℝ) ^ 2))
      * (1 - 1 / ((2 : ℕ) : ℝ)) ^ (2 : ℕ) * (1 / 4 : ℝ) := by
    have hcast : (1 - 1 / ((2 : ℕ) : ℝ)) ^ (2 : ℕ) = 1 / 4 := by norm_num
    rw [hcast]; linarith
  have huK : (0 : EuclideanSpace ℝ (Fin 2)) ∈ K := by
    rw [hKdef]; exact Metric.mem_ball_self (by norm_num)
  have hvK : v ∈ K := by
    rw [hKdef, Metric.mem_ball, dist_eq_norm, sub_zero, hvnorm]; norm_num
  have hvT : v ∉ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 8) := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, hvnorm]; norm_num
  have hsep : ‖(0 : EuclideanSpace ℝ (Fin 2)) - v‖ < (1 : ℝ) / ((2 : ℕ) : ℝ) := by
    rw [zero_sub, norm_neg, hvnorm]; norm_num
  have hdens : densDist (fun _ : EuclideanSpace ℝ (Fin 2) => (1 : ℝ)) 0 v < 1 / 4 := by
    simp [densDist]
  refine ⟨K, Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 8), 8, 1, 1 / 2, 1 / 4, 0, v,
    by norm_num, by norm_num, by norm_num, by norm_num, measurableSet_ball, hKc, hKR,
    hKtop, hKvol, fun x hx => (hell x hx).ge, hfloor,
    ENNReal.ofReal_pos.2 (by positivity), measurableSet_ball,
    Metric.mem_ball_self (by norm_num), huK, hvK, hvT, hsep, ?_⟩
  exact metropolisGaussian_overlap_of_convex (n := 2) (by norm_num) measurableSet_ball hKc
    (by norm_num) (by norm_num) (by norm_num) hKR (fun x hx => (hell x hx).ge) hfloor
    (fun _ => 1) (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 8)) measurableSet_ball
    0 v (Metric.mem_ball_self (by norm_num)) huK hvK hvT (by exact_mod_cast hsep) hdens

end Arlib.MarkovChains

/-! ### Axiom audit -/

#print axioms Arlib.MarkovChains.metropolisAccept_ge
#print axioms Arlib.MarkovChains.mul_volume_le_setLIntegral_metropolisDensity
#print axioms Arlib.MarkovChains.mul_volume_le_metropolisGaussian
#print axioms Arlib.MarkovChains.metropolisGaussian_overlap_of_convex
#print axioms Arlib.MarkovChains.integrableOn_gaussianWeightReal
#print axioms Arlib.MarkovChains.withDensity_gaussianWeight_eq_ofReal_setIntegral
#print axioms Arlib.MarkovChains.uniformOn_gaussianWeight_eq_div
#print axioms Arlib.MarkovChains.integral_gaussianIndicator_pos
#print axioms Arlib.MarkovChains.conductance_metropolisGaussian_sharp_ge
#print axioms Arlib.MarkovChains.exists_conductance_metropolisGaussian_sharp_witness
