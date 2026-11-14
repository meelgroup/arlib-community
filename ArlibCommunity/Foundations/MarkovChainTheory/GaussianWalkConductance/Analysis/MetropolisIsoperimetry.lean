/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Analysis.EllGaussianFacts
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Analysis.EllLogConcave
import ArlibCommunity.Foundations.Convex.GaussianIsoperimetry.Analysis.IsoMeasurable
import ArlibCommunity.Foundations.Convex.GaussianIsoperimetry.Analysis.IsoIndicator
import ArlibCommunity.Foundations.Convex.GaussianIsoperimetry.Analysis.IsoWeighted
import ArlibCommunity.Foundations.Convex.GaussianIsoperimetry.Analysis.OneDimSharp
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Analysis.MetropolisOverlapSqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Isoperimetry weighted by the ball walk, and the Metropolis conductance

The Gaussian isoperimetric inequality of Cousins–Vempala instantiated at the density
`1_K · ℓ · e^{−‖x‖²/(2σ²)}`, where `ℓ` is the local conductance of the ball walk, and the
resulting conductance bound for the Metropolis-filtered Gaussian ball walk.  These
applications used to sit in the geometry files whose results they consume; they live here so
that convex geometry does not depend on the Markov chain.
-/

open ArlibCommunity.Foundations.Convex ArlibCommunity.Foundations.MarkovChainTheory

open ArlibCommunity.Foundations.Convex ArlibCommunity.Foundations.MarkovChainTheory

namespace ArlibCommunity.Foundations.MarkovChainTheory

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped ENNReal _root_.Topology

variable {n : ℕ}

/-- **`thm:iso` for the `ℓ`-weighted Gaussian density `1_K·ℓ·e^{−‖x‖²/(2σ²)}`, with
`S₁ S₂ S₃` merely measurable.**

`ArlibCommunity.Foundations.Convex.weightedIndicator_isoperimetry_measurable_logTwo` with `f` pinned to the local
conductance.  `hf0` is `ENNReal.toReal_nonneg`, `hflc` is `ArlibCommunity.Foundations.MarkovChainTheory.isLogConcave_ell_toReal`,
`hfc` is `ArlibCommunity.Foundations.MarkovChainTheory.continuous_ell_toReal`, and `hfB` is `ArlibCommunity.Foundations.MarkovChainTheory.ell_le_one` at `B = 1`.

The two binders that are **not** discharged here are the new ones: `hellKpos` (strict positivity
of `ℓ` on `K`) and `hellLip` (`ℓ` log-Lipschitz on `K` with constant `Lf`), together with the
compatibility `hLσ`.  They are genuinely extra content about `ℓ`, not isoperimetry, and this
file does not prove them for a general convex body — `ArlibCommunity.Foundations.Geometry.ellGaussian_isoperimetry_measurable_logTwo_strict_witness`
exhibits a body on which they hold with `Lf = 0`, so the statement is not vacuous.

**Scope.**  This is an isoperimetric inequality and nothing else.  It is not a conductance
bound, not a mixing bound, and not a runtime claim.  It is also **not** by itself the `hiso`
binder of `ArlibCommunity.Foundations.MarkovChainTheory.conductance_speedyWalk_ge_of_convex`: that binder is for the
density of a measure the *speedy walk* is reversible for, and the only such measures in this
repository are the scalar multiples of `ArlibCommunity.Foundations.MarkovChainTheory.ellMeasure K δ`, whose density is
`1_K·ℓ` with **no** Gaussian factor.  See the module docstring for what a kernel reversible for
`1_K·ℓ·γ` would have to be. -/
theorem ellGaussian_isoperimetry_measurable_logTwo (hn : 2 ≤ n) {σ d δ R Lf : ℝ}
    (hσ : 0 < σ) (hδ : 0 ≤ δ) (hLf : 0 ≤ Lf)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hK0 : volume K ≠ 0)
    (hellKpos : ∀ x ∈ K, 0 < (ell K δ x).toReal)
    (hellLip : ∀ u ∈ K, ∀ v ∈ K,
      (ell K δ u).toReal ≤ (ell K δ v).toReal * Real.exp (Lf * ‖u - v‖))
    (hLσ : Real.sqrt 3 * (σ ^ 2 * Lf + R) ≤ 2 * σ * Real.sqrt n)
    {S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))}
    (hpart : IsPartition3 Set.univ S₁ S₂ S₃)
    (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂) (hS₃ : MeasurableSet S₃)
    (hsep : ∀ u ∈ S₁, ∀ v ∈ S₂,
      d / Real.log 2 ≤ ‖u - v‖ ∨
        4 * (d / σ) * Real.sqrt n
          ≤ densDist (Set.indicator K
              (fun x => (ell K δ x).toReal * gaussianWeightReal (σ ^ 2) x)) u v) :
    d / σ * ((∫ x in S₁,
          Set.indicator K (fun y => (ell K δ y).toReal * gaussianWeightReal (σ ^ 2) y) x)
        * ∫ x in S₂,
          Set.indicator K (fun y => (ell K δ y).toReal * gaussianWeightReal (σ ^ 2) y) x)
      ≤ (∫ x, Set.indicator K
            (fun y => (ell K δ y).toReal * gaussianWeightReal (σ ^ 2) y) x)
        * ∫ x in S₃,
          Set.indicator K (fun y => (ell K δ y).toReal * gaussianWeightReal (σ ^ 2) y) x := by
  have hn0 : n ≠ 0 := by omega
  have hell1 : ∀ x : EuclideanSpace ℝ (Fin n), (ell K δ x).toReal ≤ 1 := by
    intro x
    have := ENNReal.toReal_mono ENNReal.one_ne_top (ell_le_one K δ x)
    simpa using this
  exact weightedIndicator_isoperimetry_measurable_logTwo (B := 1) hn hσ hLf hK hKc hKR hK0
    (fun _ => ENNReal.toReal_nonneg) (isLogConcave_ell_toReal hK hKc δ)
    (continuous_ell_toReal hn0 hδ) hell1 hellKpos hellLip hLσ hpart hS₁ hS₂ hS₃ hsep

/-- **Strict non-vacuity for `ArlibCommunity.Foundations.Geometry.ellGaussian_isoperimetry_measurable_logTwo`.**

The two binders that instantiation does not discharge — `ℓ` strictly positive on `K` and `ℓ`
log-Lipschitz on `K` — are met **with `Lf = 0`** on a body where `ℓ` is *constant*:

  `K = closedBall 0 (1/2)`, `δ = 4`, `σ = 1`, `R = 1/2`, `d = 1/32`.

Since `‖z‖, ‖x‖ ≤ 1/2` gives `dist z x ≤ 1 < 4`, the whole body lies in every proposal ball
centred in it, so `B(x,4) ∩ K = K` and `ℓ(x) = vol K / vol(4Bₙ)` for every `x ∈ K` — a positive
constant.  `hLσ` therefore reduces to the indicator theorem's `√3·R ≤ 2σ√n`, i.e. `√3/2 ≤ 2√n`.
The separation fires on the metric branch and the left-hand side is strictly positive, so the
conclusion is not `0 ≤ something`. -/
theorem ellGaussian_isoperimetry_measurable_logTwo_strict_witness (hn : 2 ≤ n) :
    ∃ (K S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))) (σ d δ R Lf : ℝ),
      0 < σ ∧ 0 < d ∧ 0 ≤ δ ∧ 0 ≤ Lf ∧
      MeasurableSet K ∧ Convex ℝ K ∧ (∀ x ∈ K, ‖x‖ ≤ R) ∧ volume K ≠ 0 ∧
      (∀ x ∈ K, 0 < (ell K δ x).toReal) ∧
      (∀ u ∈ K, ∀ v ∈ K,
        (ell K δ u).toReal ≤ (ell K δ v).toReal * Real.exp (Lf * ‖u - v‖)) ∧
      Real.sqrt 3 * (σ ^ 2 * Lf + R) ≤ 2 * σ * Real.sqrt n ∧
      IsPartition3 Set.univ S₁ S₂ S₃ ∧
      MeasurableSet S₁ ∧ MeasurableSet S₂ ∧ MeasurableSet S₃ ∧
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        d / Real.log 2 ≤ ‖u - v‖ ∨
          4 * (d / σ) * Real.sqrt n
            ≤ densDist (Set.indicator K
                (fun x => (ell K δ x).toReal * gaussianWeightReal (σ ^ 2) x)) u v) ∧
      (S₁ ∩ K).Nonempty ∧ (S₂ ∩ K).Nonempty ∧
      0 < d / σ * ((∫ x in S₁, Set.indicator K
              (fun y => (ell K δ y).toReal * gaussianWeightReal (σ ^ 2) y) x)
        * ∫ x in S₂, Set.indicator K
              (fun y => (ell K δ y).toReal * gaussianWeightReal (σ ^ 2) y) x) := by
  classical
  set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ) with hedef
  have he : ‖e‖ = 1 := by rw [hedef, PiLp.norm_single]; norm_num
  have hee : (inner ℝ e e : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  set K : Set (EuclideanSpace ℝ (Fin n)) := Metric.closedBall 0 (1 / 2) with hKdef
  have hKmem : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 / 2 → x ∈ K := by
    intro x hx
    rw [hKdef, Metric.mem_closedBall, dist_zero_right]
    exact hx
  have hKmeas : MeasurableSet K := measurableSet_closedBall
  have hKconv : Convex ℝ K := convex_closedBall _ _
  have hKR : ∀ x ∈ K, ‖x‖ ≤ (1 / 2 : ℝ) := by
    intro x hx
    rw [hKdef, Metric.mem_closedBall, dist_zero_right] at hx
    exact hx
  have hK0 : volume K ≠ 0 := by
    have : 0 < volume K :=
      lt_of_lt_of_le (Metric.measure_ball_pos volume 0 (by norm_num : (0:ℝ) < 1/2))
        (measure_mono Metric.ball_subset_closedBall)
    exact this.ne'
  have hKtop : volume K ≠ ⊤ := measure_closedBall_lt_top.ne
  -- the whole body sits inside every proposal ball centred in it
  have hsub : ∀ x ∈ K, K ⊆ Metric.ball x (4 : ℝ) := by
    intro x hx z hz
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 := hKR x hx
    have h2 := hKR z hz
    have := norm_sub_le z x
    linarith
  -- so `ℓ` is the constant `vol K / vol(4Bₙ)` on `K`
  have hellval : ∀ x ∈ K, ell K (4 : ℝ) x
      = volume K / volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 4) := by
    intro x hx
    rw [ell_apply, Set.inter_eq_self_of_subset_right (hsub x hx), volume_ball_eq]
  have hellpos : ∀ x ∈ K, 0 < (ell K (4:ℝ) x).toReal := by
    intro x hx
    refine ENNReal.toReal_pos ?_
      (ne_top_of_le_ne_top ENNReal.one_ne_top (ell_le_one K (4:ℝ) x))
    rw [hellval x hx]
    exact ENNReal.div_ne_zero.2 ⟨hK0, measure_ball_lt_top.ne⟩
  have hellLip : ∀ u ∈ K, ∀ v ∈ K,
      (ell K (4:ℝ) u).toReal ≤ (ell K (4:ℝ) v).toReal * Real.exp ((0:ℝ) * ‖u - v‖) := by
    intro u hu v hv
    rw [hellval u hu, hellval v hv, zero_mul, Real.exp_zero, mul_one]
  -- the density
  have hgpos : ∀ x : EuclideanSpace ℝ (Fin n), 0 < gaussianWeightReal ((1:ℝ) ^ 2) x :=
    fun x => gaussianWeightReal_pos _ x
  have hgi : Integrable
      (fun x : EuclideanSpace ℝ (Fin n) => gaussianWeightReal ((1:ℝ) ^ 2) x) :=
    integrable_gaussianWeightReal one_pos
  have hell1 : ∀ x : EuclideanSpace ℝ (Fin n), (ell K (4:ℝ) x).toReal ≤ 1 := by
    intro x
    have := ENNReal.toReal_mono ENNReal.one_ne_top (ell_le_one K (4:ℝ) x)
    simpa using this
  have hellc : Continuous fun x : EuclideanSpace ℝ (Fin n) => (ell K (4:ℝ) x).toReal :=
    continuous_ell_toReal (by omega) (by norm_num)
  have hfgi : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      (ell K (4:ℝ) x).toReal * gaussianWeightReal ((1:ℝ) ^ 2) x) := by
    refine hgi.mono' ((hellc.mul (continuous_gaussianWeightReal _)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg (hgpos x).le)]
    exact mul_le_of_le_one_left (hgpos x).le (hell1 x)
  have hhi : Integrable (Set.indicator K
      (fun y => (ell K (4:ℝ) y).toReal * gaussianWeightReal ((1:ℝ) ^ 2) y)) :=
    hfgi.indicator hKmeas
  have hh0 : ∀ x, 0 ≤ Set.indicator K
      (fun y => (ell K (4:ℝ) y).toReal * gaussianWeightReal ((1:ℝ) ^ 2) y) x :=
    fun x => Set.indicator_nonneg
      (fun y _ => mul_nonneg ENNReal.toReal_nonneg (hgpos y).le) x
  -- the constant lower bound on the half-radius ball
  set c₀ : ℝ := (ell K (4:ℝ) 0).toReal with hc₀def
  have h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K := hKmem 0 (by simp)
  have hc₀ : 0 < c₀ := hellpos 0 h0K
  have hlow : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 / 2 →
      c₀ * Real.exp (-(1:ℝ) / 2)
        ≤ Set.indicator K
            (fun y => (ell K (4:ℝ) y).toReal * gaussianWeightReal ((1:ℝ) ^ 2) y) x := by
    intro x hx
    have hxK : x ∈ K := hKmem x hx
    rw [Set.indicator_of_mem hxK _]
    have h1 : (ell K (4:ℝ) x).toReal = c₀ := by
      rw [hc₀def, hellval x hxK, hellval 0 h0K]
    have h2 : Real.exp (-(1:ℝ) / 2) ≤ gaussianWeightReal ((1:ℝ) ^ 2) x := by
      rw [gaussianWeightReal]
      refine Real.exp_le_exp.mpr ?_
      have hx2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
      have h2' : (2:ℝ) * (1:ℝ) ^ 2 = 2 := by norm_num
      rw [h2']
      linarith
    rw [h1]
    exact mul_le_mul_of_nonneg_left h2 hc₀.le
  obtain ⟨hp1, hp2⟩ := slab_setIntegral_pos hhi hh0
    (mul_pos hc₀ (Real.exp_pos _)) hlow he
  have hmec : Continuous fun x : EuclideanSpace ℝ (Fin n) => (inner ℝ e x : ℝ) :=
    continuous_const.inner continuous_id
  have hS1meas : MeasurableSet
      {x : EuclideanSpace ℝ (Fin n) | (inner ℝ e x : ℝ) < -(1 / 8 : ℝ)} :=
    (isOpen_lt hmec continuous_const).measurableSet
  have hS2meas : MeasurableSet
      {x : EuclideanSpace ℝ (Fin n) | (1 / 8 : ℝ) < (inner ℝ e x : ℝ)} :=
    (isOpen_lt continuous_const hmec).measurableSet
  have hS3meas : MeasurableSet
      {x : EuclideanSpace ℝ (Fin n) |
        -(1 / 8 : ℝ) ≤ (inner ℝ e x : ℝ) ∧ (inner ℝ e x : ℝ) ≤ 1 / 8} :=
    ((isClosed_le continuous_const hmec).inter (isClosed_le hmec continuous_const)).measurableSet
  have hnrmp : ‖(-(1 / 4 : ℝ)) • e‖ = 1 / 4 := by
    rw [norm_smul, Real.norm_eq_abs, he, mul_one, abs_neg,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 4)]
  have hnrmq : ‖((1 / 4 : ℝ)) • e‖ = 1 / 4 := by
    rw [norm_smul, Real.norm_eq_abs, he, mul_one,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 4)]
  refine ⟨K, {x | (inner ℝ e x : ℝ) < -(1 / 8 : ℝ)}, {x | (1 / 8 : ℝ) < (inner ℝ e x : ℝ)},
    {x | -(1 / 8 : ℝ) ≤ (inner ℝ e x : ℝ) ∧ (inner ℝ e x : ℝ) ≤ 1 / 8},
    1, 1 / 32, 4, 1 / 2, 0,
    one_pos, by norm_num, by norm_num, le_rfl, hKmeas, hKconv, hKR, hK0,
    hellpos, hellLip, ?_,
    isPartition3_slab e (by norm_num : (0:ℝ) ≤ 1 / 8),
    hS1meas, hS2meas, hS3meas,
    ?_, ?_, ?_, ?_⟩
  · -- `hLσ` at `Lf = 0`: `√3·(1/2) ≤ 2√n`
    have hs3 : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]
    have hsn : (1 : ℝ) ≤ Real.sqrt n := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by
        have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt h1
    nlinarith
  · intro u hu v hv
    left
    have hgeo := two_mul_le_norm_sub_of_inner_lt (e := e) he (c := (1 / 8 : ℝ)) hu hv
    have := thirtysecond_div_logTwo_le
    linarith
  · exact ⟨(-(1 / 4 : ℝ)) • e, by
      simp only [Set.mem_setOf_eq, real_inner_smul_right, hee, mul_one]; norm_num,
      hKmem _ (by rw [hnrmp]; norm_num)⟩
  · exact ⟨((1 / 4 : ℝ)) • e, by
      simp only [Set.mem_setOf_eq, real_inner_smul_right, hee, mul_one]; norm_num,
      hKmem _ (by rw [hnrmq]; norm_num)⟩
  · have h1 : (0:ℝ) < (1 / 32 : ℝ) / 1 := by norm_num
    exact mul_pos h1 (mul_pos hp1 hp2)

/-- **Cousins–Vempala's `thm:iso` for measurable `S₁, S₂, S₃`, at the indicator density
`h = 1_K·ℓ·γ`** — the density `ArlibCommunity.Foundations.MarkovChainTheory.conductance_speedyGaussian_ge` consumes.

Compare `ArlibCommunity.Foundations.Geometry.ellGaussian_isoperimetry_measurable_logTwo`
(`ArlibCommunity/Foundations/Convex/GaussianIsoperimetry/Analysis/IsoWeighted.lean`), which reaches the measurable case by converting the
density branch of the separation disjunction into the metric branch and therefore carries

    hellLip : ∀ u ∈ K, ∀ v ∈ K, ℓ(u) ≤ ℓ(v)·exp(Lf·‖u − v‖)
    hLσ     : √3·(σ²·Lf + R) ≤ 2σ√n

for which `AUDIT.md` §0i(b) argues there is no witness with non-constant `ℓ` at the operative
step `δ ≤ σ/(8√n)`.  **Both are gone here, along with the parameters `R` and `Lf`.**

See the module docstring for why the mollification limit closes without any comparison
between `densDist (g j)` and `densDist h`. -/
theorem ellGaussianIndicator_isoperimetry_measurable_logTwo (hn : 2 ≤ n) {σ d δ : ℝ}
    (hσ : 0 < σ) (hd : 0 < d) (hδ : 0 < δ)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hK0 : volume K ≠ 0)
    {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hh : ∀ x, h x = Set.indicator K
      (fun y => (ell K δ y).toReal * Real.exp (-‖y‖ ^ 2 / (2 * σ ^ 2))) x)
    {S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))}
    (hpart : IsPartition3 Set.univ S₁ S₂ S₃)
    (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂) (hS₃ : MeasurableSet S₃)
    (hsep : ∀ u ∈ S₁, ∀ v ∈ S₂,
      d / Real.log 2 ≤ ‖u - v‖ ∨ 4 * (d / σ) * Real.sqrt n ≤ densDist h u v) :
    d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x) ≤ (∫ x, h x) * ∫ x in S₃, h x := by
  classical
  have hn0 : n ≠ 0 := by omega
  have hKne : K.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hc
    exact hK0 (by rw [hc]; exact measure_empty)
  -- the mollified family
  set g : ℕ → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun j x => Real.exp (-(j : ℝ) * Metric.infDist x (closure K)) * (ell K δ x).toReal
      * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) with hgdef
  have hg : ∀ (j : ℕ) (x : EuclideanSpace ℝ (Fin n)), g j x =
      Real.exp (-(j : ℝ) * Metric.infDist x (closure K)) * (ell K δ x).toReal
        * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) := fun _ _ => rfl
  -- on `K` the mollified density, the continuous one and the indicator one all agree
  have hgK : ∀ (j : ℕ), ∀ x ∈ K,
      g j x = (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) := by
    intro j x hx
    have hz : Metric.infDist x (closure K) = 0 :=
      Metric.infDist_zero_of_mem (subset_closure hx)
    rw [hg, hz, mul_zero, Real.exp_zero, one_mul]
  have hhK : ∀ x ∈ K, h x = (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) :=
    fun x hx => by rw [hh, Set.indicator_of_mem hx]
  -- the parts, cut to `K`
  set S₁' : Set (EuclideanSpace ℝ (Fin n)) := S₁ ∩ K with hS₁'def
  set S₂' : Set (EuclideanSpace ℝ (Fin n)) := S₂ ∩ K with hS₂'def
  have hS₁'m : MeasurableSet S₁' := hS₁.inter hK
  have hS₂'m : MeasurableSet S₂' := hS₂.inter hK
  have hS₃'m : MeasurableSet (S₁' ∪ S₂')ᶜ := (hS₁'m.union hS₂'m).compl
  have hpart' : IsPartition3 Set.univ S₁' S₂' (S₁' ∪ S₂')ᶜ :=
    { union := Set.union_compl_self _
      disjoint₁₂ := hpart.disjoint₁₂.mono Set.inter_subset_left Set.inter_subset_left
      disjoint₁₃ := Set.disjoint_left.mpr fun a ha hc => hc (Or.inl ha)
      disjoint₂₃ := Set.disjoint_left.mpr fun a ha hc => hc (Or.inr ha) }
  -- the residual, intersected with `K`, is exactly `S₃ ∩ K`
  have hres : (S₁' ∪ S₂')ᶜ ∩ K = S₃ ∩ K := by
    ext x
    constructor
    · rintro ⟨hx, hxK⟩
      refine ⟨?_, hxK⟩
      have hx1 : x ∉ S₁ := fun hc => hx (Or.inl ⟨hc, hxK⟩)
      have hx2 : x ∉ S₂ := fun hc => hx (Or.inr ⟨hc, hxK⟩)
      have hcover : x ∈ S₁ ∪ S₂ ∪ S₃ := by rw [hpart.union]; exact Set.mem_univ x
      rcases hcover with (h1 | h2) | h3
      · exact absurd h1 hx1
      · exact absurd h2 hx2
      · exact h3
    · rintro ⟨hx3, hxK⟩
      refine ⟨?_, hxK⟩
      rintro (⟨hc, -⟩ | ⟨hc, -⟩)
      · exact (Set.disjoint_left.mp hpart.disjoint₁₃ hc) hx3
      · exact (Set.disjoint_left.mp hpart.disjoint₂₃ hc) hx3
  -- the capstone, at each `j`
  have hmain : ∀ j : ℕ, d / σ * ((∫ x in S₁', g j x) * ∫ x in S₂', g j x)
      ≤ (∫ x, g j x) * ∫ x in (S₁' ∪ S₂')ᶜ, g j x := by
    intro j
    refine gaussianRestricted_isoperimetry_measurable_logTwo hn hσ hd
      (f := fun x => Real.exp (-(j : ℝ) * Metric.infDist x (closure K)) * (ell K δ x).toReal)
      (fun x => mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg)
      (isLogConcave_expNegInfDist_mul_ell hK hKc hKb hKne δ j)
      (fun x => by rw [hg]) (hMoll_continuous hn0 hδ.le hg j) (hMoll_le_one hg j)
      (hMoll_integrable hn0 hδ.le hσ hg j) hpart' hS₁'m hS₂'m hS₃'m
      (hMoll_integral_pos hn0 hδ hσ hKc hKb hK0 hg j) ?_
    -- the separation, transferred verbatim because `g j = h` on `K`
    intro u hu v hv
    have hdd : densDist (g j) u v = densDist h u v := by
      rw [densDist, densDist, hgK j u hu.2, hgK j v hv.2, hhK u hu.2, hhK v hv.2]
    rw [hdd]
    exact hsep u hu.1 v hv.1
  -- the indicator density, read as an integral over `A ∩ K` of the continuous one
  have hHdK : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      (∫ x in A ∩ K, (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))
        = ∫ x in A, h x := by
    intro A _
    simp only [hh]
    exact (setIntegral_eq_setIntegral_indicator (σ := σ) hK A).symm
  -- the two integrals that do not move
  have hfix : ∀ (j : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))), MeasurableSet A →
      (∫ x in A ∩ K, g j x) = ∫ x in A, h x := by
    intro j A hA
    rw [setIntegral_congr_fun (hA.inter hK) (fun x hx => hgK j x hx.2)]
    exact hHdK A hA
  -- the limits
  have hlim_mass : Tendsto (fun j : ℕ => ∫ x, g j x) atTop (𝓝 (∫ x, h x)) := by
    have h1 := tendsto_integral_hMoll hn0 hδ.le hσ hKne hg
    have h2 : (∫ x in closure K, (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))
        = ∫ x, h x := by
      calc (∫ x in closure K, (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))
          = ∫ x in Set.univ ∩ closure K,
              (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) := by
            rw [Set.univ_inter]
        _ = ∫ x in Set.univ ∩ K, (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) :=
            setIntegral_closure_eq_setIntegral (δ := δ) (σ := σ) hK hKc Set.univ
        _ = ∫ x in Set.univ, h x := hHdK Set.univ MeasurableSet.univ
        _ = ∫ x, h x := setIntegral_univ
    rwa [h2] at h1
  have hlim_res : Tendsto (fun j : ℕ => ∫ x in (S₁' ∪ S₂')ᶜ, g j x) atTop
      (𝓝 (∫ x in S₃, h x)) := by
    have h1 := tendsto_setIntegral_hMoll hn0 hδ.le hσ hKne hg (S₁' ∪ S₂')ᶜ
    have h2 : (∫ x in (S₁' ∪ S₂')ᶜ ∩ closure K,
        (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) = ∫ x in S₃, h x := by
      calc (∫ x in (S₁' ∪ S₂')ᶜ ∩ closure K,
            (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))
          = ∫ x in (S₁' ∪ S₂')ᶜ ∩ K,
              (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) :=
            setIntegral_closure_eq_setIntegral (δ := δ) (σ := σ) hK hKc _
        _ = ∫ x in S₃ ∩ K, (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) := by
            rw [hres]
        _ = ∫ x in S₃, h x := hHdK S₃ hS₃
    rwa [h2] at h1
  -- pass to the limit; the left-hand side never moved
  have hLHS : ∀ j : ℕ, d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x)
      ≤ (∫ x, g j x) * ∫ x in (S₁' ∪ S₂')ᶜ, g j x := by
    intro j
    have := hmain j
    rwa [hS₁'def, hS₂'def, hfix j S₁ hS₁, hfix j S₂ hS₂] at this
  exact ge_of_tendsto (hlim_mass.mul hlim_res) (Eventually.of_forall hLHS)

/-- **`thm:iso` for measurable `S₁, S₂, S₃`, at the `ℓ`-weighted Gaussian density
`h = ℓ·γ` — with no Lipschitz hypothesis.**

This is `ArlibCommunity.Foundations.MarkovChainTheory.ellGaussian_isoperimetry_openClosed_logTwo`
(`ArlibCommunity/Foundations/MarkovChainTheory/GaussianWalkConductance/Analysis/EllLogConcave.lean`) with `IsOpen S₁`, `IsOpen S₂`, `IsClosed S₃`
replaced by `MeasurableSet`.

Compare `ArlibCommunity.Foundations.Geometry.ellGaussian_isoperimetry_measurable_logTwo`
(`ArlibCommunity/Foundations/Convex/GaussianIsoperimetry/Analysis/IsoWeighted.lean`), which reaches the measurable case through the
metric-enlargement detour and therefore carries

    hellLip : ∀ u ∈ K, ∀ v ∈ K, ℓ(u) ≤ ℓ(v)·exp(Lf·‖u − v‖)
    hLσ     : √3·(σ²·Lf + R) ≤ 2σ√n

which `AUDIT.md` §0i(b) argues admit no witness with non-constant `ℓ` at the operative step.
**Both are gone here**, together with `R` and `Lf` themselves.  The log-concavity of `ℓ`
(`ArlibCommunity.Foundations.MarkovChainTheory.isLogConcave_ell_toReal`) does all the work that log-Lipschitzness was being asked
for, because the route never converts the density branch into the metric branch.

⚠ **This is still not the consumer's density.**  `hiso` in
`ArlibCommunity.Foundations.MarkovChainTheory.conductance_speedyGaussian_ge` is pinned by
`ArlibCommunity.Foundations.MarkovChainTheory.hpi_ellGaussian` to the **indicator** density `1_K·ℓ·γ`, which is
discontinuous across `∂K` and so fails `hhc`.  Bridging to it needs the mollification
argument that `ArlibCommunity.Foundations.Convex.gaussianIndicator_isoperimetry_measurable`
(`ArlibCommunity/Foundations/Convex/GaussianIsoperimetry/Analysis/IsoIndicator.lean`) performs for `1_K·γ`, carried out with the extra
factor `ℓ`.  Until that lands, nothing here may be quoted as a conductance, mixing-time or
runtime bound.  See `AUDIT.md` §0j. -/
theorem ellGaussian_isoperimetry_measurable_logTwo_uncond (hn : 2 ≤ n) {σ d δ : ℝ}
    (hσ : 0 < σ) (hd : 0 < d) (hδ : 0 < δ)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hK0 : volume K ≠ 0)
    {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hh : ∀ x, h x = (ArlibCommunity.Foundations.MarkovChainTheory.ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))
    {S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))}
    (hpart : IsPartition3 Set.univ S₁ S₂ S₃)
    (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂) (hS₃ : MeasurableSet S₃)
    (hsep : ∀ u ∈ S₁, ∀ v ∈ S₂,
      d / Real.log 2 ≤ ‖u - v‖ ∨ 4 * (d / σ) * Real.sqrt n ≤ densDist h u v) :
    d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x) ≤ (∫ x, h x) * ∫ x in S₃, h x :=
  gaussianRestricted_isoperimetry_measurable_logTwo hn hσ hd
    (fun _ => ENNReal.toReal_nonneg) (isLogConcave_ell_toReal hK hKc δ) hh
    (ellGaussian_continuous (by omega) hδ.le hh)
    (ellGaussian_le_one hh)
    (ellGaussian_integrable (by omega) hδ.le hσ hh)
    hpart hS₁ hS₂ hS₃
    (ellGaussian_integral_pos (by omega) hδ hσ hKc hKb hK0 hh)
    hsep

/-- **`ArlibCommunity.Foundations.MarkovChainTheory.conductance_metropolisGaussian_sharp_sqrt_ge` with `hiso` discharged.**

The only hypothesis of that theorem that this repository could not previously supply was `hiso`
— Cousins–Vempala's `thm:iso` at `d = δ·log 2/√n`, whose metric branch is stated at the
threshold `d / log 2`.  `ArlibCommunity.Foundations.Convex.hiso_metropolisGaussian_sharp_sqrt_logTwo` now proves exactly
that binder, so the conductance bound holds outright, with `hRσ : √3·R ≤ 2σ√n` (a bounding
radius compatible with the Gaussian scale) as the only added hypothesis.

The docstring of `conductance_metropolisGaussian_sharp_sqrt_ge` says of `hiso`: "It is **not
proved in this repository**.  Therefore **this theorem is not a mixing-time bound...**".  With
this corollary that caveat no longer applies to the conductance statement itself. -/
theorem conductance_metropolisGaussian_sharp_sqrt_ge_of_convex (hn : 2 ≤ n)
    {σ δ R θ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) (hδσ : δ ≤ σ / (8 * Real.sqrt n)) (hR : 0 ≤ R)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hKtop : volume K ≠ ⊤) (hK0 : volume K ≠ 0)
    (hell : ∀ x ∈ K, ENNReal.ofReal θ ≤ ArlibCommunity.Foundations.MarkovChainTheory.ell K δ x)
    (hfloor : 1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) * (1 / 4) * θ)
    (hRσ : Real.sqrt 3 * R ≤ 2 * σ * Real.sqrt n) :
    ENNReal.ofReal (δ * Real.log 2 / (640 * σ * Real.sqrt n))
      ≤ ArlibCommunity.Foundations.MarkovChainTheory.conductance (ArlibCommunity.Foundations.MarkovChainTheory.metropolisGaussian K δ (σ ^ 2))
          (ArlibCommunity.Foundations.Convex.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
            (gaussianWeight (σ ^ 2))) K) :=
  ArlibCommunity.Foundations.MarkovChainTheory.conductance_metropolisGaussian_sharp_sqrt_ge hn hσ hδ hδσ hR hK hKc hKR
    hKtop hK0 hell hfloor
    (hiso_metropolisGaussian_sharp_sqrt_logTwo hn hσ hK hKc hKR hKtop hK0 hRσ)

end ArlibCommunity.Foundations.MarkovChainTheory
