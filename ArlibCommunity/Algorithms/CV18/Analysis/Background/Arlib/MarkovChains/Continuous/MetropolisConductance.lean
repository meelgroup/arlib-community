/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.MetropolisGaussian
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.ConvexBodyMixing
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.Convexity.GaussianCooling.Unblock

/-!
# Conductance and mixing of the Metropolis-filtered ball walk for the Gaussian density

`Arlib/MarkovChains/Continuous/MetropolisGaussian.lean` builds the Cousins-Vempala chain
`metropolisGaussian K δ s` — propose uniformly in `x + δBₙ`, accept with probability
`1_K(y)·min(1, g(y)/g(x))` for `g(x) = e^{-‖x‖²/(2s)}` — and proves it is a Markov kernel
reversible for `Arlib.uniformOn (volume.withDensity g) K`.  It supplies **no** conductance
bound.  This file supplies one, and the mixing time that follows from it.

It is the weighted analogue of `Arlib/MarkovChains/Continuous/BallWalkConductance.lean`,
and it reuses that file wholesale wherever the argument is not about the density: the
ball-intersection geometry (`volume_ball_le_volume_inter_ball_add`), the three-way flow
partition (`mul_measure_add_measure_le_mul_flow`, which is stated for an arbitrary
reversible Markov kernel on an arbitrary measurable space), the laziness bridge (`lazy`,
`isReversible_lazy`, `hasNonnegSpectrum_lazy`, `conductance_lazy`), and the non-degeneracy
lemmas.  What had to be redone is exactly the two steps that see the density.

## The two steps that are new

1. **The one-step overlap estimate for a non-uniform density**
   (`mul_ell_le_metropolisGaussian_add_metropolisGaussian_compl`).  The uniform bound
   `ℓ(u) ≤ P_u(T) + P_v(Tᶜ) + n‖u-v‖/(2δ)` is false here, because a Metropolis step from `u`
   does not distribute its mass uniformly over `B(u,δ) ∩ K`.  What replaces it is

       α·ℓ(u)  ≤  P_u(T) + P_v(Tᶜ) + n‖u-v‖/(2δ),

   where `α` is any **acceptance floor**: a bound `α ≤ g(y)` valid throughout `K`.  The
   point is `le_metropolisAccept`: since `g ≤ 1` everywhere (this is where `0 < s` enters),
   `min(1, g(y)/g(x)) ≥ min(1, g(y)) ≥ α` for *every* `x`, with no constraint on `x` at all.
   So the loss is a single factor `α = m/M` — one power of the density-sandwich ratio, not
   two.

2. **A weighted local-conductance floor.**  In the form above the local conductance that
   appears is still the *unweighted* `Arlib.MarkovChains.ell`, so
   `Arlib.MarkovChains.le_ell_of_convex_of_ball_subset` (`ConvexBodyMixing.lean`) applies
   verbatim and the weighted floor is `α·θ` with `θ = (γ/(γ+D))ⁿ`.  That is the whole
   content of the second step: the density is absorbed into `α`, not into `ℓ`.

## The isoperimetric input

`Arlib.Convexity.uniformOn_gaussian_iso_kappa` and
`Arlib.Convexity.exists_uniformOn_gaussian_iso_of_convex`
(`Arlib/Convexity/GaussianCooling/Unblock.lean`) prove the three-set isoperimetric
inequality for `Arlib.uniformOn (volume.withDensity g) K` — the *same* measure that is
stationary for `metropolisGaussian K δ s` — in exactly the shape
`conductance_metropolisGaussian_ge` consumes.  The density sandwich `m ≤ g ≤ M` those
theorems use is available at precisely the parameters needed here: `M = 1` from
`gaussianWeight_le_one` and `m = e^{-R²/(2s)}` from `exp_le_gaussianWeightReal`, with the
radius `R` manufactured from convexity by
`Arlib.Convexity.exists_closedBall_superset_of_convex`.  The acceptance floor `α` of step 1
is the *same* `m/M`.  So the convex-body theorems below assume **nothing**.

## Main results

* `le_metropolisAccept`, `ofReal_exp_le_gaussianWeight` — the acceptance floor.
* `mul_ell_le_metropolisGaussian_add_metropolisGaussian_compl` — the one-step overlap.
* `lt_dist_of_metropolisGaussian_lt` — the separation it forces.
* `conductance_metropolisGaussian_ge` — **the conductance bound**, with the isoperimetric
  inequality and the local-conductance floor written out inline as `∀`-hypotheses.
* `exists_smallSet_uniformOn_gaussian` — non-degeneracy of the weighted target.
* `mixesWithin_lazy_metropolisGaussian` — the mixing time.
* `conductance_metropolisGaussian_convex`, `mixesWithin_lazy_metropolisGaussian_convex`,
  `exists_conductance_metropolisGaussian_pos`,
  `exists_mixesWithin_lazy_metropolisGaussian_convex` — the unconditional convex-body
  instances, with every hypothesis discharged.

## The constant is exponentially small, and this is not a polynomial-time result

The conductance proved for a convex `K ⊆ R·Bₙ` with an inscribed ball `B(c,γ)` is

    Φ  ≥  min( α·θ/16 ,  κ·(α·θ)²·δ/(64·n) ),
    α = e^{-R²/(2s)},   θ = (γ/(γ+2R))ⁿ,   κ = e^{-R²/s}·2⁻ⁿ/(2R).

Every one of `α`, `θ`, `κ` is exponentially small in `n` for the Cousins-Vempala parameters
(`R ≍ √n`, `s` as small as `Θ(1/n)` makes `α = e^{-Θ(n²)}`), and in
`exists_conductance_metropolisGaussian_pos` the radius `R` itself is only bounded by
`2·vol K/vol B(0,1/2)`, which is exponential in `n`.  **So the conductance here is
exponentially small in `n` and the mixing time exponentially large; nothing below is a
polynomial-time statement and none of it may be quoted as one.**  The obstruction is
inherited, not introduced: `Arlib/Convexity/GaussianCooling/Unblock.lean:591-596` records
that its isoperimetric constant is not polynomial, and
`Arlib/MarkovChains/Continuous/BallWalkConductance.lean` records the further `√n` loss in
the ball-intersection geometry.  The sharp isoperimetric constant needs localization, which
this development does not have.

## What is assumed

Nothing that is not written inline.  There is **no** `def`, `structure`, `class` or named
`Prop` in this file — every declaration is a `theorem`.  The two hypotheses with content in
`conductance_metropolisGaussian_ge` (the isoperimetric inequality `hiso` and the
local-conductance floor `hell`) appear in full in its type, and both are *discharged* in
`conductance_metropolisGaussian_convex`, which therefore assumes only geometry.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

variable {n : ℕ}

/-! ## 1. The acceptance floor

The one place where the Metropolis filter could destroy the argument is that a step from `x`
might reject almost everything.  It cannot, uniformly in `x`: because `g ≤ 1`, the ratio
`g(y)/g(x)` is at least `g(y)`, so a lower bound on `g` over the body is a lower bound on
the acceptance probability from *every* point. -/

/-- **The acceptance probability is bounded below by any lower bound on the target density
at the proposed point** — with no hypothesis whatsoever on the current point `x`.

`min(1, g(y)/g(x)) ≥ min(1, g(y)) ≥ α` whenever `α ≤ 1` and `α ≤ g(y)`, because `g(x) ≤ 1`
(which is where `0 < s` is used).  This is the estimate that replaces "the ball walk moves
uniformly", and it costs exactly one factor of the density-sandwich ratio `m/M`. -/
theorem le_metropolisAccept {s : ℝ} (hs : 0 < s) {α : ℝ≥0∞} (hα1 : α ≤ 1)
    (x : EuclideanSpace ℝ (Fin n)) {y : EuclideanSpace ℝ (Fin n)}
    (hy : α ≤ gaussianWeight s y) :
    α ≤ metropolisAccept s x y := by
  rw [metropolisAccept]
  refine le_min hα1 ?_
  rw [ENNReal.le_div_iff_mul_le (Or.inl (gaussianWeight_ne_zero s x))
    (Or.inl (gaussianWeight_ne_top s x))]
  calc α * gaussianWeight s x ≤ α * 1 := by gcongr; exact gaussianWeight_le_one hs x
    _ = α := mul_one α
    _ ≤ gaussianWeight s y := hy

/-- **The concrete acceptance floor on a bounded body**: `e^{-R²/(2s)} ≤ g(y)` for
`‖y‖ ≤ R`.  This is the lower half of the density sandwich of
`Arlib/Convexity/GaussianCooling/Unblock.lean`, in the `gaussianWeight` spelling. -/
theorem ofReal_exp_le_gaussianWeight {s R : ℝ} (hs : 0 < s)
    {y : EuclideanSpace ℝ (Fin n)} (hy : ‖y‖ ≤ R) :
    ENNReal.ofReal (Real.exp (-R ^ 2 / (2 * s))) ≤ gaussianWeight s y :=
  ENNReal.ofReal_le_ofReal (exp_le_gaussianWeightReal hs hy)

/-! ## 2. The one-step overlap estimate (the first new step) -/

/-- **The one-step overlap bound for the Metropolis walk.**  For every acceptance floor `α`
(i.e. `α ≤ 1` and `α ≤ g(y)` throughout `K`), all points `u, v` and every measurable `T`,

    α·ℓ(u)  ≤  P_u(T) + P_v(Tᶜ) + n·‖u - v‖/(2δ),

where `ℓ` is the *unweighted* local conductance `Arlib.MarkovChains.ell` and `P` is
`metropolisGaussian K δ s`.

The proof is the uniform one of `Arlib.MarkovChains.ell_le_ballWalk_add_ballWalk_compl` with
the uniform density replaced by its floor: both one-step distributions dominate `α` times
the uniform measure on `C ∩ K`, `C = B(u,δ) ∩ B(v,δ)`, the events `T` and `Tᶜ` cut `C ∩ K`
in two, and `volume_ball_le_volume_inter_ball_add` says `C ∩ K` misses `B(u,δ) ∩ K` by at
most an `n‖u-v‖/(2δ)` fraction of the proposal ball.  No convexity, no isoperimetry, and no
positivity of `α`.

The `α` is deliberately *not* attached to the error term `n‖u-v‖/(2δ)`: dropping it there
(legitimate since `α ≤ 1`) is what keeps the separation of §3 at `θ'δ/n` with `θ' = αθ`,
rather than degrading it by `α⁻¹`. -/
theorem mul_ell_le_metropolisGaussian_add_metropolisGaussian_compl (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) {δ s : ℝ}
    (hδ : 0 < δ) (hs : 0 < s) {α : ℝ≥0∞} (hα1 : α ≤ 1)
    (hαK : ∀ y ∈ K, α ≤ gaussianWeight s y)
    (u v : EuclideanSpace ℝ (Fin n)) {T : Set (EuclideanSpace ℝ (Fin n))}
    (hT : MeasurableSet T) :
    α * ell K δ u ≤ metropolisGaussian K δ s u T + metropolisGaussian K δ s v Tᶜ
      + ENNReal.ofReal (n * dist u v / (2 * δ)) := by
  set vb : ℝ≥0∞ := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ) with hvb
  have hvb0 : vb ≠ 0 := (Metric.measure_ball_pos volume 0 hδ).ne'
  have hvbtop : vb ≠ ⊤ := measure_ball_lt_top.ne
  have hbu : volume (Metric.ball u δ) = vb := volume_ball_eq u δ
  set C : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball u δ ∩ Metric.ball v δ with hC
  have hCm : MeasurableSet C := measurableSet_ball.inter measurableSet_ball
  have hCu : C ⊆ Metric.ball u δ := Set.inter_subset_left
  have hCv : C ⊆ Metric.ball v δ := Set.inter_subset_right
  have hCtop : volume C ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono hCu)
    rw [hbu]; exact hvbtop
  -- both one-step distributions dominate `α` times the uniform measure on `C ∩ K`
  have key : ∀ w : EuclideanSpace ℝ (Fin n), ∀ A : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet A → C ⊆ Metric.ball w δ →
      vb⁻¹ * (α * volume (A ∩ (C ∩ K))) ≤ metropolisGaussian K δ s w A := by
    intro w A hA hCw
    rw [metropolisGaussian_apply_set K δ s w hA, volume_ball_eq w δ]
    refine le_trans ?_ le_self_add
    gcongr
    calc α * volume (A ∩ (C ∩ K))
        = ∫⁻ _ in A ∩ (C ∩ K), α := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ y in A ∩ (C ∩ K), metropolisDensity s δ w y := by
          refine setLIntegral_mono' (hA.inter (hCm.inter hK)) fun y hy => ?_
          rw [metropolisDensity, Set.indicator_of_mem (hCw hy.2.1)]
          exact le_metropolisAccept hs hα1 w (hαK y hy.2.2)
      _ ≤ ∫⁻ y in A ∩ K, metropolisDensity s δ w y := by
          refine lintegral_mono' (Measure.restrict_mono ?_ le_rfl) le_rfl
          rintro z ⟨hz1, -, hz3⟩
          exact ⟨hz1, hz3⟩
  have h1 := key u T hT hCu
  have h2 := key v Tᶜ hT.compl hCv
  have h3 : volume (T ∩ (C ∩ K)) + volume (Tᶜ ∩ (C ∩ K)) = volume (C ∩ K) := by
    have h := measure_inter_add_sdiff (μ := volume) (C ∩ K) hT
    rwa [Set.inter_comm (C ∩ K) T, Set.sdiff_eq, Set.inter_comm (C ∩ K) Tᶜ] at h
  have hsum : vb⁻¹ * (α * volume (C ∩ K))
      ≤ metropolisGaussian K δ s u T + metropolisGaussian K δ s v Tᶜ := by
    rw [← h3, mul_add, mul_add]
    exact add_le_add h1 h2
  -- the intersection misses only an `n·t/(2δ)` fraction of `B(u, δ)`
  have hdiff : volume (Metric.ball u δ \ C)
      ≤ ENNReal.ofReal (n * dist u v / (2 * δ)) * vb := by
    have hEq : volume C + volume (Metric.ball u δ \ C) = vb := by
      have h := measure_inter_add_sdiff (μ := volume) (Metric.ball u δ) hCm
      rwa [Set.inter_eq_self_of_subset_right hCu, hbu] at h
    have hle : volume C + volume (Metric.ball u δ \ C)
        ≤ volume C + ENNReal.ofReal (n * dist u v / (2 * δ)) * vb := by
      rw [hEq]
      have h := volume_ball_le_volume_inter_ball_add hn u v hδ
      rwa [hbu, ← hC] at h
    exact (ENNReal.add_le_add_iff_left hCtop).1 hle
  have hballK : volume (Metric.ball u δ ∩ K)
      ≤ volume (C ∩ K) + ENNReal.ofReal (n * dist u v / (2 * δ)) * vb := by
    have hsubset : Metric.ball u δ ∩ K ⊆ (C ∩ K) ∪ (Metric.ball u δ \ C) := by
      rintro x ⟨hx1, hx2⟩
      by_cases hxC : x ∈ C
      · exact Or.inl ⟨hxC, hx2⟩
      · exact Or.inr ⟨hx1, hxC⟩
    calc volume (Metric.ball u δ ∩ K)
        ≤ volume ((C ∩ K) ∪ (Metric.ball u δ \ C)) := measure_mono hsubset
      _ ≤ volume (C ∩ K) + volume (Metric.ball u δ \ C) := measure_union_le _ _
      _ ≤ _ := by gcongr
  have hcancel : vb⁻¹ * (ENNReal.ofReal (n * dist u v / (2 * δ)) * vb)
      = ENNReal.ofReal (n * dist u v / (2 * δ)) := by
    rw [mul_comm (ENNReal.ofReal (n * dist u v / (2 * δ))) vb, ← mul_assoc,
      ENNReal.inv_mul_cancel hvb0 hvbtop, one_mul]
  have hell : ell K δ u = vb⁻¹ * volume (Metric.ball u δ ∩ K) := by
    rw [ell_apply, hbu, ENNReal.div_eq_inv_mul]
  rw [hell]
  calc α * (vb⁻¹ * volume (Metric.ball u δ ∩ K))
      ≤ α * (vb⁻¹ * (volume (C ∩ K)
          + ENNReal.ofReal (n * dist u v / (2 * δ)) * vb)) := by gcongr
    _ = vb⁻¹ * (α * volume (C ∩ K))
          + α * (vb⁻¹ * (ENNReal.ofReal (n * dist u v / (2 * δ)) * vb)) := by ring
    _ = vb⁻¹ * (α * volume (C ∩ K)) + α * ENNReal.ofReal (n * dist u v / (2 * δ)) := by
        rw [hcancel]
    _ ≤ (metropolisGaussian K δ s u T + metropolisGaussian K δ s v Tᶜ)
          + ENNReal.ofReal (n * dist u v / (2 * δ)) := by
        gcongr
        calc α * ENNReal.ofReal (n * dist u v / (2 * δ))
            ≤ 1 * ENNReal.ofReal (n * dist u v / (2 * δ)) := by gcongr
          _ = _ := one_mul _

/-! ## 3. Separation -/

/-- **Separation from overlap, for the Metropolis walk.**  If `α·ℓ(u) ≥ θ`, the step from
`u` enters `T` with probability below `θ/4`, and the step from `v` enters `Tᶜ` with
probability below `θ/4`, then `‖u - v‖ > θ·δ/n`.

Word for word `Arlib.MarkovChains.lt_dist_of_ballWalk_lt` with the uniform overlap estimate
replaced by `mul_ell_le_metropolisGaussian_add_metropolisGaussian_compl`; the thresholds are
written multiplicatively to keep the `ℝ≥0∞` arithmetic division-free. -/
theorem lt_dist_of_metropolisGaussian_lt (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) {δ s : ℝ}
    (hδ : 0 < δ) (hs : 0 < s) {α : ℝ≥0∞} (hα1 : α ≤ 1)
    (hαK : ∀ y ∈ K, α ≤ gaussianWeight s y) {θ : ℝ}
    {u v : EuclideanSpace ℝ (Fin n)} {T : Set (EuclideanSpace ℝ (Fin n))}
    (hT : MeasurableSet T) (hu : ENNReal.ofReal θ ≤ α * ell K δ u)
    (hu' : 4 * metropolisGaussian K δ s u T < ENNReal.ofReal θ)
    (hv' : 4 * metropolisGaussian K δ s v Tᶜ < ENNReal.ofReal θ) :
    θ * δ / (n : ℝ) < dist u v := by
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hov := mul_ell_le_metropolisGaussian_add_metropolisGaussian_compl hn hK hδ hs hα1 hαK
    u v hT
  have hΘ := hu.trans hov
  have hXtop : (4:ℝ≥0∞) * ENNReal.ofReal ((n:ℝ) * dist u v / (2 * δ)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  have hΘtop : (2:ℝ≥0∞) * ENNReal.ofReal θ ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  have hstep : (2:ℝ≥0∞) * ENNReal.ofReal θ + 2 * ENNReal.ofReal θ
      < 2 * ENNReal.ofReal θ + 4 * ENNReal.ofReal ((n:ℝ) * dist u v / (2 * δ)) := by
    calc (2:ℝ≥0∞) * ENNReal.ofReal θ + 2 * ENNReal.ofReal θ
        = 4 * ENNReal.ofReal θ := by ring
      _ ≤ 4 * (metropolisGaussian K δ s u T + metropolisGaussian K δ s v Tᶜ
            + ENNReal.ofReal ((n:ℝ) * dist u v / (2 * δ))) := by gcongr
      _ = 4 * metropolisGaussian K δ s u T + 4 * metropolisGaussian K δ s v Tᶜ
            + 4 * ENNReal.ofReal ((n:ℝ) * dist u v / (2 * δ)) := by ring
      _ < ENNReal.ofReal θ + ENNReal.ofReal θ
            + 4 * ENNReal.ofReal ((n:ℝ) * dist u v / (2 * δ)) :=
          ENNReal.add_lt_add_right hXtop (ENNReal.add_lt_add hu' hv')
      _ = 2 * ENNReal.ofReal θ
            + 4 * ENNReal.ofReal ((n:ℝ) * dist u v / (2 * δ)) := by ring
  have hgt : (2:ℝ≥0∞) * ENNReal.ofReal θ
      < 4 * ENNReal.ofReal ((n:ℝ) * dist u v / (2 * δ)) :=
    (ENNReal.add_lt_add_iff_left hΘtop).1 hstep
  have e1 : (2:ℝ≥0∞) * ENNReal.ofReal θ = ENNReal.ofReal (2 * θ) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    simp
  have e2 : (4:ℝ≥0∞) * ENNReal.ofReal ((n:ℝ) * dist u v / (2 * δ))
      = ENNReal.ofReal (4 * ((n:ℝ) * dist u v / (2 * δ))) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
    simp
  rw [e1, e2] at hgt
  have hpos : (0:ℝ) < 4 * ((n:ℝ) * dist u v / (2 * δ)) := by
    by_contra hc
    rw [not_lt] at hc
    rw [ENNReal.ofReal_eq_zero.2 hc] at hgt
    exact absurd hgt (by simp)
  have hreal : 2 * θ < 4 * ((n:ℝ) * dist u v / (2 * δ)) :=
    (ENNReal.ofReal_lt_ofReal_iff hpos).1 hgt
  have h := mul_lt_mul_of_pos_right hreal hδ
  have he : 4 * ((n:ℝ) * dist u v / (2 * δ)) * δ = 2 * ((n:ℝ) * dist u v) := by
    field_simp
    ring
  rw [he] at h
  rw [div_lt_iff₀ hnR]
  nlinarith [h]

/-! ## 4. The conductance bound

The assembly is the paper's three-way partition, and it is *identical* to the uniform one:
`mul_measure_add_measure_le_mul_flow` (`BallWalkConductance.lean`) is stated for an arbitrary
reversible Markov kernel on an arbitrary measurable space and is reused unchanged.  The only
inputs that see the density are the separation of §3 and the isoperimetric inequality, and
both are supplied from outside. -/

/-- **The conductance of the Metropolis-filtered Gaussian ball walk.**

    Φ(metropolisGaussian K δ s)  ≥  min( α·θ/16 , κ·(α·θ)²·δ/(64·n) )

with respect to `π = Arlib.uniformOn (volume.withDensity g) K`, `g(x) = e^{-‖x‖²/(2s)}`,
which by `Arlib.MarkovChains.isReversible_metropolisGaussian` is exactly the chain's
stationary law.

Three hypotheses carry content, all written out inline; none is a `def` or a named `Prop`.

* `hαK` — an **acceptance floor** `α ≤ g(y)` on `K`, with `0 < α ≤ 1`.  On a body inside
  `R·Bₙ` this holds at `α = e^{-R²/(2s)}` (`ofReal_exp_le_gaussianWeight`).  It is the lower
  half of the density sandwich of `Arlib/Convexity/GaussianCooling/Unblock.lean`, and it
  enters the conductance to the **first** power (the isoperimetric constant `κ` already
  carries it squared).
* `hell` — a **uniform lower bound `ℓ(x) ≥ θ` on the unweighted local conductance**, exactly
  as in `Arlib.MarkovChains.conductance_ballWalk_ge`, and satisfiable by
  `Arlib.MarkovChains.le_ell_of_convex_of_ball_subset` on any convex body with an inscribed
  ball.  Some such hypothesis is forced for the same reason as there: near a boundary point
  of a bounded body the walk really is slow.
* `hiso` — the **isoperimetric inequality for the weighted measure `π`**, spelled out.  It is
  *proved*, not assumed, by `Arlib.Convexity.uniformOn_gaussian_iso_kappa` for a convex `K`
  inside `R·Bₙ`, at `κ = e^{-R²/s}·2⁻ⁿ/(2R)`.

The remaining hypotheses are non-degeneracy: `1 ≤ n`, `K` measurable, `0 < δ`, `0 < s`, and
`0 < (volume.withDensity g) K < ∞` so that `π` is a probability measure.

**The constant is exponentially small in `n`** at the parameters that discharge these
hypotheses; see the module docstring.  This is not a polynomial-time bound. -/
theorem conductance_metropolisGaussian_ge (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) {δ s : ℝ}
    (hδ : 0 < δ) (hs : 0 < s)
    (hν0 : ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (gaussianWeight s)) K ≠ 0)
    (hνtop : ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (gaussianWeight s)) K ≠ ⊤)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hαK : ∀ y ∈ K, ENNReal.ofReal α ≤ gaussianWeight s y)
    {θ : ℝ} (hθ : 0 < θ) (hell : ∀ x ∈ K, ENNReal.ofReal θ ≤ ell K δ x)
    {kappa : ℝ≥0∞}
    (hiso : ∀ d : ℝ, 0 < d → ∀ A B : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet A → MeasurableSet B → A ⊆ K → B ⊆ K →
      (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) →
      kappa * ENNReal.ofReal d
          * Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
              (gaussianWeight s)) K A
          * Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
              (gaussianWeight s)) K B
        ≤ Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
              (gaussianWeight s)) K ((K \ A) \ B)) :
    min (ENNReal.ofReal (α * θ) / 16)
        (kappa * ENNReal.ofReal ((α * θ) ^ 2 * δ / (n : ℝ)) / 64)
      ≤ conductance (metropolisGaussian K δ s)
          (Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
            (gaussianWeight s)) K) := by
  set ν : Measure (EuclideanSpace ℝ (Fin n)) :=
    (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight s) with hνdef
  haveI : IsProbabilityMeasure (Arlib.uniformOn ν K) :=
    Arlib.isProbabilityMeasure_uniformOn ν hν0 hνtop
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  set th : ℝ := α * θ with hthdef
  have hth : 0 < th := mul_pos hα0 hθ
  have hdpos : (0:ℝ) < th * δ / (n : ℝ) := by positivity
  have hmul : ENNReal.ofReal th * ENNReal.ofReal (th * δ / (n : ℝ))
      = ENNReal.ofReal (th ^ 2 * δ / (n : ℝ)) := by
    rw [← ENNReal.ofReal_mul hth.le]
    congr 1
    ring
  have hα1' : ENNReal.ofReal α ≤ 1 := ENNReal.ofReal_le_one.2 hα1
  have hellα : ∀ x ∈ K, ENNReal.ofReal th ≤ ENNReal.ofReal α * ell K δ x := by
    intro x hx
    rw [hthdef, ENNReal.ofReal_mul hα0.le]
    gcongr
    exact hell x hx
  have hrev : IsReversible (metropolisGaussian K δ s) (Arlib.uniformOn ν K) :=
    isReversible_metropolisGaussian hK δ s
  have hKc : Arlib.uniformOn ν K Kᶜ = 0 := Arlib.uniformOn_compl_eq_zero ν hK
  set pi : Measure (EuclideanSpace ℝ (Fin n)) := Arlib.uniformOn ν K with hpidef
  set P : Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
    metropolisGaussian K δ s with hPdef
  refine le_conductance P pi fun S hSm hSpos hShalf => ?_
  have hpitop : pi S ≠ ⊤ := measure_ne_top _ _
  have hcompl : pi S + pi Sᶜ = 1 := by
    rw [measure_add_measure_compl hSm, measure_univ]
  have hSc : (1:ℝ≥0∞) / 2 ≤ pi Sᶜ := by
    have h1 : (1:ℝ≥0∞) / 2 + 1 / 2 ≤ 1 / 2 + pi Sᶜ := by
      calc (1:ℝ≥0∞) / 2 + 1 / 2 = 1 := ENNReal.add_halves 1
        _ = pi S + pi Sᶜ := hcompl.symm
        _ ≤ 1 / 2 + pi Sᶜ := by gcongr
    exact (ENNReal.add_le_add_iff_left (by simp)).1 h1
  set S1 : Set (EuclideanSpace ℝ (Fin n)) :=
    (S ∩ K) ∩ {x | 4 * P x Sᶜ < ENNReal.ofReal th} with hS1def
  set S2 : Set (EuclideanSpace ℝ (Fin n)) :=
    (K \ S) ∩ {x | 4 * P x S < ENNReal.ofReal th} with hS2def
  have hS1m : MeasurableSet S1 :=
    (hSm.inter hK).inter
      (measurableSet_lt ((Kernel.measurable_coe P hSm.compl).const_mul 4) measurable_const)
  have hS2m : MeasurableSet S2 :=
    (hK.diff hSm).inter
      (measurableSet_lt ((Kernel.measurable_coe P hSm).const_mul 4) measurable_const)
  have hmem1 : ∀ x, x ∈ S1 ↔ ((x ∈ S ∧ x ∈ K) ∧ 4 * P x Sᶜ < ENNReal.ofReal th) := by
    intro x
    rw [hS1def]
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  have hmem2 : ∀ x, x ∈ S2 ↔ ((x ∈ K ∧ x ∉ S) ∧ 4 * P x S < ENNReal.ofReal th) := by
    intro x
    rw [hS2def]
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_setOf_eq]
  have hS1K : S1 ⊆ K := fun x hx => ((hmem1 x).1 hx).1.2
  have hS2K : S2 ⊆ K := fun x hx => ((hmem2 x).1 hx).1.1
  have hSA : S \ (S1 ∪ Kᶜ) = (S ∩ K) \ S1 := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff]
    tauto
  have hSB : Sᶜ \ (S2 ∪ Kᶜ) = (K \ S) \ S2 := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_compl_iff]
    tauto
  have hA' : ∀ x ∈ S \ (S1 ∪ Kᶜ), ENNReal.ofReal th ≤ 4 * P x Sᶜ := by
    rw [hSA]
    rintro x ⟨⟨hxS, hxK⟩, hxS1⟩
    by_contra hc
    rw [not_le] at hc
    exact hxS1 ((hmem1 x).2 ⟨⟨hxS, hxK⟩, hc⟩)
  have hB' : ∀ x ∈ Sᶜ \ (S2 ∪ Kᶜ), ENNReal.ofReal th ≤ 4 * P x S := by
    rw [hSB]
    rintro x ⟨⟨hxK, hxS⟩, hxS2⟩
    by_contra hc
    rw [not_le] at hc
    exact hxS2 ((hmem2 x).2 ⟨⟨hxK, hxS⟩, hc⟩)
  have hflow : ENNReal.ofReal th * (pi ((S ∩ K) \ S1) + pi ((K \ S) \ S2))
      ≤ 2 * (4 * flow P pi S Sᶜ) := by
    have h := mul_measure_add_measure_le_mul_flow P pi hrev hSm (hS1m.union hK.compl)
      (hS2m.union hK.compl) hA' hB'
    rwa [hSA, hSB] at h
  have hpart : pi ((K \ S1) \ S2) ≤ pi ((S ∩ K) \ S1) + pi ((K \ S) \ S2) := by
    have hsub : (K \ S1) \ S2 ⊆ ((S ∩ K) \ S1) ∪ ((K \ S) \ S2) := by
      rintro x ⟨⟨hxK, hxS1⟩, hxS2⟩
      by_cases hxS : x ∈ S
      · exact Or.inl ⟨⟨hxS, hxK⟩, hxS1⟩
      · exact Or.inr ⟨⟨hxK, hxS⟩, hxS2⟩
    exact (measure_mono hsub).trans (measure_union_le _ _)
  have hcov1 : pi S ≤ pi ((S ∩ K) \ S1) + pi S1 := by
    have hsub : S ⊆ (((S ∩ K) \ S1) ∪ S1) ∪ Kᶜ := by
      intro x hx
      by_cases hxK : x ∈ K
      · by_cases hxS1 : x ∈ S1
        · exact Or.inl (Or.inr hxS1)
        · exact Or.inl (Or.inl ⟨⟨hx, hxK⟩, hxS1⟩)
      · exact Or.inr hxK
    calc pi S ≤ pi ((((S ∩ K) \ S1) ∪ S1) ∪ Kᶜ) := measure_mono hsub
      _ ≤ pi (((S ∩ K) \ S1) ∪ S1) + pi Kᶜ := measure_union_le _ _
      _ ≤ pi ((S ∩ K) \ S1) + pi S1 + pi Kᶜ := by
          gcongr
          exact measure_union_le _ _
      _ = pi ((S ∩ K) \ S1) + pi S1 := by rw [hKc, add_zero]
  have hcov2 : pi Sᶜ ≤ pi ((K \ S) \ S2) + pi S2 := by
    have hsub : Sᶜ ⊆ (((K \ S) \ S2) ∪ S2) ∪ Kᶜ := by
      intro x hx
      by_cases hxK : x ∈ K
      · by_cases hxS2 : x ∈ S2
        · exact Or.inl (Or.inr hxS2)
        · exact Or.inl (Or.inl ⟨⟨hxK, hx⟩, hxS2⟩)
      · exact Or.inr hxK
    calc pi Sᶜ ≤ pi ((((K \ S) \ S2) ∪ S2) ∪ Kᶜ) := measure_mono hsub
      _ ≤ pi (((K \ S) \ S2) ∪ S2) + pi Kᶜ := measure_union_le _ _
      _ ≤ pi ((K \ S) \ S2) + pi S2 + pi Kᶜ := by
          gcongr
          exact measure_union_le _ _
      _ = pi ((K \ S) \ S2) + pi S2 := by rw [hKc, add_zero]
  have hsep : ∀ u ∈ S1, ∀ v ∈ S2, th * δ / (n : ℝ) ≤ dist u v := by
    intro u hu v hv
    have hu8 : 4 * metropolisGaussian K δ s u Sᶜ < ENNReal.ofReal th := by
      have h := ((hmem1 u).1 hu).2
      rwa [hPdef] at h
    have hv8 : 4 * metropolisGaussian K δ s v Sᶜᶜ < ENNReal.ofReal th := by
      have h := ((hmem2 v).1 hv).2
      rw [hPdef] at h
      rwa [compl_compl]
    exact (lt_dist_of_metropolisGaussian_lt hn hK hδ hs hα1' hαK hSm.compl
      (hellα u (hS1K hu)) hu8 hv8).le
  have hkey : ENNReal.ofReal th * pi S ≤ 16 * flow P pi S Sᶜ
      ∨ kappa * ENNReal.ofReal (th ^ 2 * δ / (n : ℝ)) * pi S ≤ 64 * flow P pi S Sᶜ := by
    by_cases hc1 : pi S ≤ 2 * pi ((S ∩ K) \ S1)
    · left
      calc ENNReal.ofReal th * pi S
          ≤ ENNReal.ofReal th * (2 * pi ((S ∩ K) \ S1)) := by gcongr
        _ = 2 * (ENNReal.ofReal th * pi ((S ∩ K) \ S1)) := by ring
        _ ≤ 2 * (ENNReal.ofReal th * (pi ((S ∩ K) \ S1) + pi ((K \ S) \ S2))) := by
            gcongr
            exact le_self_add
        _ ≤ 2 * (2 * (4 * flow P pi S Sᶜ)) := by gcongr
        _ = 16 * flow P pi S Sᶜ := by ring
    by_cases hc2 : pi Sᶜ ≤ 2 * pi ((K \ S) \ S2)
    · left
      calc ENNReal.ofReal th * pi S
          ≤ ENNReal.ofReal th * pi Sᶜ :=
            mul_le_mul_right (hShalf.trans hSc) (ENNReal.ofReal th)
        _ ≤ ENNReal.ofReal th * (2 * pi ((K \ S) \ S2)) := by gcongr
        _ = 2 * (ENNReal.ofReal th * pi ((K \ S) \ S2)) := by ring
        _ ≤ 2 * (ENNReal.ofReal th * (pi ((S ∩ K) \ S1) + pi ((K \ S) \ S2))) := by
            gcongr
            exact le_add_self
        _ ≤ 2 * (2 * (4 * flow P pi S Sᶜ)) := by gcongr
        _ = 16 * flow P pi S Sᶜ := by ring
    right
    rw [not_le] at hc1 hc2
    have h1 : pi S < 2 * pi S1 := by
      have hstep : pi S + pi S < pi S + 2 * pi S1 := by
        calc pi S + pi S = 2 * pi S := (two_mul _).symm
          _ ≤ 2 * (pi ((S ∩ K) \ S1) + pi S1) := by gcongr
          _ = 2 * pi ((S ∩ K) \ S1) + 2 * pi S1 := by ring
          _ < pi S + 2 * pi S1 :=
              ENNReal.add_lt_add_right
                (ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _)) hc1
      exact (ENNReal.add_lt_add_iff_left hpitop).1 hstep
    have h2 : pi Sᶜ < 2 * pi S2 := by
      have hstep : pi Sᶜ + pi Sᶜ < pi Sᶜ + 2 * pi S2 := by
        calc pi Sᶜ + pi Sᶜ = 2 * pi Sᶜ := (two_mul _).symm
          _ ≤ 2 * (pi ((K \ S) \ S2) + pi S2) := by gcongr
          _ = 2 * pi ((K \ S) \ S2) + 2 * pi S2 := by ring
          _ < pi Sᶜ + 2 * pi S2 :=
              ENNReal.add_lt_add_right
                (ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _)) hc2
      exact (ENNReal.add_lt_add_iff_left (measure_ne_top _ _)).1 hstep
    have h2half : (1:ℝ≥0∞) ≤ 2 * pi Sᶜ := by
      have hhalf : (2:ℝ≥0∞) * (1 / 2) = 1 := by
        rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
      calc (1:ℝ≥0∞) = 2 * (1 / 2) := hhalf.symm
        _ ≤ 2 * pi Sᶜ := by gcongr
    have h3 : (1:ℝ≥0∞) ≤ 4 * pi S2 := by
      calc (1:ℝ≥0∞) ≤ 2 * pi Sᶜ := h2half
        _ ≤ 2 * (2 * pi S2) := by gcongr
        _ = 4 * pi S2 := by ring
    have hprod : pi S ≤ 8 * (pi S1 * pi S2) := by
      calc pi S = pi S * 1 := (mul_one _).symm
        _ ≤ 2 * pi S1 * (4 * pi S2) := mul_le_mul' h1.le h3
        _ = 8 * (pi S1 * pi S2) := by ring
    have hisoS := hiso (th * δ / (n : ℝ)) hdpos S1 S2 hS1m hS2m hS1K hS2K hsep
    calc kappa * ENNReal.ofReal (th ^ 2 * δ / (n : ℝ)) * pi S
        = ENNReal.ofReal th * (kappa * ENNReal.ofReal (th * δ / (n : ℝ)) * pi S) := by
          rw [← hmul]; ring
      _ ≤ ENNReal.ofReal th *
            (kappa * ENNReal.ofReal (th * δ / (n : ℝ)) * (8 * (pi S1 * pi S2))) := by gcongr
      _ = 8 * (ENNReal.ofReal th *
            (kappa * ENNReal.ofReal (th * δ / (n : ℝ)) * pi S1 * pi S2)) := by ring
      _ ≤ 8 * (ENNReal.ofReal th * pi ((K \ S1) \ S2)) := by gcongr
      _ ≤ 8 * (ENNReal.ofReal th * (pi ((S ∩ K) \ S1) + pi ((K \ S) \ S2))) := by gcongr
      _ ≤ 8 * (2 * (4 * flow P pi S Sᶜ)) := by gcongr
      _ = 64 * flow P pi S Sᶜ := by ring
  have hswap : ∀ a b c : ℝ≥0∞, a / c * b = a * b / c := by
    intro a b c
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]
  rw [conductanceOn_apply, ENNReal.le_div_iff_mul_le (Or.inl hSpos.ne') (Or.inl hpitop)]
  rcases hkey with h | h
  · calc min (ENNReal.ofReal th / 16)
            (kappa * ENNReal.ofReal (th ^ 2 * δ / (n : ℝ)) / 64) * pi S
        ≤ ENNReal.ofReal th / 16 * pi S := by gcongr; exact min_le_left _ _
      _ = ENNReal.ofReal th * pi S / 16 := hswap _ _ _
      _ ≤ flow P pi S Sᶜ := by
          rw [ENNReal.div_le_iff_le_mul (Or.inl (by norm_num)) (Or.inl (by norm_num))]
          exact h.trans_eq (mul_comm _ _)
  · calc min (ENNReal.ofReal th / 16)
            (kappa * ENNReal.ofReal (th ^ 2 * δ / (n : ℝ)) / 64) * pi S
        ≤ kappa * ENNReal.ofReal (th ^ 2 * δ / (n : ℝ)) / 64 * pi S := by
          gcongr; exact min_le_right _ _
      _ = kappa * ENNReal.ofReal (th ^ 2 * δ / (n : ℝ)) * pi S / 64 := hswap _ _ _
      _ ≤ flow P pi S Sᶜ := by
          rw [ENNReal.div_le_iff_le_mul (Or.inl (by norm_num)) (Or.inl (by norm_num))]
          exact h.trans_eq (mul_comm _ _)

/-! ## 5. Non-degeneracy of the weighted target

`Arlib.MarkovChains.mixesWithin_of_conductance` needs two facts about the target measure
alone: that the conductance is not the empty infimum `⊤`, and that `L²(π)` contains a
non-constant function.  Both follow from a measurable set of relative `π`-mass in `(0, 1/2]`.
`Arlib.MarkovChains.exists_smallSet_uniformOn` supplies one for *Lebesgue* measure; the
Gaussian weight is strictly positive and bounded by `1`, so the same set works here. -/

/-- **The Gaussian weight is null-preserving in both directions**: since `g > 0` everywhere,
`(volume.withDensity g) A = 0` exactly when `volume A = 0`. -/
theorem withDensity_gaussianWeight_eq_zero_iff (s : ℝ)
    (A : Set (EuclideanSpace ℝ (Fin n))) :
    ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight s)) A = 0
      ↔ volume A = 0 := by
  rw [withDensity_apply_eq_zero (measurable_gaussianWeight s)]
  have h : {x : EuclideanSpace ℝ (Fin n) | gaussianWeight s x ≠ 0} = Set.univ :=
    Set.eq_univ_of_forall fun x => gaussianWeight_ne_zero s x
  rw [h, Set.univ_inter]

/-- The Gaussian-weighted measure of a set of positive Lebesgue measure is positive. -/
theorem withDensity_gaussianWeight_ne_zero (s : ℝ) {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA : volume A ≠ 0) :
    ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight s)) A ≠ 0 :=
  fun h => hA ((withDensity_gaussianWeight_eq_zero_iff s A).1 h)

/-- The Gaussian-weighted measure of a measurable set of finite Lebesgue measure is finite,
because `g ≤ 1` for `s > 0`. -/
theorem withDensity_gaussianWeight_ne_top {s : ℝ} (hs : 0 < s)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hAm : MeasurableSet A) (hA : volume A ≠ ⊤) :
    ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight s)) A ≠ ⊤ := by
  refine ne_top_of_le_ne_top hA ?_
  rw [withDensity_apply _ hAm]
  calc ∫⁻ x in A, gaussianWeight s x ≤ ∫⁻ _ in A, 1 :=
        setLIntegral_mono' hAm fun x _ => gaussianWeight_le_one hs x
    _ = volume A := by simp

/-- **A body of positive finite volume has a piece of relative Gaussian mass in `(0, 1/2]`.**

This is the non-degeneracy input of `Arlib.MarkovChains.mixesWithin_of_conductance` for the
weighted target.  The witness is the same ball that
`Arlib.MarkovChains.exists_volume_inter_ball_pos_lt` produces for Lebesgue measure: the
Gaussian weight is strictly positive, so it preserves both "positive mass" and "not all the
mass". -/
theorem exists_smallSet_uniformOn_gaussian (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤) {s : ℝ} (hs : 0 < s) :
    ∃ S : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet S ∧
      0 < Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          (gaussianWeight s)) K S ∧
      Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          (gaussianWeight s)) K S ≤ 1 / 2 := by
  set ν : Measure (EuclideanSpace ℝ (Fin n)) :=
    (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight s) with hνdef
  have hν0 : ν K ≠ 0 := withDensity_gaussianWeight_ne_zero s hK0
  have hνtop : ν K ≠ ⊤ := withDensity_gaussianWeight_ne_top hs hK hKtop
  haveI : IsProbabilityMeasure (Arlib.uniformOn ν K) :=
    Arlib.isProbabilityMeasure_uniformOn ν hν0 hνtop
  obtain ⟨r, hrpos, hrlt⟩ := exists_volume_inter_ball_pos_lt hn hK0 hKtop
  set S : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r with hS
  have hSm : MeasurableSet S := measurableSet_ball
  have hInt0 : ν (K ∩ S) ≠ 0 := withDensity_gaussianWeight_ne_zero s hrpos.ne'
  have hdiff0 : volume (K \ S) ≠ 0 := by
    intro h0
    have h := measure_inter_add_sdiff (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      K hSm
    rw [h0, add_zero] at h
    exact absurd h hrlt.ne
  have hνdiff0 : ν (K \ S) ≠ 0 := withDensity_gaussianWeight_ne_zero s hdiff0
  have hsplit : ν (K ∩ S) + ν (K \ S) = ν K := measure_inter_add_sdiff K hSm
  have hInttop : ν (K ∩ S) ≠ ⊤ :=
    ne_top_of_le_ne_top hνtop (measure_mono Set.inter_subset_left)
  have hlt : ν (K ∩ S) < ν K := by
    rw [← hsplit]
    exact ENNReal.lt_add_right hInttop hνdiff0
  have hval : Arlib.uniformOn ν K S = ν (K ∩ S) / ν K := by
    rw [Arlib.uniformOn_apply ν hK hSm, Set.inter_comm]
  have hpos : 0 < Arlib.uniformOn ν K S := by
    rw [hval]
    exact ENNReal.div_pos hInt0 hνtop
  have hone : Arlib.uniformOn ν K S < 1 := by
    rw [hval, ENNReal.div_lt_iff (Or.inl hν0) (Or.inl hνtop), one_mul]
    exact hlt
  rcases le_or_gt (Arlib.uniformOn ν K S) (1 / 2) with h | h
  · exact ⟨S, hSm, hpos, h⟩
  · refine ⟨Sᶜ, hSm.compl, ?_, ?_⟩
    · rw [prob_compl_eq_one_sub hSm]
      exact tsub_pos_of_lt hone
    · rw [prob_compl_eq_one_sub hSm, tsub_le_iff_left]
      calc (1 : ℝ≥0∞) = 1 / 2 + 1 / 2 := (ENNReal.add_halves 1).symm
        _ ≤ Arlib.uniformOn ν K S + 1 / 2 := by gcongr

/-! ## 6. Mixing

`Arlib.MarkovChains.lazy` and its two structural theorems `isReversible_lazy`,
`hasNonnegSpectrum_lazy` are stated for an arbitrary kernel on an arbitrary measurable
space in `BallWalkConductance.lean`, and `conductance_lazy` says laziness halves the
conductance exactly.  So the whole laziness bridge is reused without change. -/

/-- **The lazy Metropolis-filtered Gaussian ball walk is reversible for the
Gaussian-restricted measure and has nonnegative spectrum** — the two kernel-level
hypotheses of `Arlib.MarkovChains.mixesWithin_of_conductance`. -/
theorem isReversible_and_hasNonnegSpectrum_lazy_metropolisGaussian
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (δ : ℝ) {s : ℝ}
    (hν0 : ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (gaussianWeight s)) K ≠ 0)
    (hνtop : ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (gaussianWeight s)) K ≠ ⊤) :
    IsReversible (lazy (metropolisGaussian K δ s))
        (Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          (gaussianWeight s)) K)
      ∧ HasNonnegSpectrum (lazy (metropolisGaussian K δ s))
        (Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          (gaussianWeight s)) K) := by
  haveI : IsProbabilityMeasure
      (Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight s)) K) :=
    Arlib.isProbabilityMeasure_uniformOn _ hν0 hνtop
  exact ⟨isReversible_lazy (isReversible_metropolisGaussian hK δ s),
    hasNonnegSpectrum_lazy (isReversible_metropolisGaussian hK δ s)⟩

/-- **The lazy Metropolis-filtered Gaussian ball walk on `K` mixes to total variation `eps`
from an `M`-warm start** in

    conductanceMixingTime M (min (α·θ/32) (κ·(α·θ)²·δ/(128·n))) eps

steps, i.e. `O(φ⁻² log(M/eps))` steps with `φ = min(αθ/32, κ(αθ)²δ/(128n))`.

The target is `Arlib.uniformOn (volume.withDensity g) K` with `g(x) = e^{-‖x‖²/(2s)}`,
which is *exactly* the chain's stationary law
(`Arlib.MarkovChains.invariant_metropolisGaussian`), so there is no residual bias term in
the conclusion.

The hypotheses with content are the same three as in `conductance_metropolisGaussian_ge` —
the acceptance floor `hαK`, the local-conductance floor `hell`, and the isoperimetric
inequality `hiso` — all written out inline, plus the warm start.  All three are discharged
for a convex body in `mixesWithin_lazy_metropolisGaussian_convex` below.

**The step count is exponential in `n`** at the parameters that discharge them; see the
module docstring. -/
theorem mixesWithin_lazy_metropolisGaussian (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤) {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hαK : ∀ y ∈ K, ENNReal.ofReal α ≤ gaussianWeight s y)
    {θ : ℝ} (hθ : 0 < θ) (hell : ∀ x ∈ K, ENNReal.ofReal θ ≤ ell K δ x)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hiso : ∀ d : ℝ, 0 < d → ∀ A B : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet A → MeasurableSet B → A ⊆ K → B ⊆ K →
      (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) →
      ENNReal.ofReal kappa * ENNReal.ofReal d
          * Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
              (gaussianWeight s)) K A
          * Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
              (gaussianWeight s)) K B
        ≤ Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
              (gaussianWeight s)) K ((K \ A) \ B))
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0
      (Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight s)) K))
    {eps : ℝ} (heps : 0 < eps) {t : ℕ}
    (ht : conductanceMixingTime M
      (min (α * θ / 32) (kappa * (α * θ) ^ 2 * δ / (128 * (n : ℝ)))) eps ≤ t) :
    MixesWithin (lazy (metropolisGaussian K δ s))
      (Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight s)) K) mu0 t (ENNReal.ofReal eps) := by
  have hν0 : ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (gaussianWeight s)) K ≠ 0 := withDensity_gaussianWeight_ne_zero s hK0
  have hνtop : ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (gaussianWeight s)) K ≠ ⊤ := withDensity_gaussianWeight_ne_top hs hK hKtop
  haveI : IsProbabilityMeasure
      (Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight s)) K) :=
    Arlib.isProbabilityMeasure_uniformOn _ hν0 hνtop
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨hrev, hpsd⟩ :=
    isReversible_and_hasNonnegSpectrum_lazy_metropolisGaussian hK δ hν0 hνtop
  obtain ⟨S0, hS0m, hS0pos, hS0half⟩ := exists_smallSet_uniformOn_gaussian hn hK hK0 hKtop hs
  have hne := rayleighSet_nonempty_of_smallSet (lazy (metropolisGaussian K δ s)) hS0m hS0pos
    hS0half
  obtain ⟨x0, hx0⟩ := nonempty_of_measure_ne_zero hK0
  have hθ1 : θ ≤ 1 := ENNReal.ofReal_le_one.1 ((hell x0 hx0).trans (ell_le_one K δ x0))
  set phi : ℝ := min (α * θ / 32) (kappa * (α * θ) ^ 2 * δ / (128 * (n : ℝ))) with hphidef
  have hphi0 : 0 < phi := lt_min (by positivity) (by positivity)
  have hphi1 : phi ≤ 1 := by
    refine le_trans (min_le_left _ _) ?_
    nlinarith
  have hcond := conductance_metropolisGaussian_ge hn hK hδ hs hν0 hνtop hα0 hα1 hαK hθ hell
    (kappa := ENNReal.ofReal kappa) hiso
  have hbranch1 : ENNReal.ofReal phi * 2 ≤ ENNReal.ofReal (α * θ) / 16 := by
    have h16 : ENNReal.ofReal (α * θ) / 16 = ENNReal.ofReal (α * θ / 16) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 16)]
      norm_num
    have hmul : ENNReal.ofReal phi * 2 = ENNReal.ofReal (phi * 2) := by
      rw [ENNReal.ofReal_mul hphi0.le]
      norm_num
    rw [h16, hmul]
    refine ENNReal.ofReal_le_ofReal ?_
    have hmin := min_le_left (α * θ / 32) (kappa * (α * θ) ^ 2 * δ / (128 * (n : ℝ)))
    rw [← hphidef] at hmin
    linarith
  have hbranch2 : ENNReal.ofReal phi * 2
      ≤ ENNReal.ofReal kappa * ENNReal.ofReal ((α * θ) ^ 2 * δ / (n : ℝ)) / 64 := by
    have hrhs : ENNReal.ofReal kappa * ENNReal.ofReal ((α * θ) ^ 2 * δ / (n : ℝ)) / 64
        = ENNReal.ofReal (kappa * ((α * θ) ^ 2 * δ / (n : ℝ)) / 64) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 64),
        ENNReal.ofReal_mul hkappa.le]
      norm_num
    have hmul : ENNReal.ofReal phi * 2 = ENNReal.ofReal (phi * 2) := by
      rw [ENNReal.ofReal_mul hphi0.le]
      norm_num
    rw [hrhs, hmul]
    refine ENNReal.ofReal_le_ofReal ?_
    have hmin := min_le_right (α * θ / 32) (kappa * (α * θ) ^ 2 * δ / (128 * (n : ℝ)))
    rw [← hphidef] at hmin
    have heq : kappa * (α * θ) ^ 2 * δ / (128 * (n : ℝ)) * 2
        = kappa * ((α * θ) ^ 2 * δ / (n : ℝ)) / 64 := by
      field_simp
      ring
    nlinarith [hmin]
  have hlazy : ENNReal.ofReal phi
      ≤ conductance (lazy (metropolisGaussian K δ s))
          (Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
            (gaussianWeight s)) K) := by
    rw [conductance_lazy]
    have hstep : ENNReal.ofReal phi
        ≤ min (ENNReal.ofReal (α * θ) / 16)
            (ENNReal.ofReal kappa * ENNReal.ofReal ((α * θ) ^ 2 * δ / (n : ℝ)) / 64) / 2 := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      exact le_min hbranch1 hbranch2
    exact hstep.trans (by gcongr)
  have hcondtop : conductance (lazy (metropolisGaussian K δ s))
      (Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight s)) K) ≠ ⊤ :=
    ne_top_of_le_ne_top (by norm_num)
      (conductance_le_one _ _ ⟨S0, hS0m, hS0pos, hS0half⟩)
  have hphireal : phi ≤ (conductance (lazy (metropolisGaussian K δ s))
      (Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight s)) K)).toReal := by
    have h := ENNReal.toReal_mono hcondtop hlazy
    rwa [ENNReal.toReal_ofReal hphi0.le] at h
  exact mixesWithin_of_conductance hrev hpsd hne hM hwarm hphi0 hphi1 heps hphireal ht

/-! ## 7. The unconditional convex-body instances

Here the three hypotheses with content are all discharged, and what remains is geometry:
`K` convex, measurable, bounded (by `R`), with an inscribed ball `B(c,γ)`.  The isoperimetric
inequality comes from `Arlib.Convexity.uniformOn_gaussian_iso_kappa`, the local-conductance
floor from `Arlib.MarkovChains.le_ell_of_convex_of_ball_subset`, and the acceptance floor
from `ofReal_exp_le_gaussianWeight`. -/

/-- The `gaussianWeight` of `MetropolisGaussian.lean` is the inline weight of
`Arlib/Convexity/GaussianCooling/Unblock.lean`, definitionally.  This is a bridge, not a
claim: it is proved by `rfl`, so no name can stand in for an unproved identification. -/
theorem gaussianWeight_eq_ofReal_exp (s : ℝ) :
    (gaussianWeight s : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
      = fun x => ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / (2 * s))) := rfl

/-- **The conductance of the Metropolis-filtered Gaussian ball walk on a bounded convex body
with an inscribed ball — with nothing assumed.**

    Φ  ≥  min( α·θ/16 ,  κ·(α·θ)²·δ/(64·n) ),
    α = e^{-R²/(2s)},   θ = (γ/(γ+2R))ⁿ,   κ = e^{-R²/s}·2⁻ⁿ/(2R).

Assumed: only geometry — `1 ≤ n`; `K` measurable, convex, of finite volume, contained in
`R·Bₙ` and containing `B(c,γ)`; a step `0 < δ ≤ γ`; a temperature `0 < s`.  There is **no**
isoperimetric hypothesis and **no** local-conductance hypothesis: the first is
`Arlib.Convexity.uniformOn_gaussian_iso_kappa`, the second
`Arlib.MarkovChains.le_ell_of_convex_of_ball_subset`, and the acceptance floor is
`ofReal_exp_le_gaussianWeight`.

Proved: the conductance of `metropolisGaussian K δ s` with respect to *its own* stationary
measure `Arlib.uniformOn (volume.withDensity e^{-‖·‖²/(2s)}) K`.

**All three constants are exponentially small in `n`, so this bound is exponentially small
and is not a polynomial-time statement.** -/
theorem conductance_metropolisGaussian_convex (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKm : MeasurableSet K) (hconv : Convex ℝ K)
    (hKtop : volume K ≠ ⊤)
    {c : EuclideanSpace ℝ (Fin n)} {γ : ℝ} (hγ : 0 < γ) (hballγ : Metric.ball c γ ⊆ K)
    {R : ℝ} (hR0 : 0 < R) (hR : K ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)
    {δ s : ℝ} (hδ : 0 < δ) (hδγ : δ ≤ γ) (hs : 0 < s) :
    min (ENNReal.ofReal (Real.exp (-R ^ 2 / (2 * s)) * (γ / (γ + 2 * R)) ^ n) / 16)
        (ENNReal.ofReal (Real.exp (-(R ^ 2) / s) * (1 / 2 : ℝ) ^ n / (2 * R))
          * ENNReal.ofReal
              ((Real.exp (-R ^ 2 / (2 * s)) * (γ / (γ + 2 * R)) ^ n) ^ 2 * δ / (n : ℝ)) / 64)
      ≤ conductance (metropolisGaussian K δ s)
          (Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
            (gaussianWeight s)) K) := by
  have hK0 : volume K ≠ 0 := volume_ne_zero_of_ball_subset hγ hballγ
  have hnorm : ∀ x ∈ K, ‖x‖ ≤ R := by
    intro x hx
    have hxb := hR hx
    rwa [mem_closedBall_zero_iff] at hxb
  have hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ 2 * R := by
    intro x hx y hy
    calc dist x y = ‖x - y‖ := dist_eq_norm x y
      _ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
      _ ≤ 2 * R := by linarith [hnorm x hx, hnorm y hy]
  have hiso := Arlib.Convexity.uniformOn_gaussian_iso_kappa hs hconv hKm hK0 hKtop hR
  rw [← gaussianWeight_eq_ofReal_exp s] at hiso
  refine conductance_metropolisGaussian_ge hn hKm hδ hs
    (withDensity_gaussianWeight_ne_zero s hK0)
    (withDensity_gaussianWeight_ne_top hs hKm hKtop)
    (α := Real.exp (-R ^ 2 / (2 * s))) (Real.exp_pos _) ?_ ?_
    (θ := (γ / (γ + 2 * R)) ^ n) (by positivity)
    (le_ell_of_convex_of_ball_subset hconv hγ hballγ hD hδ hδγ)
    (kappa := ENNReal.ofReal (Real.exp (-(R ^ 2) / s) * (1 / 2 : ℝ) ^ n / (2 * R))) hiso
  · rw [Real.exp_le_one_iff, neg_div]
    exact neg_nonpos.2 (div_nonneg (sq_nonneg _) (by linarith))
  · exact fun y hy => ofReal_exp_le_gaussianWeight hs (hnorm y hy)

/-- **Unconditional total-variation mixing of the lazy Metropolis-filtered Gaussian ball
walk on a bounded convex body with an inscribed ball.**

Assumed: only geometry, plus an `M`-warm start, an accuracy `eps > 0` and enough steps.
**No isoperimetric hypothesis and no local-conductance hypothesis.**

Proved: after `t` steps the law is within `eps` in total variation of
`Arlib.uniformOn (volume.withDensity e^{-‖·‖²/(2s)}) K`, which is exactly the chain's
stationary measure — so `eps` is the only error.

The step count is exponential in `n`; see the module docstring. -/
theorem mixesWithin_lazy_metropolisGaussian_convex (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKm : MeasurableSet K) (hconv : Convex ℝ K)
    (hKtop : volume K ≠ ⊤)
    {c : EuclideanSpace ℝ (Fin n)} {γ : ℝ} (hγ : 0 < γ) (hballγ : Metric.ball c γ ⊆ K)
    {R : ℝ} (hR0 : 0 < R) (hR : K ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)
    {δ s : ℝ} (hδ : 0 < δ) (hδγ : δ ≤ γ) (hs : 0 < s)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0
      (Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight s)) K))
    {eps : ℝ} (heps : 0 < eps) {t : ℕ}
    (ht : conductanceMixingTime M
      (min (Real.exp (-R ^ 2 / (2 * s)) * (γ / (γ + 2 * R)) ^ n / 32)
        (Real.exp (-(R ^ 2) / s) * (1 / 2 : ℝ) ^ n / (2 * R)
          * (Real.exp (-R ^ 2 / (2 * s)) * (γ / (γ + 2 * R)) ^ n) ^ 2 * δ
          / (128 * (n : ℝ)))) eps ≤ t) :
    MixesWithin (lazy (metropolisGaussian K δ s))
      (Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight s)) K) mu0 t (ENNReal.ofReal eps) := by
  have hK0 : volume K ≠ 0 := volume_ne_zero_of_ball_subset hγ hballγ
  have hnorm : ∀ x ∈ K, ‖x‖ ≤ R := by
    intro x hx
    have hxb := hR hx
    rwa [mem_closedBall_zero_iff] at hxb
  have hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ 2 * R := by
    intro x hx y hy
    calc dist x y = ‖x - y‖ := dist_eq_norm x y
      _ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
      _ ≤ 2 * R := by linarith [hnorm x hx, hnorm y hy]
  have hiso := Arlib.Convexity.uniformOn_gaussian_iso_kappa hs hconv hKm hK0 hKtop hR
  rw [← gaussianWeight_eq_ofReal_exp s] at hiso
  refine mixesWithin_lazy_metropolisGaussian hn hKm hK0 hKtop hδ hs
    (α := Real.exp (-R ^ 2 / (2 * s))) (Real.exp_pos _) ?_ ?_
    (θ := (γ / (γ + 2 * R)) ^ n) (by positivity)
    (le_ell_of_convex_of_ball_subset hconv hγ hballγ hD hδ hδγ)
    (kappa := Real.exp (-(R ^ 2) / s) * (1 / 2 : ℝ) ^ n / (2 * R)) (by positivity) ?_
    hM hwarm heps ht
  · rw [Real.exp_le_one_iff, neg_div]
    exact neg_nonpos.2 (div_nonneg (sq_nonneg _) (by linarith))
  · exact fun y hy => ofReal_exp_le_gaussianWeight hs (hnorm y hy)
  · exact hiso

/-! ## 8. Removing the radius, and the non-vacuity witness

`Arlib.Convexity.exists_closedBall_superset_of_convex` manufactures the radius `R` out of
convexity, an inscribed unit ball and finiteness of the volume — the exact hypothesis bundle
a volume-oracle interface supplies.  With it the geometric hypotheses collapse to three, and
the conductance is *positive* with no assumption at all.  The radius it produces is
`max 1 (2·vol K/vol B(0,1/2))`, exponentially large in `n`, so the resulting constant is
doubly exponentially small; the statement is therefore existential in `φ`, claiming only
positivity. -/

/-- **The Metropolis-filtered Gaussian ball walk on a convex body has strictly positive
conductance — unconditionally.**

For every convex measurable `K ⊆ ℝⁿ` containing the unit ball and of finite volume — the
class a volume oracle quantifies over — every step `0 < δ ≤ 1` and every temperature
`s > 0`, there is a `φ > 0` with `φ ≤ Φ(metropolisGaussian K δ s)` for the chain's own
stationary measure.

**Assumed: nothing.**  The isoperimetric input is
`Arlib.Convexity.exists_uniformOn_gaussian_iso_of_convex`, the local-conductance floor is
`Arlib.MarkovChains.le_ell_of_convex_of_ball_subset`, and the acceptance floor is
`ofReal_exp_le_gaussianWeight`.

**Cost.**  The `φ` produced is `min(αθ/16, κ(αθ)²δ/(64n))` at `R = max 1 (2·vol K/vol
B(0,1/2))`, hence *doubly* exponentially small in `n` in the worst case.  The statement is
existential precisely because no useful uniform constant is claimed: what is claimed is
positivity, which is what makes the conductance non-trivial, and nothing more.  **This is
not a polynomial-time result.** -/
theorem exists_conductance_metropolisGaussian_pos (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKm : MeasurableSet K) (hconv : Convex ℝ K)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) (hKtop : volume K ≠ ⊤)
    {δ s : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : 0 < s) :
    ∃ phi : ℝ, 0 < phi ∧
      ENNReal.ofReal phi ≤ conductance (metropolisGaussian K δ s)
        (Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          (gaussianWeight s)) K) := by
  obtain ⟨R, hR0, hR⟩ := Arlib.Convexity.exists_closedBall_superset_of_convex hconv hball hKtop
  set α : ℝ := Real.exp (-R ^ 2 / (2 * s)) with hα
  set θ : ℝ := (1 / (1 + 2 * R)) ^ n with hθ
  set kap : ℝ := Real.exp (-(R ^ 2) / s) * (1 / 2 : ℝ) ^ n / (2 * R) with hkap
  have hR1 : (0:ℝ) < 1 + 2 * R := by linarith
  have hα0 : 0 < α := Real.exp_pos _
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  have hkap0 : 0 < kap := by rw [hkap]; positivity
  refine ⟨min (α * θ / 16) (kap * (α * θ) ^ 2 * δ / (64 * (n : ℝ))), ?_, ?_⟩
  · have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
    exact lt_min (by positivity) (by positivity)
  · have hmain := conductance_metropolisGaussian_convex hn hKm hconv hKtop
      (c := 0) (γ := 1) one_pos hball hR0 hR hδ hδ1 hs
    refine le_trans ?_ hmain
    have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
    refine le_min ?_ ?_
    · calc ENNReal.ofReal (min (α * θ / 16) (kap * (α * θ) ^ 2 * δ / (64 * (n : ℝ))))
          ≤ ENNReal.ofReal (α * θ / 16) :=
            ENNReal.ofReal_le_ofReal (min_le_left _ _)
        _ = ENNReal.ofReal (α * θ) / 16 := by
            rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 16)]
            norm_num
    · calc ENNReal.ofReal (min (α * θ / 16) (kap * (α * θ) ^ 2 * δ / (64 * (n : ℝ))))
          ≤ ENNReal.ofReal (kap * ((α * θ) ^ 2 * δ / (n : ℝ)) / 64) := by
            refine ENNReal.ofReal_le_ofReal (le_trans (min_le_right _ _) (le_of_eq ?_))
            field_simp
        _ = ENNReal.ofReal kap * ENNReal.ofReal ((α * θ) ^ 2 * δ / (n : ℝ)) / 64 := by
            rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 64),
              ENNReal.ofReal_mul hkap0.le]
            norm_num

/-- **Non-vacuity (`CLAUDE.md` §11): the whole hypothesis bundle is jointly satisfiable, and
the chain really mixes.**

For every convex measurable `K` containing the unit ball with finite volume, every
`0 < δ ≤ 1`, every `s > 0` and every `eps > 0` there is a starting law and a step count for
which the lazy Metropolis-filtered Gaussian ball walk is within `eps` in total variation of
its stationary measure.  Nothing is assumed: the warm start is the target itself (`1`-warm)
and the step count is a natural number.

The step count is exponential in `n`; see the module docstring. -/
theorem exists_mixesWithin_lazy_metropolisGaussian_convex (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKm : MeasurableSet K) (hconv : Convex ℝ K)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) (hKtop : volume K ≠ ⊤)
    {δ s : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : 0 < s) {eps : ℝ} (heps : 0 < eps) :
    ∃ (mu0 : Measure (EuclideanSpace ℝ (Fin n))) (_ : IsProbabilityMeasure mu0) (t : ℕ),
      MixesWithin (lazy (metropolisGaussian K δ s))
        (Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          (gaussianWeight s)) K) mu0 t (ENNReal.ofReal eps) := by
  obtain ⟨R, hR0, hR⟩ := Arlib.Convexity.exists_closedBall_superset_of_convex hconv hball hKtop
  have hK0 : volume K ≠ 0 := volume_ne_zero_of_ball_subset one_pos hball
  haveI hprob : IsProbabilityMeasure
      (Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight s)) K) :=
    Arlib.isProbabilityMeasure_uniformOn _ (withDensity_gaussianWeight_ne_zero s hK0)
      (withDensity_gaussianWeight_ne_top hs hKm hKtop)
  refine ⟨Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (gaussianWeight s)) K, hprob,
    conductanceMixingTime 1
      (min (Real.exp (-R ^ 2 / (2 * s)) * ((1:ℝ) / (1 + 2 * R)) ^ n / 32)
        (Real.exp (-(R ^ 2) / s) * (1 / 2 : ℝ) ^ n / (2 * R)
          * (Real.exp (-R ^ 2 / (2 * s)) * ((1:ℝ) / (1 + 2 * R)) ^ n) ^ 2 * δ
          / (128 * (n : ℝ)))) eps, ?_⟩
  refine mixesWithin_lazy_metropolisGaussian_convex hn hKm hconv hKtop
    (c := 0) (γ := 1) one_pos hball hR0 hR hδ hδ1 hs (M := 1) le_rfl ?_ heps le_rfl
  simp only [ENNReal.ofReal_one]
  exact isWarm_one_self _

/-! ## Axiom audit -/

#print axioms le_metropolisAccept
#print axioms ofReal_exp_le_gaussianWeight
#print axioms mul_ell_le_metropolisGaussian_add_metropolisGaussian_compl
#print axioms lt_dist_of_metropolisGaussian_lt
#print axioms conductance_metropolisGaussian_ge
#print axioms withDensity_gaussianWeight_eq_zero_iff
#print axioms withDensity_gaussianWeight_ne_zero
#print axioms withDensity_gaussianWeight_ne_top
#print axioms exists_smallSet_uniformOn_gaussian
#print axioms isReversible_and_hasNonnegSpectrum_lazy_metropolisGaussian
#print axioms mixesWithin_lazy_metropolisGaussian
#print axioms gaussianWeight_eq_ofReal_exp
#print axioms conductance_metropolisGaussian_convex
#print axioms mixesWithin_lazy_metropolisGaussian_convex
#print axioms exists_conductance_metropolisGaussian_pos
#print axioms exists_mixesWithin_lazy_metropolisGaussian_convex

end Arlib.MarkovChains
