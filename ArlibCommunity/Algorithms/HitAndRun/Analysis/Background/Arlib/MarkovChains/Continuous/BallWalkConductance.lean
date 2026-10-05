/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.BallWalk
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.L2Mixing
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.PointwiseRoute
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Overlap, separation, and a conductance bound for the ball walk

Cousins-Vempala section 4.1 (`../gaussian-cooling-vempala/vol3_journal.tex:514-746`) bound the
conductance of the ball walk in three moves: a *one-step overlap* estimate, the
*separation* it forces, and an assembly against the isoperimetric inequality.  This file
carries out all three over the uniform ball walk built in
`Arlib/MarkovChains/Continuous/BallWalk.lean`, and adds the laziness bridge that
`Arlib/MarkovChains/Continuous/L2Mixing.lean` needs to turn the result into a mixing time.

## Proved unconditionally

* `midpoint_ball_subset_inter_ball`, `volume_ball_le_volume_inter_ball_add` — the geometry
  of two `delta`-balls at centre distance `t`: their intersection loses at most an
  `n·t/(2·delta)` fraction of the volume.  Elementary: a ball of radius `delta - t/2` about
  the midpoint sits inside both, and Bernoulli turns `(1 - t/(2·delta))^n` into
  `1 - n·t/(2·delta)`.
* `ell_le_ballWalk_add_ballWalk_compl` — **the one-step overlap bound**,
  `ell(u) ≤ P_u(T) + P_v(Tᶜ) + n·‖u-v‖/(2·delta)`.  Equivalently: the total-variation
  distance between the one-step distributions from `u` and from `v` is at most
  `1 - ell(u) + n‖u-v‖/(2·delta)`, so the two distributions overlap in mass at least
  `ell(u) - n‖u-v‖/(2·delta)`.  No convexity of `K`, no isoperimetry.
* `lt_dist_of_ballWalk_lt` — the separation `‖u-v‖ > theta·delta/n` that follows when
  `ell(u) ≥ theta` and neither step crosses with probability `theta/4`.
* `mul_measure_add_measure_le_mul_flow` — the flow accounting behind the paper's three-way
  partition, for an arbitrary reversible Markov kernel on an arbitrary measurable space.
* `ofReal_le_ell_unitBall` — `ell ≥ (1/2)^n` at every point of the unit ball, for steps
  `0 < delta ≤ 1`.  This is the **non-vacuity witness** for the local-conductance
  hypothesis below.
* `lazy`, `isReversible_lazy`, `neg_integral_sq_le_pairing_self`, `hasNonnegSpectrum_lazy`,
  `isReversible_and_hasNonnegSpectrum_lazy_ballWalk` — the laziness bridge.  The plain ball
  walk does *not* have nonnegative spectrum (its proposal operator is convolution with a
  ball indicator, whose Fourier transform changes sign); `lazy P x = (P x + delta_x)/2`
  does, because `⟪f,f⟫_{lazy P} = (‖f‖² + ⟪f,f⟫_P)/2` and `⟪f,f⟫_P ≥ -‖f‖²`.
* `conductanceOn_lazy`, `conductance_lazy` — **laziness halves the conductance, exactly**:
  `Φ(lazy P) = Φ(P)/2`.  The holding term contributes nothing to the escape flow and the
  admissible family `pi S ≤ 1/2` is a condition on `pi` alone, so the infimum goes through
  with no loss.  This is what lets the conductance bound and the mixing theorem compose.
* `exists_volume_inter_ball_pos_lt`, `exists_smallSet_uniformOn`,
  `rayleighSet_nonempty_of_smallSet` — the non-degeneracy the mixing theorem needs: a body
  of positive finite volume has a measurable piece of relative volume in `(0, 1/2]`, so the
  conductance is not the empty infimum `⊤` and `L²(pi)` contains a non-constant function.

## The end-to-end theorems

* `mixesWithin_lazy_ballWalk` — **the lazy ball walk on `K` mixes to total variation `eps`
  from an `M`-warm start** in `conductanceMixingTime M (min (θ/32) (κθ²δ/(128n))) eps` steps.
* `theorem2_of_lazy_ballWalk` — the same, composed with
  `Arlib.PointwiseRoute.theorem2_of_mixesWithin`: from an isoperimetric inequality for `K`
  to Kannan–Vempala Theorem 2's two-sided window on the rounding probability.
* `mixesWithin_lazy_ballWalk_unitBall` — the joint-satisfiability check (`CLAUDE.md` §11):
  every hypothesis except `hiso` discharged concretely on the unit ball.

## Assumed, and where

The **isoperimetric inequality is the only unproved input** anywhere in this file, and every
theorem that consumes it (`conductance_ballWalk_ge`, `mixesWithin_lazy_ballWalk`,
`theorem2_of_lazy_ballWalk`, `mixesWithin_lazy_ballWalk_unitBall`) takes it as an **inline
`∀`-hypothesis** (`hiso`) — not as a `def`, a `structure` field, or a named `Prop`.  A
reader of any of those theorems' types sees the inequality written out in full.  There is
exactly one `def` in this file (`lazy`, a plain kernel construction that names no
conductance, gap or mixing rate); everything else is a `theorem`.

Those theorems also carry `hell : ∀ x ∈ K, theta ≤ ell K delta x`, a uniform lower bound on
the local conductance.  Some such hypothesis is *forced*, not a proof artefact: near an
extreme point of a bounded `K` one has `ell ≲ 1/2`, and near a sharp corner much less, so
the plain uniform ball walk really does have small conductance there.  Cousins-Vempala
sidestep this by analysing the *speedy walk*, whose stationary density is proportional to
`ell`; that walk is not built in this library.  The paper's reading `theta = 3/4` is
**vacuous** for a bounded `K` — a supporting hyperplane at a boundary point forces
`ell ≤ 1/2` there — which is exactly why the results are parameterised by `theta`, with
`ofReal_le_ell_unitBall` as the witness that a positive `theta` is attainable.

## The two honest caveats, kept visible

1. **A factor `√n` worse than the paper.**  `thm:speedyconductance` gets separation
   `delta/√n` from the ball-cap estimate of [KLS95, Lemma 3.5]; Mathlib has no such
   estimate, and the elementary midpoint bound used here
   (`volume_ball_le_volume_inter_ball_add`) gets only `theta·delta/n`.  Everything
   downstream — the conductance, and hence the step count — therefore carries one extra
   factor of `√n`.  The gap is in the *geometry*, not in the Markov-chain argument.
2. **`hell` is forced, and its only proved witness is exponentially small.**  See above; the
   witness `ofReal_le_ell_unitBall` gives `theta = 2⁻ⁿ` on the unit ball, so the step count
   `mixesWithin_lazy_ballWalk` certifies with that witness is exponential in `n`.  A
   polynomial bound needs the speedy walk, which is not built here.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

variable {n : ℕ}

/-! ## 1. Ball-intersection geometry (unconditional) -/

/-- **The ball around the midpoint sits in the intersection.**  If `‖u - v‖ = t` then
`B(m, δ - t/2) ⊆ B(u, δ) ∩ B(v, δ)` for `m` the midpoint of `u` and `v`: the midpoint is
at distance `t/2` from each centre, so the triangle inequality does the rest.

This is the elementary substitute for the cap estimate of Kannan-Lovász-Simonovits
(Lemma 3.5 of [KLS95], cited at `vol3_journal.tex:592`); see the module docstring of
`overlap` below for what the substitution costs. -/
theorem midpoint_ball_subset_inter_ball (u v : EuclideanSpace ℝ (Fin n)) (δ : ℝ) :
    Metric.ball (midpoint ℝ u v) (δ - dist u v / 2)
      ⊆ Metric.ball u δ ∩ Metric.ball v δ := by
  have hu : dist (midpoint ℝ u v) u = dist u v / 2 := by
    rw [dist_midpoint_left]
    simp [div_eq_inv_mul]
  have hv : dist (midpoint ℝ u v) v = dist u v / 2 := by
    rw [dist_midpoint_right]
    simp [div_eq_inv_mul]
  intro x hx
  rw [Metric.mem_ball] at hx
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_ball]
    calc dist x u ≤ dist x (midpoint ℝ u v) + dist (midpoint ℝ u v) u := dist_triangle _ _ _
      _ < (δ - dist u v / 2) + dist u v / 2 := by rw [hu]; linarith
      _ = δ := by ring
  · rw [Metric.mem_ball]
    calc dist x v ≤ dist x (midpoint ℝ u v) + dist (midpoint ℝ u v) v := dist_triangle _ _ _
      _ < (δ - dist u v / 2) + dist u v / 2 := by rw [hv]; linarith
      _ = δ := by ring

/-- **Two `δ`-balls at distance `t` lose at most an `n·t/(2δ)` fraction of their volume by
intersecting.**

    vol(B(u,δ))  ≤  vol(B(u,δ) ∩ B(v,δ))  +  (n·t/(2δ))·vol(B(u,δ)),   t = ‖u - v‖.

`midpoint_ball_subset_inter_ball` puts a ball of radius `(1 - t/(2δ))·δ` inside the
intersection, Haar scaling turns that into a factor `(1 - t/(2δ))ⁿ`, and Bernoulli's
inequality (`one_add_mul_sub_le_pow`) turns *that* into `1 - n·t/(2δ)`.

The bound is stated additively rather than as `(1 - nt/(2δ))·vol ≤ vol(∩)` because
truncated `ℝ≥0∞` subtraction would lose the content when `n·t > 2δ`; in that regime the
statement above is trivially true, which is the right behaviour.  `1 ≤ n` is needed only
for that trivial regime. -/
theorem volume_ball_le_volume_inter_ball_add (hn : 1 ≤ n)
    (u v : EuclideanSpace ℝ (Fin n)) {δ : ℝ} (hδ : 0 < δ) :
    volume (Metric.ball u δ)
      ≤ volume (Metric.ball u δ ∩ Metric.ball v δ)
        + ENNReal.ofReal (n * dist u v / (2 * δ)) * volume (Metric.ball u δ) := by
  set t : ℝ := dist u v with ht
  have ht0 : 0 ≤ t := dist_nonneg
  have h2δ : (0:ℝ) < 2 * δ := by linarith
  by_cases hcase : 2 * δ ≤ t
  · -- degenerate regime: the correction term already exceeds the whole volume
    have h1 : (1:ℝ) ≤ n * t / (2 * δ) := by
      rw [le_div_iff₀ h2δ, one_mul]
      have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      nlinarith
    have h1' : (1:ℝ≥0∞) ≤ ENNReal.ofReal (n * t / (2 * δ)) := ENNReal.one_le_ofReal.2 h1
    calc volume (Metric.ball u δ) = 1 * volume (Metric.ball u δ) := (one_mul _).symm
      _ ≤ ENNReal.ofReal (n * t / (2 * δ)) * volume (Metric.ball u δ) := by gcongr
      _ ≤ _ := le_add_self
  · rw [not_le] at hcase
    set a : ℝ := 1 - t / (2 * δ) with ha
    have ha0 : 0 < a := by
      rw [ha, sub_pos, div_lt_one h2δ]; exact hcase
    have haδ : a * δ = δ - t / 2 := by
      rw [ha]; field_simp
    have hsub : Metric.ball (midpoint ℝ u v) (a * δ)
        ⊆ Metric.ball u δ ∩ Metric.ball v δ := by
      rw [haδ]; exact midpoint_ball_subset_inter_ball u v δ
    have hvol : volume (Metric.ball (midpoint ℝ u v) (a * δ))
        = ENNReal.ofReal (a ^ n) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ) := by
      have := Measure.addHaar_ball_mul_of_pos
        (volume : Measure (EuclideanSpace ℝ (Fin n))) (midpoint ℝ u v) ha0 δ
      rwa [finrank_euclideanSpace_fin] at this
    have hball : volume (Metric.ball u δ)
        = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ) := volume_ball_eq u δ
    -- Bernoulli
    have hbern : (1:ℝ) - n * t / (2 * δ) ≤ a ^ n := by
      have hm1 : (-1:ℝ) ≤ a := by
        rw [ha]
        have : t / (2 * δ) < 1 := (div_lt_one h2δ).2 hcase
        linarith
      have := one_add_mul_sub_le_pow hm1 n
      have hsub' : a - 1 = -(t / (2 * δ)) := by rw [ha]; ring
      rw [hsub'] at this
      have hd : (n:ℝ) * (-(t / (2 * δ))) = -(n * t / (2 * δ)) := by ring
      rw [hd] at this
      linarith
    have hkey : (1:ℝ) ≤ a ^ n + n * t / (2 * δ) := by linarith
    have hsum : (1:ℝ≥0∞) ≤ ENNReal.ofReal (a ^ n) + ENNReal.ofReal (n * t / (2 * δ)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.one_le_ofReal.2 hkey
    calc volume (Metric.ball u δ) = 1 * volume (Metric.ball u δ) := (one_mul _).symm
      _ ≤ (ENNReal.ofReal (a ^ n) + ENNReal.ofReal (n * t / (2 * δ)))
            * volume (Metric.ball u δ) := by gcongr
      _ = ENNReal.ofReal (a ^ n) * volume (Metric.ball u δ)
            + ENNReal.ofReal (n * t / (2 * δ)) * volume (Metric.ball u δ) := add_mul _ _ _
      _ ≤ volume (Metric.ball u δ ∩ Metric.ball v δ)
            + ENNReal.ofReal (n * t / (2 * δ)) * volume (Metric.ball u δ) := by
          gcongr
          rw [hball, ← hvol]
          exact measure_mono hsub

/-! ## 2. One-step overlap (unconditional)

The `lem:overlap` of `vol3_journal.tex:582`, in the form the uniform ball walk needs.
No convexity of `K` is used, and no isoperimetric input. -/

/-- **The one-step overlap bound.**  For any two points `u, v` and any measurable event `T`,

    ℓ(u)  ≤  P_u(T) + P_v(Tᶜ) + n·‖u - v‖/(2δ).

Read `P_u(T) + P_v(Tᶜ)` as `1 - (P_u(T) - P_v(T))`: taking the infimum over `T` on the
right, the inequality says that the total-variation distance between the one-step
distributions from `u` and from `v` is at most `1 - ℓ(u) + n‖u-v‖/(2δ)`.  So the two
one-step distributions overlap in mass at least `ℓ(u) - n‖u-v‖/(2δ)`, which is bounded
away from `0` as soon as `u` is a speedy point and `‖u - v‖ ≲ δ/n`.

The proof is the paper's, with the ball-intersection estimate replaced by the elementary
`volume_ball_le_volume_inter_ball_add`: both one-step distributions dominate the uniform
measure on `C = B(u,δ) ∩ B(v,δ)` intersected with `K`, the two events `T` and `Tᶜ` cut
`C ∩ K` into two pieces, and `C ∩ K` misses `B(u,δ) ∩ K` by at most `vol(B(u,δ)) - vol(C)`.

**What this costs against Cousins-Vempala.**  The paper uses Lemma 3.5 of [KLS95]
(`vol3_journal.tex:592`), whose cap estimate keeps a constant fraction of the ball at
separation `‖u-v‖ ≤ δ/√n`; the elementary midpoint bound used here only keeps a constant
fraction at separation `‖u-v‖ ≲ δ/n`.  Everything downstream therefore carries `δ/n`
where the paper carries `δ/√n`, a loss of one factor of `√n` in the final conductance.
That is the single quantitative gap between this file and `thm:speedyconductance`, and it
is a gap in the *geometry*, not in the Markov-chain argument. -/
theorem ell_le_ballWalk_add_ballWalk_compl (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) {δ : ℝ} (hδ : 0 < δ)
    (u v : EuclideanSpace ℝ (Fin n)) {T : Set (EuclideanSpace ℝ (Fin n))}
    (hT : MeasurableSet T) :
    ell K δ u ≤ ballWalk K δ u T + ballWalk K δ v Tᶜ
      + ENNReal.ofReal (n * dist u v / (2 * δ)) := by
  set vb : ℝ≥0∞ := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ) with hvb
  have hvb0 : vb ≠ 0 := (Metric.measure_ball_pos volume 0 hδ).ne'
  have hvbtop : vb ≠ ⊤ := measure_ball_lt_top.ne
  have hbu : volume (Metric.ball u δ) = vb := volume_ball_eq u δ
  have hbv : volume (Metric.ball v δ) = vb := volume_ball_eq v δ
  set C : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball u δ ∩ Metric.ball v δ with hC
  have hCm : MeasurableSet C := measurableSet_ball.inter measurableSet_ball
  have hCu : C ⊆ Metric.ball u δ := Set.inter_subset_left
  have hCv : C ⊆ Metric.ball v δ := Set.inter_subset_right
  have hCtop : volume C ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono hCu)
    rw [hbu]; exact hvbtop
  -- the two one-step distributions both dominate the uniform measure on `C ∩ K`
  have h1 : vb⁻¹ * volume (T ∩ (C ∩ K)) ≤ ballWalk K δ u T := by
    rw [ballWalk_apply_set hK δ u hT, hbu]
    calc vb⁻¹ * volume (T ∩ (C ∩ K))
        ≤ vb⁻¹ * volume (T ∩ (Metric.ball u δ ∩ K)) := by gcongr
      _ ≤ _ := le_self_add
  have h2 : vb⁻¹ * volume (Tᶜ ∩ (C ∩ K)) ≤ ballWalk K δ v Tᶜ := by
    rw [ballWalk_apply_set hK δ v hT.compl, hbv]
    calc vb⁻¹ * volume (Tᶜ ∩ (C ∩ K))
        ≤ vb⁻¹ * volume (Tᶜ ∩ (Metric.ball v δ ∩ K)) := by gcongr
      _ ≤ _ := le_self_add
  have h3 : volume (T ∩ (C ∩ K)) + volume (Tᶜ ∩ (C ∩ K)) = volume (C ∩ K) := by
    have h := measure_inter_add_sdiff (μ := volume) (C ∩ K) hT
    rwa [Set.inter_comm (C ∩ K) T, Set.sdiff_eq, Set.inter_comm (C ∩ K) Tᶜ] at h
  have hsum : vb⁻¹ * volume (C ∩ K) ≤ ballWalk K δ u T + ballWalk K δ v Tᶜ := by
    rw [← h3, mul_add]
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
  calc vb⁻¹ * volume (Metric.ball u δ ∩ K)
      ≤ vb⁻¹ * (volume (C ∩ K) + ENNReal.ofReal (n * dist u v / (2 * δ)) * vb) := by gcongr
    _ = vb⁻¹ * volume (C ∩ K) + ENNReal.ofReal (n * dist u v / (2 * δ)) := by
        rw [mul_add, hcancel]
    _ ≤ (ballWalk K δ u T + ballWalk K δ v Tᶜ)
          + ENNReal.ofReal (n * dist u v / (2 * δ)) := by gcongr

/-! ## 3. Separation: points a step rarely crosses between are far apart (unconditional) -/

/-- **Separation from overlap.**  Suppose `ℓ(u) ≥ θ`, the step from `u` enters `T` with
probability less than `θ/4`, and the step from `v` enters `Tᶜ` with probability less than
`θ/4`.  Then `‖u - v‖ > θ·δ/n`.

This is the dichotomy at `vol3_journal.tex:657` ("for any `u ∈ S₁, v ∈ S₂`, either
`‖u-v‖ ≥ δ/√n` or `d_h(u,v) ≥ 1/4`"), in the form the *uniform* ball walk gives it: there
is no `d_h` alternative here because the lower bound on `ℓ(u)` is carried directly, and
`δ/√n` becomes `θ·δ/n` for the reason recorded in `ell_le_ballWalk_add_ballWalk_compl`.
Taking `θ = 3/4` recovers the paper's speedy threshold, i.e. `u ∈ SpeedyPoints K δ`.

The thresholds are written multiplicatively (`4 * p < θ` rather than `p < θ/4`) purely to
keep the `ℝ≥0∞` arithmetic division-free. -/
theorem lt_dist_of_ballWalk_lt (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) {δ : ℝ} (hδ : 0 < δ) {θ : ℝ}
    {u v : EuclideanSpace ℝ (Fin n)} {T : Set (EuclideanSpace ℝ (Fin n))}
    (hT : MeasurableSet T) (hu : ENNReal.ofReal θ ≤ ell K δ u)
    (hu' : 4 * ballWalk K δ u T < ENNReal.ofReal θ)
    (hv' : 4 * ballWalk K δ v Tᶜ < ENNReal.ofReal θ) :
    θ * δ / (n : ℝ) < dist u v := by
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hov := ell_le_ballWalk_add_ballWalk_compl hn hK hδ u v hT
  have hΘ := hu.trans hov
  have hXtop : (4:ℝ≥0∞) * ENNReal.ofReal ((n:ℝ) * dist u v / (2 * δ)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  have hΘtop : (2:ℝ≥0∞) * ENNReal.ofReal θ ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  have hstep : (2:ℝ≥0∞) * ENNReal.ofReal θ + 2 * ENNReal.ofReal θ
      < 2 * ENNReal.ofReal θ + 4 * ENNReal.ofReal ((n:ℝ) * dist u v / (2 * δ)) := by
    calc (2:ℝ≥0∞) * ENNReal.ofReal θ + 2 * ENNReal.ofReal θ
        = 4 * ENNReal.ofReal θ := by ring
      _ ≤ 4 * (ballWalk K δ u T + ballWalk K δ v Tᶜ
            + ENNReal.ofReal ((n:ℝ) * dist u v / (2 * δ))) := by gcongr
      _ = 4 * ballWalk K δ u T + 4 * ballWalk K δ v Tᶜ
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

/-! ## 4. From overlap to flow: the three-way partition (unconditional) -/

/-- **The escape flow dominates the mass that is not stuck.**  Let `S` be measurable, and
let `A`, `B` be *any* two measurable sets such that every `x ∈ S \ A` escapes into `Sᶜ`
with probability at least `e/c`, and every `x ∈ Sᶜ \ B` escapes into `S` with probability
at least `e/c`.  Then

    e·(π(S \ A) + π(Sᶜ \ B))  ≤  2·c·flow(S, Sᶜ).

This is the display at `vol3_journal.tex:660`, with `S \ A` and `Sᶜ \ B` the two halves of
the paper's `S₃`.  Reversibility is what lets the second integral — a flow *into* `S` — be
charged to the escape flow *out of* `S`.

There is no geometry here: this holds for every reversible Markov kernel on every
measurable space.  The escape probability is written `e ≤ c * P x Sᶜ` rather than
`e/c ≤ P x Sᶜ` to keep the `ℝ≥0∞` arithmetic division-free. -/
theorem mul_measure_add_measure_le_mul_flow {Om : Type*} [MeasurableSpace Om]
    (P : Kernel Om Om) [IsMarkovKernel P] (pi : Measure Om) (hrev : IsReversible P pi)
    {S A B : Set Om} (hS : MeasurableSet S) (hA : MeasurableSet A) (hB : MeasurableSet B)
    {e c : ℝ≥0∞} (hA' : ∀ x ∈ S \ A, e ≤ c * P x Sᶜ) (hB' : ∀ x ∈ Sᶜ \ B, e ≤ c * P x S) :
    e * (pi (S \ A) + pi (Sᶜ \ B)) ≤ 2 * (c * flow P pi S Sᶜ) := by
  have e1 : e * pi (S \ A) ≤ c * flow P pi S Sᶜ := by
    calc e * pi (S \ A) = ∫⁻ _ in S \ A, e ∂pi := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in S \ A, c * P x Sᶜ ∂pi := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem (hS.diff hA)] with x hx using hA' x hx
      _ = c * ∫⁻ x in S \ A, P x Sᶜ ∂pi :=
          lintegral_const_mul c (Kernel.measurable_coe P hS.compl)
      _ ≤ c * ∫⁻ x in S, P x Sᶜ ∂pi := by
          gcongr
          exact Set.sdiff_subset
      _ = c * flow P pi S Sᶜ := by rw [flow_apply]
  have e2 : e * pi (Sᶜ \ B) ≤ c * flow P pi S Sᶜ := by
    calc e * pi (Sᶜ \ B) = ∫⁻ _ in Sᶜ \ B, e ∂pi := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in Sᶜ \ B, c * P x S ∂pi := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem (hS.compl.diff hB)] with x hx using hB' x hx
      _ = c * ∫⁻ x in Sᶜ \ B, P x S ∂pi :=
          lintegral_const_mul c (Kernel.measurable_coe P hS)
      _ ≤ c * ∫⁻ x in Sᶜ, P x S ∂pi := by
          gcongr
          exact Set.sdiff_subset
      _ = c * flow P pi Sᶜ S := by rw [flow_apply]
      _ = c * flow P pi S Sᶜ := by rw [hrev _ _ hS.compl hS]
  calc e * (pi (S \ A) + pi (Sᶜ \ B)) = e * pi (S \ A) + e * pi (Sᶜ \ B) := mul_add _ _ _
    _ ≤ c * flow P pi S Sᶜ + c * flow P pi S Sᶜ := add_le_add e1 e2
    _ = 2 * (c * flow P pi S Sᶜ) := (two_mul _).symm

/-! ## 5. The conductance bound

The single theorem in this file that consumes an unproved input.  The input is the
isoperimetric inequality for the uniform measure on `K`, and it is written out **inline, as
a `∀`-hypothesis of the theorem**, so that a reader of the theorem's type sees exactly what
is assumed.  It is deliberately *not* a `def`, a `structure` field, or a named `Prop`: a
name would hide the assumption both from the reader and from any audit of what the file
proves, which is the failure mode `CV-ROADMAP.md` section 2a records for the sibling
development's `IsoInput`. -/

/-- **The conductance of the ball walk, given an isoperimetric inequality for `K`.**

    Φ(ball walk on K with δ-steps)  ≥  min(θ/16, κ·θ²·δ/(64·n)).

Two hypotheses carry content; both are written out inline.

* `hiso` — **the isoperimetric inequality**, spelled out: *for every `d > 0` and every pair
  of measurable subsets `A, B ⊆ K` all of whose points are at distance at least `d` from
  one another, what is left of `K` has mass at least `κ·d·π(A)·π(B)`.*  Nothing in this
  file proves it; Mathlib has no isoperimetric inequality for log-concave densities and
  `CV-ROADMAP.md` section 3 records why.  The theorem is stated for an arbitrary `κ`, so
  a caller who can prove the inequality with their own constant gets the bound with it.

* `hell` — **a uniform lower bound `ℓ(x) ≥ θ` on the local conductance of `K`.**  This is
  not cosmetic.  Some such hypothesis is *forced*: for a bounded `K`, points near an
  extreme point in any direction have `ℓ(x) ≲ 1/2`, and near a sharp corner `ℓ` is smaller
  still, so the plain uniform ball walk genuinely has small conductance there.
  Cousins-Vempala's `thm:speedyconductance` avoids this by analysing the *speedy walk*,
  whose stationary density is proportional to `ℓ` and which therefore reweights the slow
  points away rather than assuming them absent; that walk is not built in this library.
  Taking `θ = 3/4` is the paper's `SpeedyPoints` threshold, but note that `θ = 3/4` is
  *unsatisfiable* for a body with boundary — the hypothesis has content only for smaller
  `θ`.  `ofReal_le_ell_unitBall` below discharges it on the unit ball with `θ = 2⁻ⁿ`, which
  is what keeps the theorem from being vacuous.

The remaining hypotheses are the standing non-degeneracy guards: `1 ≤ n`, `K` measurable
with `0 < vol(K) < ∞` (so `Arlib.uniformOn volume K` is a probability measure), `0 < δ`,
and `0 < θ`.

Against the paper (`vol3_journal.tex:746`, `Φ ≥ δ/(250·σ·√n)`): the shape
`min(constant, κ·d/constant)` is the same, and `θ/16` plays the role of the paper's `1/80`.
The one quantitative gap is `d = θδ/n` in place of `δ/√n`, and it comes entirely from the
elementary ball-intersection estimate — see `ell_le_ballWalk_add_ballWalk_compl`. -/
theorem conductance_ballWalk_ge (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤) {δ : ℝ} (hδ : 0 < δ)
    {θ : ℝ} (hθ : 0 < θ)
    (hell : ∀ x ∈ K, ENNReal.ofReal θ ≤ ell K δ x) {kappa : ℝ≥0∞}
    (hiso : ∀ d : ℝ, 0 < d → ∀ A B : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet A → MeasurableSet B → A ⊆ K → B ⊆ K →
      (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) →
      kappa * ENNReal.ofReal d * Arlib.uniformOn volume K A * Arlib.uniformOn volume K B
        ≤ Arlib.uniformOn volume K ((K \ A) \ B)) :
    min (ENNReal.ofReal θ / 16) (kappa * ENNReal.ofReal (θ ^ 2 * δ / (n : ℝ)) / 64)
      ≤ conductance (ballWalk K δ) (Arlib.uniformOn volume K) := by
  haveI : IsProbabilityMeasure (Arlib.uniformOn volume K) :=
    Arlib.isProbabilityMeasure_uniformOn volume hK0 hKtop
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdpos : (0:ℝ) < θ * δ / (n : ℝ) := by positivity
  have hmul : ENNReal.ofReal θ * ENNReal.ofReal (θ * δ / (n : ℝ))
      = ENNReal.ofReal (θ ^ 2 * δ / (n : ℝ)) := by
    rw [← ENNReal.ofReal_mul hθ.le]
    congr 1
    ring
  have hrev : IsReversible (ballWalk K δ) (Arlib.uniformOn volume K) :=
    isReversible_ballWalk hK δ
  have hKc : Arlib.uniformOn volume K Kᶜ = 0 := Arlib.uniformOn_compl_eq_zero volume hK
  set pi : Measure (EuclideanSpace ℝ (Fin n)) := Arlib.uniformOn volume K with hpidef
  set P : Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
    ballWalk K δ with hPdef
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
  -- the paper's `S₁` and `S₂`: the points a step almost never moves across
  set S1 : Set (EuclideanSpace ℝ (Fin n)) :=
    (S ∩ K) ∩ {x | 4 * P x Sᶜ < ENNReal.ofReal θ} with hS1def
  set S2 : Set (EuclideanSpace ℝ (Fin n)) :=
    (K \ S) ∩ {x | 4 * P x S < ENNReal.ofReal θ} with hS2def
  have hS1m : MeasurableSet S1 :=
    (hSm.inter hK).inter
      (measurableSet_lt ((Kernel.measurable_coe P hSm.compl).const_mul 4) measurable_const)
  have hS2m : MeasurableSet S2 :=
    (hK.diff hSm).inter
      (measurableSet_lt ((Kernel.measurable_coe P hSm).const_mul 4) measurable_const)
  have hmem1 : ∀ x, x ∈ S1 ↔ ((x ∈ S ∧ x ∈ K) ∧ 4 * P x Sᶜ < ENNReal.ofReal θ) := by
    intro x
    rw [hS1def]
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  have hmem2 : ∀ x, x ∈ S2 ↔ ((x ∈ K ∧ x ∉ S) ∧ 4 * P x S < ENNReal.ofReal θ) := by
    intro x
    rw [hS2def]
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_setOf_eq]
  have hS1K : S1 ⊆ K := fun x hx => ((hmem1 x).1 hx).1.2
  have hS2K : S2 ⊆ K := fun x hx => ((hmem2 x).1 hx).1.1
  -- the flow bound
  have hSA : S \ (S1 ∪ Kᶜ) = (S ∩ K) \ S1 := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff]
    tauto
  have hSB : Sᶜ \ (S2 ∪ Kᶜ) = (K \ S) \ S2 := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_compl_iff]
    tauto
  have hA' : ∀ x ∈ S \ (S1 ∪ Kᶜ), ENNReal.ofReal θ ≤ 4 * P x Sᶜ := by
    rw [hSA]
    rintro x ⟨⟨hxS, hxK⟩, hxS1⟩
    by_contra hc
    rw [not_le] at hc
    exact hxS1 ((hmem1 x).2 ⟨⟨hxS, hxK⟩, hc⟩)
  have hB' : ∀ x ∈ Sᶜ \ (S2 ∪ Kᶜ), ENNReal.ofReal θ ≤ 4 * P x S := by
    rw [hSB]
    rintro x ⟨⟨hxK, hxS⟩, hxS2⟩
    by_contra hc
    rw [not_le] at hc
    exact hxS2 ((hmem2 x).2 ⟨⟨hxK, hxS⟩, hc⟩)
  have hflow : ENNReal.ofReal θ * (pi ((S ∩ K) \ S1) + pi ((K \ S) \ S2))
      ≤ 2 * (4 * flow P pi S Sᶜ) := by
    have h := mul_measure_add_measure_le_mul_flow P pi hrev hSm (hS1m.union hK.compl)
      (hS2m.union hK.compl) hA' hB'
    rwa [hSA, hSB] at h
  -- the leftover part of `K`
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
  -- the separation, from section 3
  have hsep : ∀ u ∈ S1, ∀ v ∈ S2, θ * δ / (n : ℝ) ≤ dist u v := by
    intro u hu v hv
    have hu8 : 4 * ballWalk K δ u Sᶜ < ENNReal.ofReal θ := by
      have h := ((hmem1 u).1 hu).2
      rwa [hPdef] at h
    have hv8 : 4 * ballWalk K δ v Sᶜᶜ < ENNReal.ofReal θ := by
      have h := ((hmem2 v).1 hv).2
      rw [hPdef] at h
      rwa [compl_compl]
    exact (lt_dist_of_ballWalk_lt hn hK hδ hSm.compl (hell u (hS1K hu)) hu8 hv8).le
  -- the two branches
  have hkey : ENNReal.ofReal θ * pi S ≤ 16 * flow P pi S Sᶜ
      ∨ kappa * ENNReal.ofReal (θ ^ 2 * δ / (n : ℝ)) * pi S ≤ 64 * flow P pi S Sᶜ := by
    by_cases hc1 : pi S ≤ 2 * pi ((S ∩ K) \ S1)
    · left
      calc ENNReal.ofReal θ * pi S
          ≤ ENNReal.ofReal θ * (2 * pi ((S ∩ K) \ S1)) := by gcongr
        _ = 2 * (ENNReal.ofReal θ * pi ((S ∩ K) \ S1)) := by ring
        _ ≤ 2 * (ENNReal.ofReal θ * (pi ((S ∩ K) \ S1) + pi ((K \ S) \ S2))) := by
            gcongr
            exact le_self_add
        _ ≤ 2 * (2 * (4 * flow P pi S Sᶜ)) := by gcongr
        _ = 16 * flow P pi S Sᶜ := by ring
    by_cases hc2 : pi Sᶜ ≤ 2 * pi ((K \ S) \ S2)
    · left
      calc ENNReal.ofReal θ * pi S
          ≤ ENNReal.ofReal θ * pi Sᶜ := mul_le_mul_right (hShalf.trans hSc) _
        _ ≤ ENNReal.ofReal θ * (2 * pi ((K \ S) \ S2)) := by gcongr
        _ = 2 * (ENNReal.ofReal θ * pi ((K \ S) \ S2)) := by ring
        _ ≤ 2 * (ENNReal.ofReal θ * (pi ((S ∩ K) \ S1) + pi ((K \ S) \ S2))) := by
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
    have hisoS := hiso (θ * δ / (n : ℝ)) hdpos S1 S2 hS1m hS2m hS1K hS2K hsep
    calc kappa * ENNReal.ofReal (θ ^ 2 * δ / (n : ℝ)) * pi S
        = ENNReal.ofReal θ * (kappa * ENNReal.ofReal (θ * δ / (n : ℝ)) * pi S) := by
          rw [← hmul]; ring
      _ ≤ ENNReal.ofReal θ *
            (kappa * ENNReal.ofReal (θ * δ / (n : ℝ)) * (8 * (pi S1 * pi S2))) := by gcongr
      _ = 8 * (ENNReal.ofReal θ *
            (kappa * ENNReal.ofReal (θ * δ / (n : ℝ)) * pi S1 * pi S2)) := by ring
      _ ≤ 8 * (ENNReal.ofReal θ * pi ((K \ S1) \ S2)) := by gcongr
      _ ≤ 8 * (ENNReal.ofReal θ * (pi ((S ∩ K) \ S1) + pi ((K \ S) \ S2))) := by gcongr
      _ ≤ 8 * (2 * (4 * flow P pi S Sᶜ)) := by gcongr
      _ = 64 * flow P pi S Sᶜ := by ring
  have hswap : ∀ a b c : ℝ≥0∞, a / c * b = a * b / c := by
    intro a b c
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]
  rw [conductanceOn_apply, ENNReal.le_div_iff_mul_le (Or.inl hSpos.ne') (Or.inl hpitop)]
  rcases hkey with h | h
  · calc min (ENNReal.ofReal θ / 16)
            (kappa * ENNReal.ofReal (θ ^ 2 * δ / (n : ℝ)) / 64) * pi S
        ≤ ENNReal.ofReal θ / 16 * pi S := by gcongr; exact min_le_left _ _
      _ = ENNReal.ofReal θ * pi S / 16 := hswap _ _ _
      _ ≤ flow P pi S Sᶜ := by
          rw [ENNReal.div_le_iff_le_mul (Or.inl (by norm_num)) (Or.inl (by norm_num))]
          exact h.trans_eq (mul_comm _ _)
  · calc min (ENNReal.ofReal θ / 16)
            (kappa * ENNReal.ofReal (θ ^ 2 * δ / (n : ℝ)) / 64) * pi S
        ≤ kappa * ENNReal.ofReal (θ ^ 2 * δ / (n : ℝ)) / 64 * pi S := by
          gcongr; exact min_le_right _ _
      _ = kappa * ENNReal.ofReal (θ ^ 2 * δ / (n : ℝ)) * pi S / 64 := hswap _ _ _
      _ ≤ flow P pi S Sᶜ := by
          rw [ENNReal.div_le_iff_le_mul (Or.inl (by norm_num)) (Or.inl (by norm_num))]
          exact h.trans_eq (mul_comm _ _)

/-! ## 6. Non-vacuity: the local-conductance hypothesis is satisfiable -/

/-- **Every point of the open unit ball is `2⁻ⁿ`-speedy** for steps `0 < δ ≤ 1`:
`ℓ(x) ≥ (1/2)ⁿ`.

The witness is a single ball.  For `x` in the unit ball put `w = (1 - δ/2)·x`.  Then
`‖w - x‖ = (δ/2)‖x‖ < δ/2`, so `B(w, δ/2) ⊆ B(x, δ)`; and `‖w‖ + δ/2 = (1-δ/2)‖x‖ + δ/2 < 1`,
so `B(w, δ/2)` is inside the unit ball as well.  Haar scaling turns the radius ratio `1/2`
into the volume ratio `(1/2)ⁿ`.

This is what keeps the `hell` hypothesis of `conductance_ballWalk_ge` from being vacuous:
it is satisfiable with `θ = (1/2)ⁿ` on a body of positive finite volume.  The constant is
exponentially small and far from optimal — for the unit ball the truth is `ℓ ≥ 1/2 - o(1)`
— but it is positive, which is what non-vacuity needs.  It also shows why the theorem is
stated for a general `θ` rather than for the paper's `3/4`: no body with boundary satisfies
`ℓ ≥ 3/4` everywhere, since a supporting hyperplane at a boundary point forces `ℓ ≤ 1/2`
there. -/
theorem ofReal_le_ell_unitBall {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ENNReal.ofReal (((1:ℝ) / 2) ^ n)
      ≤ ell (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ x := by
  have hxn : ‖x‖ < 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hx
  have hδ2 : (0:ℝ) < δ / 2 := by linarith
  have hc : (0:ℝ) < 1 - δ / 2 := by linarith
  set w : EuclideanSpace ℝ (Fin n) := (1 - δ / 2) • x with hw
  have hwsub : w - x = (-(δ / 2)) • x := by
    rw [hw]; module
  have hwx : dist w x = δ / 2 * ‖x‖ := by
    rw [dist_eq_norm, hwsub, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hδ2]
  have hwnorm : ‖w‖ = (1 - δ / 2) * ‖x‖ := by
    rw [hw, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have hwx' : dist w x < δ / 2 := by
    rw [hwx]; nlinarith [norm_nonneg x]
  have hsub : Metric.ball w (δ / 2)
      ⊆ Metric.ball x δ ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    intro y hy
    rw [Metric.mem_ball] at hy
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball]
      calc dist y x ≤ dist y w + dist w x := dist_triangle _ _ _
        _ < δ / 2 + δ / 2 := by linarith
        _ = δ := by ring
    · rw [Metric.mem_ball]
      have hw0 : dist w (0 : EuclideanSpace ℝ (Fin n)) = (1 - δ / 2) * ‖x‖ := by
        rw [dist_zero_right, hwnorm]
      have hlt : (1 - δ / 2) * ‖x‖ < (1 - δ / 2) * 1 := by nlinarith
      calc dist y (0 : EuclideanSpace ℝ (Fin n))
          ≤ dist y w + dist w (0 : EuclideanSpace ℝ (Fin n)) := dist_triangle _ _ _
        _ < δ / 2 + (1 - δ / 2) * 1 := by rw [hw0]; linarith
        _ = 1 := by ring
  have hbx0 : volume (Metric.ball x δ) ≠ 0 := (Metric.measure_ball_pos volume x hδ).ne'
  have hbxt : volume (Metric.ball x δ) ≠ ⊤ := measure_ball_lt_top.ne
  have hvw : volume (Metric.ball w (δ / 2))
      = ENNReal.ofReal ((δ / 2) ^ n)
        * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    have h := Measure.addHaar_ball_of_pos
      (volume : Measure (EuclideanSpace ℝ (Fin n))) w hδ2
    rwa [finrank_euclideanSpace_fin] at h
  have hvx : volume (Metric.ball x δ)
      = ENNReal.ofReal (δ ^ n)
        * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    have h := Measure.addHaar_ball_of_pos
      (volume : Measure (EuclideanSpace ℝ (Fin n))) x hδ
    rwa [finrank_euclideanSpace_fin] at h
  have hpow : ((1:ℝ) / 2) ^ n * δ ^ n = (δ / 2) ^ n := by
    rw [← mul_pow]; ring_nf
  rw [ell_apply, ENNReal.le_div_iff_mul_le (Or.inl hbx0) (Or.inl hbxt)]
  calc ENNReal.ofReal (((1:ℝ) / 2) ^ n) * volume (Metric.ball x δ)
      = ENNReal.ofReal ((δ / 2) ^ n)
          * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
        rw [hvx, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hpow]
    _ = volume (Metric.ball w (δ / 2)) := hvw.symm
    _ ≤ volume (Metric.ball x δ ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
        measure_mono hsub

/-! ## 7. Laziness, and the nonnegative-spectrum hypothesis

`Arlib.MarkovChains.mixesWithin_of_conductance` (`L2Mixing.lean`) turns a conductance lower
bound into a mixing time, but it needs `Arlib.MarkovChains.HasNonnegSpectrum`.  The ball
walk does **not** have it: its proposal operator is convolution with the indicator of a
ball, whose Fourier transform is a Bessel function and changes sign.  What repairs it is
laziness, and this section supplies the bridge.

Nothing here mentions a conductance, a spectral gap or a mixing rate: `lazy` is a plain
kernel construction, and `hasNonnegSpectrum_lazy` is a theorem about it. -/

section Lazy

variable {Om : Type*} [MeasurableSpace Om]

/-- **The pairing is a contraction from below**: `-∫ f² ≤ ⟪f, f⟫_P`.

Pointwise `f(x)·f(y) ≥ -(f(x)² + f(y)²)/2`, and both marginals of `pi ⊗ₘ P` are `pi` — the
second one by reversibility — so the right-hand side integrates to exactly `-∫ f²`.  This
is the whole analytic content of `hasNonnegSpectrum_lazy`. -/
theorem neg_integral_sq_le_pairing_self {P : Kernel Om Om} [IsMarkovKernel P]
    {pi : Measure Om} [IsProbabilityMeasure pi] (hrev : IsReversible P pi) {f : Om → ℝ}
    (hf : Measurable f) (hmem : MemLp f 2 pi) :
    -∫ x, f x ^ 2 ∂pi ≤ pairing P pi f f := by
  have I11 : Integrable (fun p : Om × Om => f p.1 * f p.2) (pi ⊗ₘ P) :=
    integrable_mul_compProd hrev hf hf hmem hmem
  have h1 : Integrable (fun p : Om × Om => f p.1 ^ 2) (pi ⊗ₘ P) :=
    integrable_comp_fst (hf.pow_const 2) hmem.integrable_sq
  have h2 : Integrable (fun p : Om × Om => f p.2 ^ 2) (pi ⊗ₘ P) :=
    integrable_comp_snd hrev (hf.pow_const 2) hmem.integrable_sq
  have hle : ∫ p : Om × Om, -((f p.1 ^ 2 + f p.2 ^ 2) / 2) ∂(pi ⊗ₘ P)
      ≤ ∫ p : Om × Om, f p.1 * f p.2 ∂(pi ⊗ₘ P) := by
    refine integral_mono ((h1.add h2).div_const 2).neg I11 fun p => ?_
    nlinarith [sq_nonneg (f p.1 + f p.2)]
  have hcalc : ∫ p : Om × Om, -((f p.1 ^ 2 + f p.2 ^ 2) / 2) ∂(pi ⊗ₘ P)
      = -∫ x, f x ^ 2 ∂pi := by
    rw [integral_neg, integral_div, integral_add h1 h2,
      integral_comp_fst (P := P) (hf.pow_const 2),
      integral_comp_snd hrev (hf.pow_const 2)]
    ring
  rw [pairing_apply]
  rw [hcalc] at hle
  exact hle

/-- **The lazy version of a kernel**: with probability `1/2` take a `P`-step, otherwise stay
put.  `lazy P x = (P x + δ_x)/2`.

A plain kernel construction — it names no conductance, no spectral gap, and no mixing
rate. -/
noncomputable def lazy (P : Kernel Om Om) : Kernel Om Om where
  toFun x := (2:ℝ≥0∞)⁻¹ • P x + (2:ℝ≥0∞)⁻¹ • Measure.dirac x
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun t ht => ?_
    have hrw : ∀ x : Om, ((2:ℝ≥0∞)⁻¹ • P x + (2:ℝ≥0∞)⁻¹ • Measure.dirac x) t
        = (2:ℝ≥0∞)⁻¹ * P x t + (2:ℝ≥0∞)⁻¹ * t.indicator 1 x := by
      intro x
      rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
        Measure.dirac_apply' _ ht]
    simp_rw [hrw]
    exact ((Kernel.measurable_coe P ht).const_mul _).add
      ((measurable_one.indicator ht).const_mul _)

/-- Unfolding lemma for `lazy`. -/
theorem lazy_apply (P : Kernel Om Om) (x : Om) :
    lazy P x = (2:ℝ≥0∞)⁻¹ • P x + (2:ℝ≥0∞)⁻¹ • Measure.dirac x := rfl

/-- The value of `lazy P` on a measurable event. -/
theorem lazy_apply_set (P : Kernel Om Om) (x : Om) {t : Set Om} (ht : MeasurableSet t) :
    lazy P x t = (2:ℝ≥0∞)⁻¹ * P x t + (2:ℝ≥0∞)⁻¹ * t.indicator 1 x := by
  rw [lazy_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
    smul_eq_mul, Measure.dirac_apply' _ ht]

/-- **`lazy P` is a Markov kernel**: its mass is `1/2 + 1/2`. -/
instance isMarkovKernel_lazy (P : Kernel Om Om) [IsMarkovKernel P] :
    IsMarkovKernel (lazy P) := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [lazy_apply_set P x MeasurableSet.univ, measure_univ,
    Set.indicator_of_mem (Set.mem_univ x), Pi.one_apply, mul_one]
  exact ENNReal.inv_two_add_inv_two

/-- **The flow of `lazy P`** splits into half the flow of `P` and half the mass that stays
put. -/
theorem flow_lazy (P : Kernel Om Om) (pi : Measure Om) (S : Set Om) {T : Set Om}
    (hT : MeasurableSet T) :
    flow (lazy P) pi S T = (2:ℝ≥0∞)⁻¹ * flow P pi S T + (2:ℝ≥0∞)⁻¹ * pi (T ∩ S) := by
  have hrw : ∀ x : Om, lazy P x T = (2:ℝ≥0∞)⁻¹ * P x T + (2:ℝ≥0∞)⁻¹ * T.indicator 1 x :=
    fun x => lazy_apply_set P x hT
  have hind : ∫⁻ x in S, T.indicator (1 : Om → ℝ≥0∞) x ∂pi = pi (T ∩ S) := by
    rw [lintegral_indicator hT]
    simp [Measure.restrict_apply hT]
  rw [flow, flow]
  simp_rw [hrw]
  rw [lintegral_add_left ((Kernel.measurable_coe P hT).const_mul _),
    lintegral_const_mul _ (Kernel.measurable_coe P hT),
    lintegral_const_mul _ (measurable_one.indicator hT), hind]

/-- **`lazy P` inherits detailed balance from `P`.**  Half the flow of `P` is symmetric
because `P`'s is; the other half is `pi(T ∩ S)`, which is symmetric outright. -/
theorem isReversible_lazy {P : Kernel Om Om} {pi : Measure Om} (h : IsReversible P pi) :
    IsReversible (lazy P) pi := by
  intro S T hS hT
  rw [flow_lazy P pi S hT, flow_lazy P pi T hS, h S T hS hT, Set.inter_comm]

/-- **Laziness halves the conductance of every set, exactly.**

    Φ_{lazy P}(S)  =  Φ_P(S) / 2.

The holding term contributes nothing to the escape flow — `flow_lazy` charges it
`pi (Sᶜ ∩ S) = pi ∅ = 0` — so only the factor `1/2` in front of the `P`-flow survives, and
the denominator `pi S` is untouched because `lazy P` has the same stationary measure. -/
theorem conductanceOn_lazy (P : Kernel Om Om) (pi : Measure Om) {S : Set Om}
    (hS : MeasurableSet S) :
    conductanceOn (lazy P) pi S = conductanceOn P pi S / 2 := by
  rw [conductanceOn, conductanceOn, flow_lazy P pi S hS.compl, Set.compl_inter_self,
    measure_empty, mul_zero, add_zero, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- **Laziness halves the conductance, exactly**: `Φ(lazy P) = Φ(P)/2`.

This is the step that makes `conductance_ballWalk_ge` and
`Arlib.MarkovChains.mixesWithin_of_conductance` compose: the first bounds the conductance of
the *plain* ball walk, the second needs `HasNonnegSpectrum`, which only the *lazy* walk has
(`hasNonnegSpectrum_lazy`).

Nothing is lost to the infimum: the family `SmallSets pi (1/2)` the infimum ranges over
depends only on `pi`, and `lazy P` has the same `pi`; and the side condition `pi S ≤ 1/2`
is a condition on `pi` alone, so it survives verbatim.  The constant is therefore exactly
`2` — not "at least `1/2`". -/
theorem conductance_lazy (P : Kernel Om Om) (pi : Measure Om) :
    conductance (lazy P) pi = conductance P pi / 2 := by
  refine le_antisymm ?_ ?_
  · rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    refine le_conductance P pi fun S hSm hSpos hShalf => ?_
    calc conductance (lazy P) pi * 2
        ≤ conductanceOn (lazy P) pi S * 2 := by
          gcongr
          exact conductance_le_conductanceOn _ _ hSm hSpos hShalf
      _ = conductanceOn P pi S := by
          rw [conductanceOn_lazy P pi hSm,
            ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
  · refine le_conductance (lazy P) pi fun S hSm hSpos hShalf => ?_
    rw [conductanceOn_lazy P pi hSm]
    gcongr
    exact conductance_le_conductanceOn _ _ hSm hSpos hShalf

/-- **The lazy chain's conductance is at least half the plain chain's** — the form in which
`conductance_lazy` is consumed downstream. -/
theorem conductance_div_two_le_conductance_lazy (P : Kernel Om Om) (pi : Measure Om) :
    conductance P pi / 2 ≤ conductance (lazy P) pi := (conductance_lazy P pi).ge

/-- **The joint law of one lazy step** is the corresponding average of the joint law of one
`P`-step and the law of the *diagonal* — the pair `(x, x)` for `x` drawn from `pi`. -/
theorem compProd_lazy (P : Kernel Om Om) [IsMarkovKernel P] (pi : Measure Om) [SFinite pi] :
    pi ⊗ₘ lazy P
      = (2:ℝ≥0∞)⁻¹ • (pi ⊗ₘ P) + (2:ℝ≥0∞)⁻¹ • pi.map (fun x => (x, x)) := by
  have hdiag : Measurable (fun x : Om => (x, x)) := measurable_id.prodMk measurable_id
  ext s hs
  have hsec : ∀ x : Om, MeasurableSet (Prod.mk x ⁻¹' s) := fun _ => measurable_prodMk_left hs
  have hind : ∀ x : Om, (Prod.mk x ⁻¹' s).indicator (1 : Om → ℝ≥0∞) x
      = ((fun y : Om => (y, y)) ⁻¹' s).indicator 1 x := by
    intro x
    by_cases hx : (x, x) ∈ s
    · rw [Set.indicator_of_mem (by simpa using hx), Set.indicator_of_mem (by simpa using hx)]
    · rw [Set.indicator_of_notMem (by simpa using hx),
        Set.indicator_of_notMem (by simpa using hx)]
  have hrw : ∀ x : Om, lazy P x (Prod.mk x ⁻¹' s)
      = (2:ℝ≥0∞)⁻¹ * P x (Prod.mk x ⁻¹' s)
        + (2:ℝ≥0∞)⁻¹ * ((fun y : Om => (y, y)) ⁻¹' s).indicator 1 x := by
    intro x
    rw [lazy_apply_set P x (hsec x), hind x]
  rw [Measure.compProd_apply hs, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    smul_eq_mul, smul_eq_mul, Measure.compProd_apply hs, Measure.map_apply hdiag hs,
    lintegral_congr hrw,
    lintegral_add_left ((Kernel.measurable_kernel_prodMk_left hs).const_mul _),
    lintegral_const_mul _ (Kernel.measurable_kernel_prodMk_left hs),
    lintegral_const_mul _ (measurable_one.indicator (hdiag hs)),
    lintegral_indicator (hdiag hs)]
  simp

/-- **The quadratic form of a lazy chain**: `⟪f, f⟫_{lazy P} = (∫ f² + ⟪f, f⟫_P)/2`. -/
theorem pairing_lazy {P : Kernel Om Om} [IsMarkovKernel P] {pi : Measure Om}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) {f : Om → ℝ} (hf : Measurable f)
    (hmem : MemLp f 2 pi) :
    pairing (lazy P) pi f f
      = ((2:ℝ≥0∞).toReal)⁻¹ * ∫ x, f x ^ 2 ∂pi
        + ((2:ℝ≥0∞).toReal)⁻¹ * pairing P pi f f := by
  have hdiag : Measurable (fun x : Om => (x, x)) := measurable_id.prodMk measurable_id
  have I11 : Integrable (fun p : Om × Om => f p.1 * f p.2) (pi ⊗ₘ P) :=
    integrable_mul_compProd hrev hf hf hmem hmem
  have hFm : AEStronglyMeasurable (fun p : Om × Om => f p.1 * f p.2)
      (pi.map fun x => (x, x)) :=
    ((hf.comp measurable_fst).mul (hf.comp measurable_snd)).aestronglyMeasurable
  have Idiag : Integrable (fun p : Om × Om => f p.1 * f p.2) (pi.map fun x => (x, x)) := by
    rw [integrable_map_measure hFm hdiag.aemeasurable]
    simpa [Function.comp_def, pow_two] using hmem.integrable_sq
  have hInt : ∫ p : Om × Om, f p.1 * f p.2 ∂(pi.map fun x => (x, x))
      = ∫ x, f x ^ 2 ∂pi := by
    rw [integral_map hdiag.aemeasurable hFm]
    simp [pow_two]
  rw [pairing_apply, compProd_lazy P pi,
    integral_add_measure (I11.smul_measure (by simp)) (Idiag.smul_measure (by simp)),
    integral_smul_measure, integral_smul_measure, smul_eq_mul, smul_eq_mul, hInt,
    ← pairing_apply]
  simp only [ENNReal.toReal_inv]
  ring

/-- **A lazy reversible chain has nonnegative spectrum.**

`⟪f, f⟫_{lazy P} = (‖f‖² + ⟪f, f⟫_P)/2 ≥ 0` by `neg_integral_sq_le_pairing_self`.  This is
the hypothesis `Arlib.MarkovChains.mixesWithin_of_conductance` needs and that the plain ball
walk does not supply. -/
theorem hasNonnegSpectrum_lazy {P : Kernel Om Om} [IsMarkovKernel P] {pi : Measure Om}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) :
    HasNonnegSpectrum (lazy P) pi := by
  intro f hf hmem
  rw [pairing_lazy hrev hf hmem]
  have hlow := neg_integral_sq_le_pairing_self hrev hf hmem
  have hc : (0:ℝ) ≤ ((2:ℝ≥0∞).toReal)⁻¹ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hlow hc]

end Lazy

/-- **The lazy ball walk is reversible for the uniform measure and has nonnegative
spectrum** — the two kernel-level hypotheses of
`Arlib.MarkovChains.mixesWithin_of_conductance`. -/
theorem isReversible_and_hasNonnegSpectrum_lazy_ballWalk
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (δ : ℝ)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤) :
    IsReversible (lazy (ballWalk K δ)) (Arlib.uniformOn volume K)
      ∧ HasNonnegSpectrum (lazy (ballWalk K δ)) (Arlib.uniformOn volume K) := by
  haveI : IsProbabilityMeasure (Arlib.uniformOn volume K) :=
    Arlib.isProbabilityMeasure_uniformOn volume hK0 hKtop
  exact ⟨isReversible_lazy (isReversible_ballWalk hK δ),
    hasNonnegSpectrum_lazy (isReversible_ballWalk hK δ)⟩

/-! ## 8. Non-degeneracy: a body of positive finite volume can be cut in half

`Arlib.MarkovChains.mixesWithin_of_conductance` needs two things that are *not* about the
ball walk at all, only about the target measure: that the conductance is not the empty
infimum `⊤`, and that `L²(pi)` contains a function of nonzero variance
(`(rayleighSet _ _).Nonempty`).  Both follow from a single geometric fact, proved here: a
measurable set of positive finite volume in `ℝⁿ` has a measurable piece carrying a fraction
of its volume that lies in `(0, 1/2]`.

The proof is elementary and avoids any density or Sierpiński-type theorem.  If no ball
`B(0,r)` cut `K` non-trivially then `r ↦ vol(K ∩ B(0,r))` would take only the two values `0`
and `vol K`; at `R = inf{r : vol(K ∩ B(0,r)) = vol K}` the inner ball still carries mass `0`
while every strictly larger one carries all of `vol K`, so the whole of `vol K` would be
squeezed into the shell `B(0,R+ε) \ B(0,R)` for **every** `ε > 0` — and Haar scaling makes
that shell's volume `((R+ε)ⁿ − Rⁿ)·vol(B(0,1))`, which is smaller than `vol K` once `ε` is
small enough. -/

/-- **Some ball cuts `K` non-trivially.**  For `K` of positive finite volume there is a
radius `r` with `0 < vol(K ∩ B(0,r)) < vol K`. -/
theorem exists_volume_inter_ball_pos_lt (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤) :
    ∃ r : ℝ, 0 < volume (K ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) ∧
      volume (K ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) < volume K := by
  classical
  by_contra hcon
  push_neg at hcon
  have hfle : ∀ r : ℝ, volume (K ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) ≤ volume K :=
    fun _ => measure_mono Set.inter_subset_left
  have hfmono : ∀ r r' : ℝ, r ≤ r' →
      volume (K ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)
        ≤ volume (K ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r') :=
    fun _ _ h => measure_mono (Set.inter_subset_inter_right _ (Metric.ball_subset_ball h))
  -- under the contradiction hypothesis the cut volume takes only the values `0` and `vol K`
  have hdich : ∀ r : ℝ,
      volume (K ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) = 0 ∨
        volume (K ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) = volume K := by
    intro r
    rcases eq_or_ne (volume (K ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)) 0 with h | h
    · exact Or.inl h
    · exact Or.inr (le_antisymm (hfle r) (hcon r (zero_lt_iff.2 h)))
  -- some ball already carries all of the mass
  have hBne : ∃ r : ℝ,
      volume K ≤ volume (K ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) := by
    by_contra h
    push_neg at h
    have hall : ∀ m : ℕ,
        volume (K ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (m : ℝ)) = 0 :=
      fun m => (hdich m).resolve_right (h m).ne
    have hcov : K = ⋃ m : ℕ, K ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (m : ℝ) := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Metric.mem_ball, dist_zero_right]
      constructor
      · intro hx
        obtain ⟨m, hm⟩ := exists_nat_gt ‖x‖
        exact ⟨m, hx, hm⟩
      · rintro ⟨m, hx, -⟩
        exact hx
    exact hK0 (by rw [hcov]; exact measure_iUnion_null hall)
  set B : Set ℝ :=
    {r : ℝ | volume K ≤ volume (K ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)} with hBdef
  have hBmem : ∀ r : ℝ, r ∈ B ↔
      volume K ≤ volume (K ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) := fun _ => Iff.rfl
  have hBnonempty : B.Nonempty := hBne
  have hBpos : ∀ r ∈ B, (0 : ℝ) ≤ r := by
    intro r hr
    by_contra hneg
    push_neg at hneg
    have hemp : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r = ∅ :=
      Metric.ball_eq_empty.2 hneg.le
    have h := (hBmem r).1 hr
    rw [hemp, Set.inter_empty, measure_empty, nonpos_iff_eq_zero] at h
    exact hK0 h
  have hBbd : BddBelow B := ⟨0, hBpos⟩
  set R : ℝ := sInf B with hRdef
  have hR0 : (0 : ℝ) ≤ R := le_csInf hBnonempty hBpos
  -- below `R` the ball carries no mass at all
  have hlt : ∀ r : ℝ, r < R →
      volume (K ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) = 0 := by
    intro r hr
    have hrB : r ∉ B := fun h => absurd (csInf_le hBbd h) (not_le.2 hr)
    rw [hBmem r] at hrB
    exact (hdich r).resolve_right fun heq => hrB heq.ge
  have hfR : volume (K ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) = 0 := by
    have hcov : K ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R
        = ⋃ k : ℕ, K ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R - 1 / (k + 1)) := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Metric.mem_ball, dist_zero_right]
      constructor
      · rintro ⟨hx, hxb⟩
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (by linarith : (0:ℝ) < R - ‖x‖)
        exact ⟨k, hx, by linarith⟩
      · rintro ⟨k, hx, hxb⟩
        refine ⟨hx, ?_⟩
        have hk : (0:ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
    rw [hcov]
    refine measure_iUnion_null fun k => hlt _ ?_
    have hk : (0:ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  -- above `R` the ball carries all of it
  have hgt : ∀ r : ℝ, R < r →
      volume K ≤ volume (K ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) := by
    intro r hr
    obtain ⟨b, hbB, hbr⟩ := exists_lt_of_csInf_lt hBnonempty hr
    exact le_trans ((hBmem b).1 hbB) (hfmono b r hbr.le)
  -- Haar scaling: every shell `B(0, R+eps) \ B(0, R)` would have to contain all of `vol K`
  set vb : ℝ≥0∞ := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) with hvbdef
  have hvb0 : vb ≠ 0 := (Metric.measure_ball_pos volume 0 one_pos).ne'
  have hvbtop : vb ≠ ⊤ := measure_ball_lt_top.ne
  have hballvol : ∀ r : ℝ, 0 ≤ r →
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) = ENNReal.ofReal (r ^ n) * vb := by
    intro r hr
    rcases eq_or_lt_of_le hr with h | h
    · have hn0 : n ≠ 0 := by omega
      rw [← h, Metric.ball_zero, measure_empty, zero_pow hn0, ENNReal.ofReal_zero, zero_mul]
    · have h2 := Measure.addHaar_ball_of_pos (volume : Measure (EuclideanSpace ℝ (Fin n))) 0 h
      rwa [finrank_euclideanSpace_fin] at h2
  have hshell : ∀ eps : ℝ, 0 < eps →
      ENNReal.ofReal (R ^ n) * vb + volume K ≤ ENNReal.ofReal ((R + eps) ^ n) * vb := by
    intro eps heps
    have hRe : (0:ℝ) ≤ R + eps := by linarith
    have hmb : MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) := measurableSet_ball
    have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R
        ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R + eps) :=
      Metric.ball_subset_ball (by linarith)
    have hcover : K ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R + eps)
        ⊆ (K ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)
          ∪ (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R + eps) \
            Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) := by
      rintro x ⟨hxK, hxb⟩
      by_cases hxR : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R
      · exact Or.inl ⟨hxK, hxR⟩
      · exact Or.inr ⟨hxb, hxR⟩
    have hcf : volume K ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R + eps) \
        Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) := by
      calc volume K ≤ volume (K ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R + eps)) :=
            hgt _ (by linarith)
        _ ≤ volume ((K ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)
              ∪ (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R + eps) \
                Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)) := measure_mono hcover
        _ ≤ volume (K ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)
              + volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R + eps) \
                Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) := measure_union_le _ _
        _ = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R + eps) \
              Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) := by rw [hfR, zero_add]
    have hsplit : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)
        + volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R + eps) \
          Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)
        = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R + eps)) := by
      have h := measure_inter_add_sdiff (μ := volume)
        (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R + eps)) hmb
      rwa [Set.inter_eq_self_of_subset_right hsub] at h
    calc ENNReal.ofReal (R ^ n) * vb + volume K
        = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) + volume K := by
          rw [hballvol R hR0]
      _ ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)
            + volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R + eps) \
              Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) := by gcongr
      _ = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R + eps)) := hsplit
      _ = ENNReal.ofReal ((R + eps) ^ n) * vb := hballvol _ hRe
  -- but the shell's volume tends to `0` with `eps`
  have hvbRpos : 0 < vb.toReal := ENNReal.toReal_pos hvb0 hvbtop
  have hcRpos : 0 < (volume K).toReal := ENNReal.toReal_pos hK0 hKtop
  have hnbhd : (fun t : ℝ => t ^ n) ⁻¹' Set.Iio (R ^ n + (volume K).toReal / vb.toReal)
      ∈ nhds R := by
    refine (continuous_pow n).continuousAt (Iio_mem_nhds ?_)
    have hq : 0 < (volume K).toReal / vb.toReal := by positivity
    linarith
  obtain ⟨eps, heps0, hepssub⟩ := Metric.mem_nhds_iff.1 hnbhd
  have hmem : R + eps / 2 ∈ Metric.ball R eps := by
    rw [Metric.mem_ball, Real.dist_eq, show R + eps / 2 - R = eps / 2 by ring,
      abs_of_pos (by linarith : (0:ℝ) < eps / 2)]
    linarith
  have hkey : (R + eps / 2) ^ n < R ^ n + (volume K).toReal / vb.toReal := hepssub hmem
  have hEN := hshell (eps / 2) (by linarith)
  have hfin2 : ENNReal.ofReal ((R + eps / 2) ^ n) * vb ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvbtop
  have hreal := ENNReal.toReal_mono hfin2 hEN
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvbtop) hKtop,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hR0 n),
    ENNReal.toReal_ofReal (pow_nonneg (by linarith : (0:ℝ) ≤ R + eps / 2) n)] at hreal
  have hmul := mul_lt_mul_of_pos_right hkey hvbRpos
  rw [add_mul, div_mul_cancel₀ _ hvbRpos.ne'] at hmul
  linarith

/-- **A body of positive finite volume has a piece of relative volume in `(0, 1/2]`.**

This is the non-degeneracy fact `Arlib.MarkovChains.mixesWithin_of_conductance` needs, in the
form `Arlib.MarkovChains.SmallSets` asks for it.  It is what stops the conductance infimum
from being the empty infimum `⊤` and what supplies a non-constant `L²` function. -/
theorem exists_smallSet_uniformOn (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤) :
    ∃ S : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet S ∧
      0 < Arlib.uniformOn volume K S ∧ Arlib.uniformOn volume K S ≤ 1 / 2 := by
  haveI : IsProbabilityMeasure (Arlib.uniformOn volume K) :=
    Arlib.isProbabilityMeasure_uniformOn volume hK0 hKtop
  obtain ⟨r, hrpos, hrlt⟩ := exists_volume_inter_ball_pos_lt hn hK0 hKtop
  set S : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r with hS
  have hSm : MeasurableSet S := measurableSet_ball
  have hval : Arlib.uniformOn volume K S = volume (K ∩ S) / volume K := by
    rw [Arlib.uniformOn_apply volume hK hSm, Set.inter_comm]
  have hpos : 0 < Arlib.uniformOn volume K S := by
    rw [hval]
    exact ENNReal.div_pos hrpos.ne' hKtop
  have hone : Arlib.uniformOn volume K S < 1 := by
    rw [hval, ENNReal.div_lt_iff (Or.inl hK0) (Or.inl hKtop), one_mul]
    exact hrlt
  rcases le_or_gt (Arlib.uniformOn volume K S) (1 / 2) with h | h
  · exact ⟨S, hSm, hpos, h⟩
  · refine ⟨Sᶜ, hSm.compl, ?_, ?_⟩
    · rw [prob_compl_eq_one_sub hSm]
      exact tsub_pos_of_lt hone
    · rw [prob_compl_eq_one_sub hSm, tsub_le_iff_left]
      calc (1 : ℝ≥0∞) = 1 / 2 + 1 / 2 := (ENNReal.add_halves 1).symm
        _ ≤ Arlib.uniformOn volume K S + 1 / 2 := by gcongr

/-- **A set of measure in `(0, 1/2]` supplies a non-constant `L²` function**, so the
Rayleigh set of *any* kernel on the same measure is non-empty.  The witness is the indicator
of the set, whose variance is `p(1 − p)` with `p ∈ (0, 1/2]`. -/
theorem rayleighSet_nonempty_of_smallSet {Om : Type*} [MeasurableSpace Om]
    (P : Kernel Om Om) {pi : Measure Om} [IsProbabilityMeasure pi] {S : Set Om}
    (hS : MeasurableSet S) (hpos : 0 < pi S) (hhalf : pi S ≤ 1 / 2) :
    (rayleighSet P pi).Nonempty := by
  refine ⟨rayleighQuotient P pi (Set.indicator S fun _ => (1 : ℝ)),
    Set.indicator S fun _ => (1 : ℝ), ⟨memLp_two_indicator hS, ?_⟩, rfl⟩
  rw [varianceReal_indicator hS]
  have hp0 : 0 < (pi S).toReal := ENNReal.toReal_pos hpos.ne' (measure_ne_top pi S)
  have hphalf : (pi S).toReal ≤ 1 / 2 := by
    have h2 : ((1 : ℝ≥0∞) / 2).toReal = 1 / 2 := by norm_num
    exact h2 ▸ ENNReal.toReal_mono (by norm_num) hhalf
  have : 0 < (pi S).toReal - (pi S).toReal ^ 2 := by nlinarith
  exact this.ne'

/-! ## 9. End to end: the lazy ball walk mixes

Everything above, plus `Arlib.MarkovChains.mixesWithin_of_conductance` (`L2Mixing.lean`,
whose own ingredients are Cheeger's inequality and the `L²` contraction), composed into one
statement.  The two hypotheses that carry content — the isoperimetric inequality and the
uniform lower bound on the local conductance — are still written out **inline**, exactly as
in `conductance_ballWalk_ge`; no `def`, no `structure` field, no named `Prop` stands between
the reader and what is assumed. -/

/-- **The lazy ball walk on `K` mixes to total variation `eps`, from an `M`-warm start, in

    conductanceMixingTime M (min (θ/32) (κ·θ²·δ/(128·n))) eps

steps** — i.e. `O(φ⁻² log(M/eps))` steps with `φ = min(θ/32, κθ²δ/(128n))`, by
`Arlib.MarkovChains.conductanceMixingTime_le`.

This is the whole chain in one place: `conductance_ballWalk_ge` (geometry + isoperimetry →
conductance), `conductance_lazy` (laziness costs exactly a factor `2` of conductance),
`hasNonnegSpectrum_lazy` (laziness buys the spectral hypothesis the plain ball walk lacks),
`sq_conductance_div_two_le_spectralGap` (Cheeger) and `mixesWithin_of_conductance` (`L²`
decay → a step count).

The hypotheses that carry content, spelled out and not hidden behind a name:

* `hiso` — the **isoperimetric inequality** for the uniform measure on `K`, with an explicit
  real constant `kappa > 0`.  Mathlib has no isoperimetric inequality for log-concave
  densities; a caller who can prove one with their own constant gets the mixing bound with
  it.  This is the only unproved input.
* `hell` — a **uniform lower bound `ℓ(x) ≥ θ` on the local conductance of `K`**.  Some such
  hypothesis is *forced* rather than a proof artefact: near an extreme point of a bounded
  `K` one has `ℓ ≲ 1/2`, and near a sharp corner much less, so the plain uniform ball walk
  really does have small conductance there; Cousins–Vempala avoid it by analysing the
  *speedy* walk, whose stationary density is proportional to `ℓ`, and that walk is not built
  in this library.  Note that the paper's reading `θ = 3/4` is **vacuous** for a bounded
  `K` — a supporting hyperplane at a boundary point forces `ℓ ≤ 1/2` there — which is why
  the theorem is parameterised by `θ`; `ofReal_le_ell_unitBall` is the witness that it is
  satisfiable, with `θ = 2⁻ⁿ` on the unit ball.
* `hwarm` — the `M`-warm start, and `hM : 1 ≤ M`.

**The quantitative gap against the paper.**  `thm:speedyconductance` gets separation
`δ/√n` from the ball-cap estimate of [KLS95, Lemma 3.5]; Mathlib has no such estimate, and
the elementary midpoint bound used here (`volume_ball_le_volume_inter_ball_add`) only gets
`θ·δ/n`.  So the conductance here, and therefore the step count, is worse than the paper's
by one factor of `√n`.  The loss is entirely in the *geometry*; the Markov-chain argument is
the paper's.

See `mixesWithin_lazy_ballWalk_unitBall` for the check that this hypothesis bundle is
jointly satisfiable rather than vacuously composed. -/
theorem mixesWithin_lazy_ballWalk (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤) {δ : ℝ} (hδ : 0 < δ)
    {θ : ℝ} (hθ : 0 < θ)
    (hell : ∀ x ∈ K, ENNReal.ofReal θ ≤ ell K δ x)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hiso : ∀ d : ℝ, 0 < d → ∀ A B : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet A → MeasurableSet B → A ⊆ K → B ⊆ K →
      (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) →
      ENNReal.ofReal kappa * ENNReal.ofReal d * Arlib.uniformOn volume K A
          * Arlib.uniformOn volume K B
        ≤ Arlib.uniformOn volume K ((K \ A) \ B))
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 (Arlib.uniformOn volume K))
    {eps : ℝ} (heps : 0 < eps) {t : ℕ}
    (ht : conductanceMixingTime M (min (θ / 32) (kappa * θ ^ 2 * δ / (128 * (n : ℝ)))) eps ≤ t) :
    MixesWithin (lazy (ballWalk K δ)) (Arlib.uniformOn volume K) mu0 t (ENNReal.ofReal eps) := by
  haveI : IsProbabilityMeasure (Arlib.uniformOn volume K) :=
    Arlib.isProbabilityMeasure_uniformOn volume hK0 hKtop
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨hrev, hpsd⟩ := isReversible_and_hasNonnegSpectrum_lazy_ballWalk hK δ hK0 hKtop
  obtain ⟨S0, hS0m, hS0pos, hS0half⟩ := exists_smallSet_uniformOn hn hK hK0 hKtop
  have hne := rayleighSet_nonempty_of_smallSet (lazy (ballWalk K δ)) hS0m hS0pos hS0half
  -- `θ ≤ 1`, because `ℓ ≤ 1` and `K` is non-empty
  obtain ⟨x0, hx0⟩ := nonempty_of_measure_ne_zero hK0
  have hθ1 : θ ≤ 1 := ENNReal.ofReal_le_one.1 ((hell x0 hx0).trans (ell_le_one K δ x0))
  set phi : ℝ := min (θ / 32) (kappa * θ ^ 2 * δ / (128 * (n : ℝ))) with hphidef
  have hphi0 : 0 < phi := lt_min (by positivity) (by positivity)
  have hphi1 : phi ≤ 1 := le_trans (min_le_left _ _) (by linarith)
  -- the conductance of the plain walk, then of the lazy one
  have hcond := conductance_ballWalk_ge hn hK hK0 hKtop hδ hθ hell
    (kappa := ENNReal.ofReal kappa) hiso
  have hbranch1 : ENNReal.ofReal phi * 2 ≤ ENNReal.ofReal θ / 16 := by
    have h16 : ENNReal.ofReal θ / 16 = ENNReal.ofReal (θ / 16) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 16)]
      norm_num
    have hmul : ENNReal.ofReal phi * 2 = ENNReal.ofReal (phi * 2) := by
      rw [ENNReal.ofReal_mul hphi0.le]
      norm_num
    rw [h16, hmul]
    refine ENNReal.ofReal_le_ofReal ?_
    have := min_le_left (θ / 32) (kappa * θ ^ 2 * δ / (128 * (n : ℝ)))
    rw [← hphidef] at this
    linarith
  have hbranch2 : ENNReal.ofReal phi * 2
      ≤ ENNReal.ofReal kappa * ENNReal.ofReal (θ ^ 2 * δ / (n : ℝ)) / 64 := by
    have hrhs : ENNReal.ofReal kappa * ENNReal.ofReal (θ ^ 2 * δ / (n : ℝ)) / 64
        = ENNReal.ofReal (kappa * (θ ^ 2 * δ / (n : ℝ)) / 64) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 64),
        ENNReal.ofReal_mul hkappa.le]
      norm_num
    have hmul : ENNReal.ofReal phi * 2 = ENNReal.ofReal (phi * 2) := by
      rw [ENNReal.ofReal_mul hphi0.le]
      norm_num
    rw [hrhs, hmul]
    refine ENNReal.ofReal_le_ofReal ?_
    have hmin := min_le_right (θ / 32) (kappa * θ ^ 2 * δ / (128 * (n : ℝ)))
    rw [← hphidef] at hmin
    have heq : kappa * θ ^ 2 * δ / (128 * (n : ℝ)) * 2 = kappa * (θ ^ 2 * δ / (n : ℝ)) / 64 := by
      field_simp
      ring
    nlinarith [hmin]
  have hlazy : ENNReal.ofReal phi
      ≤ conductance (lazy (ballWalk K δ)) (Arlib.uniformOn volume K) := by
    rw [conductance_lazy]
    have hstep : ENNReal.ofReal phi
        ≤ min (ENNReal.ofReal θ / 16)
            (ENNReal.ofReal kappa * ENNReal.ofReal (θ ^ 2 * δ / (n : ℝ)) / 64) / 2 := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      exact le_min hbranch1 hbranch2
    exact hstep.trans (by gcongr)
  have hcondtop : conductance (lazy (ballWalk K δ)) (Arlib.uniformOn volume K) ≠ ⊤ :=
    ne_top_of_le_ne_top (by norm_num)
      (conductance_le_one _ _ ⟨S0, hS0m, hS0pos, hS0half⟩)
  have hphireal : phi ≤ (conductance (lazy (ballWalk K δ)) (Arlib.uniformOn volume K)).toReal := by
    have h := ENNReal.toReal_mono hcondtop hlazy
    rwa [ENNReal.toReal_ofReal hphi0.le] at h
  exact mixesWithin_of_conductance hrev hpsd hne hM hwarm hphi0 hphi1 heps hphireal ht

/-! ## 10. Joint satisfiability of the hypothesis bundle (`CLAUDE.md` §11)

A chain of four individually true theorems can compose to something vacuous.  What follows
is the check, and it is deliberately split so that the one hypothesis this library cannot
discharge stays visible.

`mixesWithin_lazy_ballWalk_unitBall` instantiates **every** hypothesis of
`mixesWithin_lazy_ballWalk` on the unit ball except `hiso`, which it still carries: the body
is measurable with positive finite volume, `hell` holds at `θ = 2⁻ⁿ` by
`ofReal_le_ell_unitBall`, the start is `1`-warm (it is the target itself), and the step
count is a concrete natural number.  So the *geometry* and the *local-conductance*
hypotheses are compatible: they hold simultaneously, on a convex body, at a positive `θ`.

`hiso` itself is **not** proved here and cannot be: Mathlib has no isoperimetric inequality
for convex bodies or log-concave densities.  It is not vacuous either — it is the
Lovász–Simonovits inequality, true for every convex body with `kappa = 1/diam(K)`, so
`kappa = 1/2` for the unit ball.  Two things are worth recording about it.  First, it is a
hypothesis with real content, not one that any positive-volume body satisfies: for the
*disconnected* body `B(0,1) ∪ B(v,1)` with `‖v‖ > 2`, taking `A` and `B` to be the two
components gives `π(A)π(B) = 1/4 > 0` and `π(K \ A \ B) = 0`, so `hiso` fails at every
`kappa > 0`.  Convexity is doing work.  Second, the only *proved* witness for `hell` is
`θ = 2⁻ⁿ`, which makes the step count exponential in `n`; the polynomial bound needs the
speedy walk, whose stationary density is proportional to `ℓ` — see the caveat in the
docstring of `mixesWithin_lazy_ballWalk`. -/

/-- **Every hypothesis of `mixesWithin_lazy_ballWalk` except the isoperimetric one, jointly
discharged on the unit ball.**  Body: the open unit ball, which is convex with positive
finite volume.  Local conductance: `θ = 2⁻ⁿ`, by `ofReal_le_ell_unitBall`.  Start: the
uniform law itself, which is `1`-warm.  What remains carried is exactly `hiso`. -/
theorem mixesWithin_lazy_ballWalk_unitBall (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hiso : ∀ d : ℝ, 0 < d → ∀ A B : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet A → MeasurableSet B →
      A ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 →
      B ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 →
      (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) →
      ENNReal.ofReal kappa * ENNReal.ofReal d
          * Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) A
          * Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) B
        ≤ Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
            ((Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 \ A) \ B))
    {eps : ℝ} (heps : 0 < eps) {t : ℕ}
    (ht : conductanceMixingTime 1
      (min (((1:ℝ) / 2) ^ n / 32)
        (kappa * (((1:ℝ) / 2) ^ n) ^ 2 * δ / (128 * (n : ℝ)))) eps ≤ t) :
    MixesWithin (lazy (ballWalk (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ))
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) t
      (ENNReal.ofReal eps) := by
  haveI := isProbabilityMeasure_uniformOn_unitBall (n := n)
  refine mixesWithin_lazy_ballWalk hn measurableSet_ball volume_unitBall_ne_zero
    volume_unitBall_ne_top hδ (by positivity)
    (fun x hx => ofReal_le_ell_unitBall hδ hδ1 hx) hkappa hiso le_rfl ?_ heps ht
  simpa using IsWarm.refl
    (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))

/-! ## 11. The sampler contract: Kannan–Vempala Theorem 2 from a geometric hypothesis

`Arlib.PointwiseRoute.theorem2_of_mixesWithin` consumes a chain that has mixed in
total variation to tolerance `acc / Vol(K)` and returns Theorem 2's two-sided window.
Feeding it `mixesWithin_lazy_ballWalk` closes the chain from a geometric hypothesis about
`K` all the way to the sampler contract. -/

/-- **End to end: from an isoperimetric inequality for `K` to the KV97 Theorem 2 window.**

Run the lazy `δ`-ball walk on `K` from an `M`-warm start for
`conductanceMixingTime M (min (θ/32) (κθ²δ/(128n))) (acc/V)` steps; then for every lattice
point `x`, the rounding probability lies in the window `[(1−(E+acc))/V, (1+acc)/V]`.

Every hypothesis with content is inline: `hiso` is the isoperimetric inequality written out,
`hell` the uniform lower bound on the local conductance, `hesc` the escape mass of the tent
outside `K`, `hwarm` the warm start.  The two honest caveats of
`mixesWithin_lazy_ballWalk` apply verbatim: the constant is a factor `√n` worse than
Cousins–Vempala's because Mathlib lacks the ball-cap volume estimate, and `hell` is forced
rather than a proof artefact — its only *proved* witness is `θ = 2⁻ⁿ` on the unit ball, so
the step count this theorem certifies is exponential in `n` unless the caller supplies a
better `θ`. -/
theorem theorem2_of_lazy_ballWalk (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤) {δ : ℝ} (hδ : 0 < δ)
    {θ : ℝ} (hθ : 0 < θ)
    (hell : ∀ x ∈ K, ENNReal.ofReal θ ≤ ell K δ x)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hiso : ∀ d : ℝ, 0 < d → ∀ A B : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet A → MeasurableSet B → A ⊆ K → B ⊆ K →
      (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) →
      ENNReal.ofReal kappa * ENNReal.ofReal d * Arlib.uniformOn volume K A
          * Arlib.uniformOn volume K B
        ≤ Arlib.uniformOn volume K ((K \ A) \ B))
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 (Arlib.uniformOn volume K))
    {V acc E : ℝ} (hV : (volume K).toReal = V) (hacc : 0 < acc)
    {x : EuclideanSpace ℝ (Fin n)}
    (hesc : ∫ p in Kᶜ, Arlib.Lattice.Rounding.prodTent x p ≤ E)
    {t : ℕ}
    (ht : conductanceMixingTime M (min (θ / 32) (kappa * θ ^ 2 * δ / (128 * (n : ℝ))))
      (acc / V) ≤ t) :
    (1 - (E + acc)) / V
        ≤ ∫ p, Arlib.Lattice.Rounding.prodTent x p
            ∂(iterate (lazy (ballWalk K δ)) mu0 t) ∧
      ∫ p, Arlib.Lattice.Rounding.prodTent x p
          ∂(iterate (lazy (ballWalk K δ)) mu0 t) ≤ (1 + acc) / V := by
  have hVpos : 0 < V := hV ▸ ENNReal.toReal_pos hK0 hKtop
  exact Arlib.PointwiseRoute.theorem2_of_mixesWithin hK hK0 hKtop hV hacc.le
    (mixesWithin_lazy_ballWalk hn hK hK0 hKtop hδ hθ hell hkappa hiso hM hwarm
      (by positivity) ht)
    hesc

/-! ## Axiom check -/

#print axioms midpoint_ball_subset_inter_ball
#print axioms volume_ball_le_volume_inter_ball_add
#print axioms ell_le_ballWalk_add_ballWalk_compl
#print axioms lt_dist_of_ballWalk_lt
#print axioms mul_measure_add_measure_le_mul_flow
#print axioms conductance_ballWalk_ge
#print axioms ofReal_le_ell_unitBall
#print axioms neg_integral_sq_le_pairing_self
#print axioms hasNonnegSpectrum_lazy
#print axioms isReversible_and_hasNonnegSpectrum_lazy_ballWalk
#print axioms conductanceOn_lazy
#print axioms conductance_lazy
#print axioms conductance_div_two_le_conductance_lazy
#print axioms exists_volume_inter_ball_pos_lt
#print axioms exists_smallSet_uniformOn
#print axioms rayleighSet_nonempty_of_smallSet
#print axioms mixesWithin_lazy_ballWalk
#print axioms mixesWithin_lazy_ballWalk_unitBall
#print axioms theorem2_of_lazy_ballWalk

end Arlib.MarkovChains
