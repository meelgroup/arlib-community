/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.WalkLaw
import ArlibCommunity.Algorithms.HitAndRun.Analysis.ChordPoint
import ArlibCommunity.Algorithms.HitAndRun.Analysis.GaussianDirection

/-!
# The law of one step

`law_step_apply`: one step of the sampler stays put with probability `1/2` (the lazy
coin) and otherwise moves.  `law_move_apply`: the move draws a Gaussian vector `g` and
lands as the capped chord sampling `Tape.chordPoint` along `θ = g/‖g‖` between the
bisection values.  `lintegral_direction`: averaging a function of `θ` over `g` is
averaging it over the uniform law on the sphere.
-/

set_option autoImplicit false

open MeasureTheory Set ProbabilityTheory Metric
open scoped ENNReal

namespace ArlibCommunity.Algorithms.HitAndRun

open ArlibCommunity.Algorithms.HitAndRun.Model.Operations
open TapeProgram

variable {n : ℕ} {member : State n → Bool}

namespace Tape

/-- The moving half of a step from `x`, after the Gaussian vector `g`. -/
noncomputable def move (w : WalkParams) (x g : State n) : TapeProgram n (State n) := do
  let hi ← bisect x (‖g‖⁻¹ • g) w.bisectionSteps 0 (2 * w.D)
  let lo ← bisect x (-(‖g‖⁻¹ • g)) w.bisectionSteps 0 (2 * w.D)
  chordPoint x (‖g‖⁻¹ • g) lo hi w.rejectionTries

theorem step_eq (w : WalkParams) (x : State n) :
    step w x = TapeProgram.unitNumber >>= fun coin =>
      if coin ≤ 1 / 2 then Pure.pure x else TapeProgram.gaussianVector >>= fun g => move w x g :=
  rfl

theorem move_meas (hm : Measurable member) (w : WalkParams) :
    MeasFam member fun q : State n × State n => move w q.1 q.2 := by
  refine MeasFam.bind' ((bisect_meas hm w.bisectionSteps).comp
    (φ := fun q : State n × State n => ((q.1, ‖q.2‖⁻¹ • q.2), ((0 : ℝ), 2 * w.D)))
    (by fun_prop)) ?_
  refine MeasFam.bind' ((bisect_meas hm w.bisectionSteps).comp
    (φ := fun q : (State n × State n) × ℝ =>
      ((q.1.1, -(‖q.1.2‖⁻¹ • q.1.2)), ((0 : ℝ), 2 * w.D))) (by fun_prop)) ?_
  exact (chordPoint_meas hm w.rejectionTries).comp
    (φ := fun q : ((State n × State n) × ℝ) × ℝ =>
      ((q.1.1.1, ‖q.1.1.2‖⁻¹ • q.1.1.2), (q.2, q.1.2))) (by fun_prop)

end Tape

/-- The chord point of the move along `g`, between the two bisection values. -/
noncomputable def moveChord (member : State n → Bool) (w : WalkParams) (x g : State n) :
    TapeProgram n (State n) :=
  Tape.chordPoint x (‖g‖⁻¹ • g)
    (bisectVal member x (-(‖g‖⁻¹ • g)) w.bisectionSteps 0 (2 * w.D))
    (bisectVal member x (‖g‖⁻¹ • g) w.bisectionSteps 0 (2 * w.D)) w.rejectionTries

theorem law_move (w : WalkParams) (x g : State n) :
    law member (Tape.move w x g) = law member (moveChord member w x g) := by
  unfold Tape.move
  simp only [TapeProgram.bind_eq]
  rw [law_bisect_bind]
  rw [law_bisect_bind]
  rfl

/-- **One step**: stay with probability `1/2`, else move. -/
theorem law_step_apply (w : WalkParams) (x : State n)
    {S : Set (State n)} (hS : MeasurableSet S) :
    law member (Tape.step w x) S =
      2⁻¹ * Measure.dirac x S +
        2⁻¹ * ((standardGaussian n).bind fun g => law member (Tape.move w x g)) S := by
  set M := (standardGaussian n).bind fun g => law member (Tape.move w x g)
  have hlaw : law member (Tape.step w x) =
      uniformUnit.bind fun c => if c ≤ 1 / 2 then Measure.dirac x else M := by
    show uniformUnit.bind (fun c => law member (if c ≤ 1 / 2 then TapeProgram.pure x else
      TapeProgram.gaussian fun g => (TapeProgram.pure g).bind fun g => Tape.move w x g)) = _
    congr 1
    funext c
    split <;> rfl
  have hI : MeasurableSet (Iic (1 / 2 : ℝ)) := measurableSet_Iic
  have hκ : Measurable fun c : ℝ => if c ≤ 1 / 2 then Measure.dirac x else M :=
    Measurable.ite hI measurable_const measurable_const
  have hhalf : uniformUnit (Iic (1 / 2 : ℝ)) = 2⁻¹ := by
    have hset : Iic (1 / 2 : ℝ) ∩ Icc 0 1 = Icc 0 (1 / 2) := by
      ext c
      simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
    rw [uniformUnit, Measure.restrict_apply hI, hset, Real.volume_Icc, sub_zero,
      ArlibCommunity.Foundations.MarkovChainTheory.ofReal_one_half, one_div]
  have hhalf' : uniformUnit (Iic (1 / 2 : ℝ))ᶜ = 2⁻¹ := by
    rw [prob_compl_eq_one_sub hI, hhalf, ENNReal.one_sub_inv_two]
  rw [hlaw, Measure.bind_apply hS hκ.aemeasurable]
  have hfun : ∀ c : ℝ, (if c ≤ 1 / 2 then Measure.dirac x else M) S =
      (Iic (1 / 2 : ℝ)).indicator (fun _ => Measure.dirac x S) c +
        (Iic (1 / 2 : ℝ))ᶜ.indicator (fun _ => M S) c := by
    intro c
    by_cases hc : c ≤ 1 / 2
    · simp only [hc, ↓reduceIte]
      rw [indicator_of_mem (show c ∈ Iic (1 / 2 : ℝ) from hc),
        indicator_of_notMem (show c ∉ (Iic (1 / 2 : ℝ))ᶜ from fun h => h hc), add_zero]
    · simp only [hc, ↓reduceIte]
      rw [indicator_of_notMem (show c ∉ Iic (1 / 2 : ℝ) from hc),
        indicator_of_mem (show c ∈ (Iic (1 / 2 : ℝ))ᶜ from hc), zero_add]
  simp_rw [hfun]
  rw [lintegral_add_left ((measurable_const.indicator hI)), lintegral_indicator_const hI,
    lintegral_indicator_const hI.compl, hhalf, hhalf', mul_comm (Measure.dirac x S),
    mul_comm (M S)]

/-- **The move, on an event**: average over the Gaussian vector of the capped chord
sampling along its direction. -/
theorem law_move_apply (hm : Measurable member) (w : WalkParams) (x : State n)
    {S : Set (State n)} (hS : MeasurableSet S) :
    ((standardGaussian n).bind fun g => law member (Tape.move w x g)) S =
      ∫⁻ g, law member (moveChord member w x g) S ∂(standardGaussian n) := by
  have hmeas : Measurable fun g => law member (Tape.move w x g) :=
    measurable_law member (Tape.move w x)
      ((Tape.move_meas hm w).comp (φ := fun g : State n => (x, g))
        (by fun_prop)).fst
  rw [Measure.bind_apply hS hmeas.aemeasurable]
  simp_rw [law_move]

/-! ## Directions -/

/-- The standard Gaussian gives the origin no mass. -/
theorem standardGaussian_zero [NeZero n] : standardGaussian n {0} = 0 := by
  rw [standardGaussian, GaussianDirection.stdGaussian_apply n (measurableSet_singleton 0)]
  exact setLIntegral_measure_zero _ _ (measure_singleton 0)

/-- **Averaging over the direction of a Gaussian vector is averaging over the sphere.** -/
theorem lintegral_direction [NeZero n] {F : State n → ℝ≥0∞}
    (hF : Measurable fun θ : sphere (0 : State n) 1 => F θ) :
    ∫⁻ g, F (‖g‖⁻¹ • g) ∂(standardGaussian n) =
      ∫⁻ θ, F θ ∂(ArlibCommunity.Foundations.MarkovChainTheory.unifSphere n) := by
  rw [← GaussianDirection.stdGaussian_map_direction, lintegral_map hF
    GaussianDirection.measurable_direction]
  refine lintegral_congr_ae ?_
  have h0 : ∀ᵐ g ∂(standardGaussian n), g ≠ 0 := by
    rw [ae_iff]
    simpa using standardGaussian_zero
  filter_upwards [h0] with g hg
  simp [GaussianDirection.direction, GaussianDirection.directionVal, hg]

end ArlibCommunity.Algorithms.HitAndRun
