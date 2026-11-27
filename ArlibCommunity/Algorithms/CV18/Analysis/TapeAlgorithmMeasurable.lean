/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.TapeAlgorithm
import ArlibCommunity.Algorithms.CV18.Analysis.TapeMeasurability
import ArlibCommunity.Algorithms.CV18.Analysis.ProgramSemantics

/-!
# The tape algorithm runs measurably

Each procedure of the tape algorithm (`Analysis/TapeAlgorithm.lean`) runs measurably in
its arguments, its budget and the tape (`MeasFam`), when membership is answered by a
measurable `member` — as a correct oracle's is (`MembershipOracle.measurable_query`).
-/

set_option autoImplicit false

open MeasureTheory Set

namespace ArlibCommunity.Algorithms.CV18

open ArlibCommunity.Algorithms.CV18.Model.Operations

namespace TapeProgram

variable {n : ℕ} {member : AmbientSpace n → Bool}
variable {A β γ : Type} [MeasurableSpace A] [MeasurableSpace β] [MeasurableSpace γ]

theorem MeasFam.bindBall {k : A → AmbientSpace n → TapeProgram n β}
    (hk : MeasFam member fun p : A × AmbientSpace n => k p.1 p.2) :
    MeasFam member fun a => TapeProgram.ballPoint >>= k a :=
  MeasFam.congr (MeasFam.ball hk) fun _ => rfl

theorem MeasFam.bindGaussian {k : A → AmbientSpace n → TapeProgram n β}
    (hk : MeasFam member fun p : A × AmbientSpace n => k p.1 p.2) :
    MeasFam member fun a => TapeProgram.gaussianVector >>= k a :=
  MeasFam.congr (MeasFam.gaussian hk) fun _ => rfl

theorem MeasFam.bindUnit {k : A → ℝ → TapeProgram n β}
    (hk : MeasFam member fun p : A × ℝ => k p.1 p.2) :
    MeasFam member fun a => TapeProgram.unitNumber >>= k a :=
  MeasFam.congr (MeasFam.unit hk) fun _ => rfl

theorem MeasFam.bindIsMember (hm : Measurable member) {x : A → AmbientSpace n}
    (hx : Measurable x) {k : A → Bool → TapeProgram n β}
    (hk : MeasFam member fun p : A × Bool => k p.1 p.2) :
    MeasFam member fun a => TapeProgram.isMember (x a) >>= k a :=
  MeasFam.congr (MeasFam.query hm hx hk) fun _ => rfl

theorem MeasFam.bind' [Inhabited β] {f : A → TapeProgram n β} {h : A → β → TapeProgram n γ}
    (hf : MeasFam member f) (hh : MeasFam member fun p : A × β => h p.1 p.2) :
    MeasFam member fun a => f a >>= h a :=
  MeasFam.bind hf hh

/-- A family indexed by a countable discrete parameter runs measurably if each slice
does. -/
theorem MeasFam.of_slices {K : Type} [MeasurableSpace K] [Countable K]
    [MeasurableSingletonClass K] {f : K × A → TapeProgram n β}
    (h : ∀ k, MeasFam member fun a => f (k, a)) : MeasFam member f := by
  have hg : Measurable fun p : (A × ℕ × Tape n) × K => execB member (f (p.2, p.1.1)) p.1.2.1
      p.1.2.2 :=
    measurable_from_prod_countable_left fun k => h k
  exact hg.comp ((measurable_fst.snd.prodMk measurable_snd).prodMk measurable_fst.fst)

end TapeProgram

namespace Tape

open TapeProgram

variable (q : VolumeParams) {member : AmbientSpace q.n → Bool} (hm : Measurable member)
include hm

theorem ballWalkStep_meas (sigma2 : ℝ) :
    MeasFam member fun x : AmbientSpace q.n => ballWalkStep q sigma2 x := by
  refine MeasFam.bindBall ?_
  refine MeasFam.bindIsMember hm (x := fun p : AmbientSpace q.n × AmbientSpace q.n => p.1 + proposalRadius q sigma2 • p.2)
    (by fun_prop) ?_
  refine MeasFam.bindUnit ?_
  have hy : Measurable fun p : ((AmbientSpace q.n × AmbientSpace q.n) × Bool) × ℝ =>
      p.1.1.1 + proposalRadius q sigma2 • p.1.1.2 := by fun_prop
  refine MeasFam.ite ?_ (MeasFam.pure ?_) (MeasFam.pure ?_)
  · measurability
  · refine measurable_const.prodMk (Measurable.ite ?_ hy (by fun_prop))
    refine measurableSet_le measurable_snd ?_
    unfold lazyAcceptance metropolisAcceptance
    fun_prop
  · fun_prop

theorem properWalk_meas (sigma2 : ℝ) :
    ∀ cap : ℕ, MeasFam member fun p : ℕ × AmbientSpace q.n => properWalk q sigma2 cap p.1 p.2
  | 0 => MeasFam.congr (MeasFam.pure (g := fun _ : ℕ × AmbientSpace q.n =>
      (none : Option (AmbientSpace q.n))) measurable_const) fun _ => rfl
  | cap + 1 => by
      refine MeasFam.of_slices fun steps => ?_
      cases steps with
      | zero =>
          refine MeasFam.bindIsMember hm (x := fun x => (scaleFactor q)⁻¹ • x) (by fun_prop) ?_
          exact MeasFam.pure (g := fun p : AmbientSpace q.n × Bool => some p.1)
            (measurable_some.comp measurable_fst)
      | succ steps =>
          refine MeasFam.bind' (ballWalkStep_meas q hm sigma2) ?_
          exact MeasFam.congr ((properWalk_meas sigma2 cap).comp
            (φ := fun p : AmbientSpace q.n × (Bool × AmbientSpace q.n) =>
              (if p.2.1 = true then steps else steps + 1, p.2.2))
            (by
              refine Measurable.prodMk ?_ measurable_snd.snd
              exact Measurable.ite (measurable_snd.fst (measurableSet_singleton true))
                measurable_const measurable_const)) fun _ => rfl

theorem rejectionAttempt_meas (sigma2 : ℝ) :
    MeasFam member fun x : AmbientSpace q.n => rejectionAttempt q sigma2 x := by
  refine MeasFam.bindIsMember hm (x := fun x => (scaleFactor q)⁻¹ • x) (by fun_prop) ?_
  refine MeasFam.bindUnit ?_
  refine MeasFam.ite ?_ (MeasFam.pure ?_) (MeasFam.pure ?_)
  · have hacc : Measurable fun p : (AmbientSpace q.n × Bool) × ℝ =>
        (2 : ENNReal)⁻¹ * gaussianScaleAcceptance sigma2 (scaleFactor q)
          ((scaleFactor q)⁻¹ • p.1.1) := by
      unfold gaussianScaleAcceptance
      fun_prop
    measurability
  · fun_prop
  · fun_prop

theorem collectSamples_slice (sigma2 : ℝ) (weight : AmbientSpace q.n → ℝ)
    (hweight : Measurable weight) (cap steps retries : ℕ) :
    ∀ retriesLeft samplesLeft : ℕ, MeasFam member fun a : ℝ × AmbientSpace q.n =>
      collectSamples q sigma2 weight cap steps retries retriesLeft samplesLeft a.1 a.2
  | _, 0 => by
      refine MeasFam.congr (MeasFam.pure (g := fun a : ℝ × AmbientSpace q.n => some a)
        measurable_some) fun a => ?_
      rw [collectSamples]
      rfl
  | 0, _ + 1 => by
      refine MeasFam.congr (MeasFam.pure (g := fun _ : ℝ × AmbientSpace q.n =>
        (none : Option (ℝ × AmbientSpace q.n))) measurable_const) fun a => ?_
      rw [collectSamples]
      rfl
  | retriesLeft + 1, samplesLeft + 1 => by
      have hcont : MeasFam member fun p : ((ℝ × AmbientSpace q.n) × AmbientSpace q.n) ×
          (Bool × AmbientSpace q.n) =>
          if p.2.1 = true then
            collectSamples q sigma2 weight cap steps retries retries samplesLeft
              (p.1.1.1 + weight p.2.2) p.1.2
          else
            collectSamples q sigma2 weight cap steps retries retriesLeft
              (samplesLeft + 1) p.1.1.1 p.1.2 :=
        MeasFam.ite (measurable_snd.fst (measurableSet_singleton true))
          ((collectSamples_slice sigma2 weight hweight cap steps retries retries
            samplesLeft).comp
            (φ := fun p : ((ℝ × AmbientSpace q.n) × AmbientSpace q.n) ×
              (Bool × AmbientSpace q.n) => (p.1.1.1 + weight p.2.2, p.1.2)) (by fun_prop))
          ((collectSamples_slice sigma2 weight hweight cap steps retries retriesLeft
            (samplesLeft + 1)).comp
            (φ := fun p : ((ℝ × AmbientSpace q.n) × AmbientSpace q.n) ×
              (Bool × AmbientSpace q.n) => (p.1.1.1, p.1.2)) (by fun_prop))
      have hsome : MeasFam member fun p : (ℝ × AmbientSpace q.n) × AmbientSpace q.n =>
          rejectionAttempt q sigma2 p.2 >>= fun r =>
            if r.1 = true then
              collectSamples q sigma2 weight cap steps retries retries samplesLeft
                (p.1.1 + weight r.2) p.2
            else
              collectSamples q sigma2 weight cap steps retries retriesLeft
                (samplesLeft + 1) p.1.1 p.2 :=
        MeasFam.bind' ((rejectionAttempt_meas q hm sigma2).comp measurable_snd) hcont
      have hopt := MeasFam.option (member := member)
        (f := fun _ : ℝ × AmbientSpace q.n =>
          (TapeProgram.pure none : TapeProgram q.n (Option (ℝ × AmbientSpace q.n))))
        (MeasFam.congr (MeasFam.pure (g := fun _ : ℝ × AmbientSpace q.n =>
          (none : Option (ℝ × AmbientSpace q.n))) measurable_const) fun _ => rfl) hsome
      have hwalk : MeasFam member fun a : ℝ × AmbientSpace q.n =>
          properWalk q sigma2 (cap + 1) steps a.2 :=
        (properWalk_meas q hm sigma2 (cap + 1)).comp
          (φ := fun a : ℝ × AmbientSpace q.n => (steps, a.2)) (by fun_prop)
      refine MeasFam.congr (MeasFam.bind hwalk hopt) fun a => ?_
      rw [collectSamples]
      congr 1
      funext o
      rcases o with _ | y
      · rfl
      · congr 1
termination_by retriesLeft samplesLeft => (samplesLeft, retriesLeft)

theorem collectSamples_meas (sigma2 : ℝ) (weight : AmbientSpace q.n → ℝ)
    (hweight : Measurable weight) (cap steps retries retriesLeft samplesLeft : ℕ) :
    MeasFam member fun a : ℝ × AmbientSpace q.n =>
      collectSamples q sigma2 weight cap steps retries retriesLeft samplesLeft a.1 a.2 :=
  collectSamples_slice q hm sigma2 weight hweight cap steps retries retriesLeft samplesLeft

theorem coolingPhase_meas (sigma2 tau2 : ℝ) :
    MeasFam member fun x : AmbientSpace q.n => coolingPhase q sigma2 tau2 x := by
  have hc := (collectSamples_meas q hm sigma2 (gaussianRatioWeight sigma2 tau2)
    (by unfold gaussianRatioWeight; fun_prop) (maxProposals q sigma2) (walkSteps q sigma2)
    (maxRetries q) (maxRetries q) (phaseSampleCount q sigma2)).comp
    (φ := fun x : AmbientSpace q.n => ((0 : ℝ), scaleFactor q • x)) (by fun_prop)
  have hk := MeasFam.option (member := member) (β := ℝ × AmbientSpace q.n)
    (f := fun _ : AmbientSpace q.n =>
      (TapeProgram.pure none : TapeProgram q.n (Option (ℝ × AmbientSpace q.n))))
    (g := fun p : AmbientSpace q.n × (ℝ × AmbientSpace q.n) =>
      TapeProgram.pure (some (p.2.1 / (phaseSampleCount q sigma2 : ℝ),
        (scaleFactor q)⁻¹ • p.2.2)))
    (MeasFam.pure measurable_const)
    (MeasFam.pure (g := fun p : AmbientSpace q.n × (ℝ × AmbientSpace q.n) =>
      some (p.2.1 / (phaseSampleCount q sigma2 : ℝ), (scaleFactor q)⁻¹ • p.2.2))
      (measurable_some.comp (by fun_prop)))
  refine MeasFam.congr (MeasFam.bind hc hk) fun x => ?_
  simp only [coolingPhase]
  congr 1
  funext o
  rcases o with _ | ⟨total, y⟩ <;> rfl

theorem uniformPhase_meas (sigma2 : ℝ) :
    MeasFam member fun x : AmbientSpace q.n => uniformPhase q sigma2 x := by
  have hc := (collectSamples_meas q hm sigma2 (uniformRatioWeight sigma2)
    (by unfold uniformRatioWeight; fun_prop) (maxProposals q sigma2) (walkSteps q sigma2)
    (maxRetries q) (maxRetries q) (sampleCount q)).comp
    (φ := fun x : AmbientSpace q.n => ((0 : ℝ), scaleFactor q • x)) (by fun_prop)
  have hk := MeasFam.option (member := member) (β := ℝ × AmbientSpace q.n)
    (f := fun _ : AmbientSpace q.n => (TapeProgram.pure none : TapeProgram q.n (Option ℝ)))
    (g := fun p : AmbientSpace q.n × (ℝ × AmbientSpace q.n) =>
      TapeProgram.pure (some (p.2.1 / (sampleCount q : ℝ))))
    (MeasFam.pure measurable_const)
    (MeasFam.pure (g := fun p : AmbientSpace q.n × (ℝ × AmbientSpace q.n) =>
      some (p.2.1 / (sampleCount q : ℝ))) (measurable_some.comp (by fun_prop)))
  refine MeasFam.congr (MeasFam.bind hc hk) fun x => ?_
  simp only [uniformPhase]
  congr 1
  funext o
  rcases o with _ | ⟨total, y⟩ <;> rfl

theorem initialSample_meas : MeasFam member fun _ : Unit => initialSample q := by
  refine MeasFam.bindGaussian ?_
  refine MeasFam.bindIsMember hm
    (x := fun p : Unit × AmbientSpace q.n => Real.sqrt (initialVariance q) • p.2)
    (by fun_prop) ?_
  refine MeasFam.pure ?_
  refine Measurable.ite ?_ (measurable_some.comp (by fun_prop)) measurable_const
  measurability

theorem coolingPhases_meas :
    ∀ variances : List ℝ,
      MeasFam member fun x : AmbientSpace q.n => coolingPhases q variances x
  | [] => MeasFam.congr (MeasFam.pure (g := fun x : AmbientSpace q.n => some ((1 : ℝ), x))
      (measurable_some.comp (by fun_prop))) fun _ => rfl
  | [_] => MeasFam.congr (MeasFam.pure (g := fun x : AmbientSpace q.n => some ((1 : ℝ), x))
      (measurable_some.comp (by fun_prop))) fun _ => rfl
  | sigma2 :: tau2 :: rest => by
      have hrest := coolingPhases_meas (tau2 :: rest)
      -- the inner continuation, given the first phase's `(W, y)`
      have hinner := MeasFam.bind (member := member)
        (f := fun p : AmbientSpace q.n × (ℝ × AmbientSpace q.n) =>
          coolingPhases q (tau2 :: rest) p.2.2)
        (hrest.comp (φ := fun p : AmbientSpace q.n × (ℝ × AmbientSpace q.n) => p.2.2)
          (by fun_prop))
        (MeasFam.option (β := ℝ × AmbientSpace q.n)
          (f := fun _ : AmbientSpace q.n × (ℝ × AmbientSpace q.n) =>
            (TapeProgram.pure none : TapeProgram q.n (Option (ℝ × AmbientSpace q.n))))
          (MeasFam.pure measurable_const)
          (MeasFam.pure (g := fun p : (AmbientSpace q.n × (ℝ × AmbientSpace q.n)) ×
            (ℝ × AmbientSpace q.n) => some (p.1.2.1 * p.2.1, p.2.2))
            (measurable_some.comp (by fun_prop))))
      have hk := MeasFam.option (member := member) (β := ℝ × AmbientSpace q.n)
        (f := fun _ : AmbientSpace q.n =>
          (TapeProgram.pure none : TapeProgram q.n (Option (ℝ × AmbientSpace q.n))))
        (MeasFam.pure measurable_const) hinner
      refine MeasFam.congr (MeasFam.bind (coolingPhase_meas q hm sigma2 tau2) hk) fun x => ?_
      rw [coolingPhases]
      congr 1
      funext o
      rcases o with _ | ⟨W, y⟩
      · rfl
      · dsimp only
        congr 1
        funext o'
        rcases o' with _ | ⟨product, z⟩ <;> rfl

theorem figureOneRun_meas : MeasFam member fun _ : Unit => figureOneRun q := by
  have hU := MeasFam.bind (member := member)
    (f := fun p : (Unit × AmbientSpace q.n) × (ℝ × AmbientSpace q.n) =>
      uniformPhase q (terminalVariance q) p.2.2)
    ((uniformPhase_meas q hm _).comp (φ := fun p : (Unit × AmbientSpace q.n) ×
      (ℝ × AmbientSpace q.n) => p.2.2) (by fun_prop))
    (MeasFam.option (β := ℝ)
      (f := fun _ : (Unit × AmbientSpace q.n) × (ℝ × AmbientSpace q.n) =>
        (TapeProgram.pure 0 : TapeProgram q.n ℝ))
      (MeasFam.pure measurable_const)
      (MeasFam.pure (g := fun p : (((Unit × AmbientSpace q.n) × (ℝ × AmbientSpace q.n)) × ℝ) =>
        initialGaussianIntegral q * p.1.2.1 * p.2) (by fun_prop)))
  have hC := MeasFam.bind (member := member)
    (f := fun p : Unit × AmbientSpace q.n => coolingPhases q (coolingSchedule q) p.2)
    ((coolingPhases_meas q hm _).comp (φ := fun p : Unit × AmbientSpace q.n => p.2)
      (by fun_prop))
    (MeasFam.option (β := ℝ × AmbientSpace q.n)
      (f := fun _ : Unit × AmbientSpace q.n => (TapeProgram.pure 0 : TapeProgram q.n ℝ))
      (MeasFam.pure measurable_const) hU)
  have hk := MeasFam.option (member := member) (β := AmbientSpace q.n)
    (f := fun _ : Unit => (TapeProgram.pure 0 : TapeProgram q.n ℝ))
    (MeasFam.pure measurable_const) hC
  refine MeasFam.congr (MeasFam.bind (initialSample_meas q hm) hk) fun _ => ?_
  simp only [figureOneRun]
  congr 1
  funext o
  rcases o with _ | x₀
  · rfl
  · dsimp only
    congr 1
    funext o'
    rcases o' with _ | ⟨product, x⟩
    · rfl
    · dsimp only
      congr 1
      funext o''
      rcases o'' with _ | U <;> rfl

end Tape

end ArlibCommunity.Algorithms.CV18
