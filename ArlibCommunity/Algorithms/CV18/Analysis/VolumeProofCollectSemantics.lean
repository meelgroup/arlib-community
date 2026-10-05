/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofPrimitives
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofStationary
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofMarkovVariance

/-! # Exact law of the executable CV18 weight collector -/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open Arlib.MarkovChains

/-- A finite power of a Markov kernel is again Markov. -/
instance kernelPow_isMarkovKernel {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (steps : ℕ) :
    IsMarkovKernel (P ^ steps) := by
  induction steps with
  | zero =>
      rw [pow_zero]
      change IsMarkovKernel (Kernel.id : Kernel S S)
      infer_instance
  | succ steps ih =>
      rw [pow_succ]
      change IsMarkovKernel ((P ^ steps) ∘ₖ P)
      infer_instance

/-- Front-recursive law of a Markov-chain weight collector.  Its coordinates
match the executable collector: accumulated weight first, last state second. -/
noncomputable def frontMarkovCollectLaw {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) (f : S → ℝ) : ℕ → S → Measure (ℝ × S)
  | 0, current => Measure.dirac (0, current)
  | samples + 1, current =>
      (P current).bind fun next =>
        (frontMarkovCollectLaw P f samples next).map fun tail =>
          (f next + tail.1, tail.2)

/-- The front-recursive collector law is a measurable probability kernel in
its initial state. -/
theorem frontMarkovCollectLaw_measurable_and_probability
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] {f : S → ℝ} (hf : Measurable f) :
    ∀ samples,
      Measurable (frontMarkovCollectLaw P f samples) ∧
      ∀ current, IsProbabilityMeasure
        (frontMarkovCollectLaw P f samples current) := by
  intro samples
  induction samples with
  | zero =>
      constructor
      · exact Measure.measurable_dirac.comp
          (measurable_const.prodMk measurable_id)
      · intro current
        change IsProbabilityMeasure (Measure.dirac ((0 : ℝ), current))
        infer_instance
  | succ samples ih =>
      let tailLaw : S → Measure (ℝ × S) := fun next =>
        (frontMarkovCollectLaw P f samples next).map fun tail =>
          (f next + tail.1, tail.2)
      have htail : Measurable tailLaw := by
        apply measurable_measure_map_param_variable ih.1 ih.2
        exact ((hf.comp measurable_fst).add
          (measurable_fst.comp measurable_snd)).prodMk
            (measurable_snd.comp measurable_snd)
      have htailProb : ∀ next, IsProbabilityMeasure (tailLaw next) := by
        intro next
        dsimp [tailLaw]
        let _ : IsProbabilityMeasure
            (frontMarkovCollectLaw P f samples next) := ih.2 next
        exact Measure.isProbabilityMeasure_map (by fun_prop)
      constructor
      · change Measurable fun current => (P current).bind tailLaw
        exact measurable_measure_bind_param_variable P.measurable
          (fun current => IsMarkovKernel.isProbabilityMeasure current)
          (htail.comp measurable_snd)
      · intro current
        change IsProbabilityMeasure ((P current).bind tailLaw)
        exact MeasureTheory.isProbabilityMeasure_bind htail.aemeasurable <|
          ae_of_all _ htailProb

/-- The finite Markov accumulator started from a point varies measurably with
that point. -/
theorem measurable_markovSumLaw_dirac
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] {f : S → ℝ}
    (hf : Measurable f) : ∀ samples,
    Measurable fun current => markovSumLaw P f samples (Measure.dirac current) := by
  intro samples
  induction samples with
  | zero =>
      exact (Measure.measurable_map _ (by fun_prop)).comp
        Measure.measurable_dirac
  | succ samples ih =>
      exact (Measure.measurable_bind'
        (measurable_markovSumStep P hf)).comp ih

/-- Adding a fixed prefix to the accumulator commutes with one Markov update.
This is the algebraic bridge between front- and back-recursive sums. -/
theorem markovSumStep_map_add
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] {f : S → ℝ}
    (hf : Measurable f) (mu : Measure (S × ℝ)) (c : ℝ) :
    (mu.map (fun stateSum => (stateSum.1, c + stateSum.2))).bind
        (fun stateSum => (P stateSum.1).map fun next =>
          (next, stateSum.2 + f next)) =
      (mu.bind (fun stateSum => (P stateSum.1).map fun next =>
        (next, stateSum.2 + f next))).map (fun stateSum =>
          (stateSum.1, c + stateSum.2)) := by
  let addC : S × ℝ → S × ℝ := fun stateSum =>
    (stateSum.1, c + stateSum.2)
  let Q : S × ℝ → Measure (S × ℝ) := fun stateSum =>
    (P stateSum.1).map fun next => (next, stateSum.2 + f next)
  let D : S × ℝ → Measure (S × ℝ) := fun stateSum =>
    Measure.dirac (addC stateSum)
  have hadd : Measurable addC := by fun_prop
  have hQ : Measurable Q := measurable_markovSumStep P hf
  have hD : Measurable D := Measure.measurable_dirac.comp hadd
  change Q ∘ₘ mu.map addC = (Q ∘ₘ mu).map addC
  rw [← Measure.bind_dirac_eq_map mu hadd]
  change Q ∘ₘ D ∘ₘ mu = (Q ∘ₘ mu).map addC
  rw [Measure.bind_bind hD.aemeasurable hQ.aemeasurable]
  rw [← Measure.bind_dirac_eq_map (Q ∘ₘ mu) hadd]
  change (fun stateSum => Q ∘ₘ D stateSum) ∘ₘ mu =
    D ∘ₘ Q ∘ₘ mu
  rw [Measure.bind_bind hQ.aemeasurable hD.aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards with stateSum
  rw [Measure.dirac_bind hQ (addC stateSum)]
  change Q (addC stateSum) =
    (fun x => Measure.dirac (addC x)) ∘ₘ Q stateSum
  rw [Measure.bind_dirac_eq_map _ hadd]
  dsimp [Q, addC]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext next
  simp only [Function.comp_apply]
  congr 1
  ring

/-- The usual back-recursive accumulator also admits the front-recursive
decomposition used by `collectWalkWeights`. -/
theorem markovSumLaw_dirac_succ_eq_front
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] {f : S → ℝ}
    (hf : Measurable f) : ∀ samples current,
    markovSumLaw P f (samples + 1) (Measure.dirac current) =
      (P current).bind fun next =>
        (markovSumLaw P f samples (Measure.dirac next)).map fun tail =>
          (tail.1, f next + tail.2) := by
  intro samples
  induction samples with
  | zero =>
      intro current
      simp only [markovSumLaw]
      rw [Measure.map_dirac' (by fun_prop),
        Measure.dirac_bind (measurable_markovSumStep P hf)]
      rw [← Measure.bind_dirac_eq_map _ (by fun_prop)]
      apply Measure.bind_congr_right
      filter_upwards with next
      rw [Measure.map_dirac' (by fun_prop),
        Measure.map_dirac' (by fun_prop)]
      simp
  | succ samples ih =>
      intro current
      rw [show Nat.succ samples + 1 = (samples + 1) + 1 by omega,
        markovSumLaw, ih current]
      let A : S → Measure (S × ℝ) := fun next =>
        (markovSumLaw P f samples (Measure.dirac next)).map fun tail =>
          (tail.1, f next + tail.2)
      let Q : S × ℝ → Measure (S × ℝ) := fun stateSum =>
        (P stateSum.1).map fun next => (next, stateSum.2 + f next)
      have hsource : Measurable fun next =>
          markovSumLaw P f samples (Measure.dirac next) :=
        measurable_markovSumLaw_dirac P hf samples
      have hsourceProb : ∀ next, IsProbabilityMeasure
          (markovSumLaw P f samples (Measure.dirac next)) := by
        intro next
        exact markovSumLaw_isProbabilityMeasure P hf _ samples
      have htransform : Measurable fun p : S × (S × ℝ) =>
          (p.2.1, f p.1 + p.2.2) := by fun_prop
      have hA : Measurable A := by
        exact measurable_measure_map_param_variable
          hsource hsourceProb htransform
      have hQ : Measurable Q := measurable_markovSumStep P hf
      change Q ∘ₘ A ∘ₘ P current =
        (fun next =>
          (markovSumLaw P f (samples + 1) (Measure.dirac next)).map
            fun tail => (tail.1, f next + tail.2)) ∘ₘ P current
      rw [Measure.bind_bind hA.aemeasurable hQ.aemeasurable]
      apply Measure.bind_congr_right
      filter_upwards with next
      change
        ((markovSumLaw P f samples (Measure.dirac next)).map
          (fun tail => (tail.1, f next + tail.2))).bind Q = _
      rw [markovSumStep_map_add P hf
        (markovSumLaw P f samples (Measure.dirac next)) (f next)]
      rfl

/-- Mapping after a measurable bind can be performed pointwise inside the
bind. -/
theorem map_bind_eq_bind_map_of_measurable
    {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (mu : Measure A) {F : A → Measure B} (hF : Measurable F)
    {g : B → C} (hg : Measurable g) :
    (mu.bind F).map g = mu.bind fun x => (F x).map g := by
  let D : B → Measure C := fun y => Measure.dirac (g y)
  have hD : Measurable D := Measure.measurable_dirac.comp hg
  rw [← Measure.bind_dirac_eq_map (mu.bind F) hg]
  change D ∘ₘ F ∘ₘ mu = _
  rw [Measure.bind_bind hF.aemeasurable hD.aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards with x
  exact Measure.bind_dirac_eq_map (F x) hg

/-- The executable front-recursive accumulator and the generic Markov
accumulator have exactly the same law, up to swapping their coordinates. -/
theorem frontMarkovCollectLaw_eq_markovSumLaw_map_swap
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] {f : S → ℝ}
    (hf : Measurable f) : ∀ samples current,
    frontMarkovCollectLaw P f samples current =
      (markovSumLaw P f samples (Measure.dirac current)).map fun stateSum =>
        (stateSum.2, stateSum.1) := by
  intro samples
  induction samples with
  | zero =>
      intro current
      simp only [frontMarkovCollectLaw, markovSumLaw]
      rw [Measure.map_dirac' (by fun_prop),
        Measure.map_dirac' (by fun_prop)]
  | succ samples ih =>
      intro current
      rw [frontMarkovCollectLaw]
      simp_rw [ih]
      rw [markovSumLaw_dirac_succ_eq_front P hf samples current]
      rw [map_bind_eq_bind_map_of_measurable (P current)
        (measurable_measure_map_param_variable
          (measurable_markovSumLaw_dirac P hf samples)
          (fun next => markovSumLaw_isProbabilityMeasure P hf _ samples)
          (by fun_prop)) (by fun_prop)]
      apply Measure.bind_congr_right
      filter_upwards with next
      rw [Measure.map_map (by fun_prop) (by fun_prop),
        Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1

/-- A Markov accumulator from an arbitrary initial law is the mixture of its
point-started accumulator laws. -/
theorem markovSumLaw_eq_bind_dirac
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] {f : S → ℝ}
    (hf : Measurable f) : ∀ samples (mu : Measure S),
    markovSumLaw P f samples mu =
      mu.bind fun current =>
        markovSumLaw P f samples (Measure.dirac current) := by
  intro samples
  induction samples with
  | zero =>
      intro mu
      rw [markovSumLaw, ← Measure.bind_dirac_eq_map _ (by fun_prop)]
      apply Measure.bind_congr_right
      filter_upwards with current
      rw [markovSumLaw, Measure.map_dirac' (by fun_prop)]
  | succ samples ih =>
      intro mu
      rw [markovSumLaw, ih mu]
      let F : S → Measure (S × ℝ) := fun current =>
        markovSumLaw P f samples (Measure.dirac current)
      let Q : S × ℝ → Measure (S × ℝ) := fun stateSum =>
        (P stateSum.1).map fun next => (next, stateSum.2 + f next)
      have hF : Measurable F := measurable_markovSumLaw_dirac P hf samples
      have hQ : Measurable Q := measurable_markovSumStep P hf
      change Q ∘ₘ F ∘ₘ mu = _
      rw [Measure.bind_bind hF.aemeasurable hQ.aemeasurable]
      apply Measure.bind_congr_right
      filter_upwards with current
      rfl

/-- Mixing point-started executable collector laws over an arbitrary initial
law gives the generic Markov accumulator law, with coordinates swapped. -/
theorem bind_frontMarkovCollectLaw_eq_markovSumLaw_map_swap
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] {f : S → ℝ}
    (hf : Measurable f) (samples : ℕ) (mu : Measure S) :
    mu.bind (frontMarkovCollectLaw P f samples) =
      (markovSumLaw P f samples mu).map fun stateSum =>
        (stateSum.2, stateSum.1) := by
  have hfront : frontMarkovCollectLaw P f samples = fun current =>
      (markovSumLaw P f samples (Measure.dirac current)).map fun stateSum =>
        (stateSum.2, stateSum.1) := by
    funext current
    exact frontMarkovCollectLaw_eq_markovSumLaw_map_swap P hf samples current
  rw [hfront]
  rw [markovSumLaw_eq_bind_dirac P hf samples mu]
  exact (map_bind_eq_bind_map_of_measurable mu
    (measurable_markovSumLaw_dirac P hf samples) (by fun_prop)).symm

/-- The actual `collectWalkWeights` program has exactly the front-recursive
law for the block kernel consisting of `walkSteps` raw lazy steps. -/
theorem runEstimate_collectWalkWeights_eq_frontMarkovCollectLaw
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (weight : AmbientSpace q.n → ℝ)
    (hweight : Measurable weight) (walkSteps : ℕ) : ∀ samples current,
    (collectWalkWeights q sigma2 walkSteps weight samples current).runEstimate
        oracle.query =
      frontMarkovCollectLaw
        (truncatedMetropolisKernel q I oracle sigma2 ^ walkSteps)
        weight samples current := by
  intro samples
  induction samples with
  | zero =>
      intro current
      rfl
  | succ samples ih =>
      intro current
      let P : Kernel (AmbientSpace q.n) (AmbientSpace q.n) :=
        truncatedMetropolisKernel q I oracle sigma2 ^ walkSteps
      let tailProgram : AmbientSpace q.n →
          MembershipOracleProgram q.n (ℝ × AmbientSpace q.n) := fun point =>
        (collectWalkWeights q sigma2 walkSteps weight samples point).bind fun tail =>
          .pure (weight point + tail.1, tail.2)
      have hcollect := collectWalkWeights_measurable_and_strong
        q I oracle sigma2 walkSteps weight hweight samples
      have htailOutput : ∀ point, Measurable fun tail : ℝ × AmbientSpace q.n =>
          (.pure (weight point + tail.1, tail.2) :
            MembershipOracleProgram q.n (ℝ × AmbientSpace q.n)).runEstimate
              oracle.query := by
        intro point
        simp only [MembershipOracleProgram.runEstimate]
        exact Measure.measurable_dirac.comp
          ((measurable_const.add measurable_fst).prodMk measurable_snd)
      have htailStrong : ∀ point,
          (tailProgram point).StronglyMeasurable oracle.query := by
        intro point
        exact (hcollect.2 point).bind (fun _ => by trivial) (htailOutput point)
      have htailRun : Measurable fun point =>
          (tailProgram point).runEstimate oracle.query := by
        have hsource : Measurable fun point =>
            (collectWalkWeights q sigma2 walkSteps weight samples point).runEstimate
              oracle.query := hcollect.1
        have hprob : ∀ point, IsProbabilityMeasure
            ((collectWalkWeights q sigma2 walkSteps weight samples point).runEstimate
              oracle.query) := fun point =>
          MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle.query _
            (hcollect.2 point).estimateMeasurable
        have htransform : Measurable fun p :
            AmbientSpace q.n × (ℝ × AmbientSpace q.n) =>
              (weight p.1 + p.2.1, p.2.2) :=
          ((hweight.comp measurable_fst).add
            (measurable_fst.comp measurable_snd)).prodMk
              (measurable_snd.comp measurable_snd)
        rw [show (fun point => (tailProgram point).runEstimate oracle.query) =
            fun point =>
              ((collectWalkWeights q sigma2 walkSteps weight samples point).runEstimate
                oracle.query).map fun tail =>
                  (weight point + tail.1, tail.2) by
          funext point
          unfold tailProgram
          rw [MembershipOracleProgram.runEstimate_bind oracle.query _ _
            (hcollect.2 point) (fun _ => by trivial) (htailOutput point)]
          simp only [MembershipOracleProgram.runEstimate]
          rw [Measure.bind_dirac_eq_map _ (by fun_prop)]]
        exact measurable_measure_map_param_variable hsource hprob htransform
      have hwalk := truncatedMetropolisBallWalk_measurable_and_strong
        q I oracle sigma2 walkSteps
      simp only [collectWalkWeights]
      rw [MembershipOracleProgram.runEstimate_bind oracle.query _ tailProgram
        (hwalk.2 current) htailStrong htailRun]
      rw [runEstimate_truncatedMetropolisBallWalk_eq_kernel_pow
        q I oracle sigma2 walkSteps current]
      simp_rw [show ∀ point, (tailProgram point).runEstimate oracle.query =
          (frontMarkovCollectLaw P weight samples point).map fun tail =>
            (weight point + tail.1, tail.2) by
        intro point
        unfold tailProgram
        rw [MembershipOracleProgram.runEstimate_bind oracle.query _ _
          (hcollect.2 point) (fun _ => by trivial) (htailOutput point), ih point]
        simp only [MembershipOracleProgram.runEstimate]
        rw [Measure.bind_dirac_eq_map _ (by fun_prop)]]
      rfl

/-- With a random initial point, the actual executable collector is exactly
the generic dependent Markov accumulator, up to swapping coordinates. -/
theorem bind_runEstimate_collectWalkWeights_eq_markovSumLaw_map_swap
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (weight : AmbientSpace q.n → ℝ)
    (hweight : Measurable weight) (walkSteps samples : ℕ)
    (mu : Measure (AmbientSpace q.n)) :
    mu.bind (fun current =>
      (collectWalkWeights q sigma2 walkSteps weight samples current).runEstimate
        oracle.query) =
      (markovSumLaw
        (truncatedMetropolisKernel q I oracle sigma2 ^ walkSteps)
        weight samples mu).map fun stateSum => (stateSum.2, stateSum.1) := by
  calc
    mu.bind (fun current =>
        (collectWalkWeights q sigma2 walkSteps weight samples current).runEstimate
          oracle.query) =
        mu.bind (frontMarkovCollectLaw
          (truncatedMetropolisKernel q I oracle sigma2 ^ walkSteps)
          weight samples) := by
      apply Measure.bind_congr_right
      filter_upwards with current
      exact runEstimate_collectWalkWeights_eq_frontMarkovCollectLaw
        q I oracle weight hweight walkSteps samples current
    _ = (markovSumLaw
          (truncatedMetropolisKernel q I oracle sigma2 ^ walkSteps)
          weight samples mu).map fun stateSum => (stateSum.2, stateSum.1) :=
      bind_frontMarkovCollectLaw_eq_markovSumLaw_map_swap
        (truncatedMetropolisKernel q I oracle sigma2 ^ walkSteps)
        hweight samples mu

/-- Warm-start dependent concentration for the actual executable CV18 weight
collector.  In particular, warmness is charged once for the complete sample
trajectory. -/
theorem bind_runEstimate_collectWalkWeights_meas_abs_fst_ge_le_of_isWarm
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} {weight : AmbientSpace q.n → ℝ}
    (hweight : Measurable weight) (walkSteps : ℕ)
    {mu pi : Measure (AmbientSpace q.n)}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure pi]
    (hrev : IsReversible
      (truncatedMetropolisKernel q I oracle sigma2 ^ walkSteps) pi)
    (hpsd : HasNonnegSpectrum
      (truncatedMetropolisKernel q I oracle sigma2 ^ walkSteps) pi)
    (hne : (rayleighSet
      (truncatedMetropolisKernel q I oracle sigma2 ^ walkSteps) pi).Nonempty)
    (hmem : MemLp weight 2 pi) (hmean : ∫ x, weight x ∂pi = 0)
    {B : ℝ} (hB : 0 ≤ B) (hweightBound : ∀ x, |weight x| ≤ B)
    (hgap : 0 < spectralGap
      (truncatedMetropolisKernel q I oracle sigma2 ^ walkSteps) pi)
    {M : ENNReal} (hwarm : Arlib.IsWarm M mu pi) (samples : ℕ)
    {c : ℝ} (hc : 0 < c) :
    (mu.bind fun current =>
      (collectWalkWeights q sigma2 walkSteps weight samples current).runEstimate
        oracle.query) {output | c ≤ |output.1|} ≤
      M * ENNReal.ofReal (((samples : ℝ) *
        (3 * ((spectralGap
          (truncatedMetropolisKernel q I oracle sigma2 ^ walkSteps) pi)⁻¹ *
            varianceReal pi weight))) / c ^ 2) := by
  rw [bind_runEstimate_collectWalkWeights_eq_markovSumLaw_map_swap
    q I oracle weight hweight walkSteps samples mu]
  rw [Measure.map_apply (by fun_prop)
    (measurableSet_le measurable_const (by fun_prop))]
  exact markovSumLaw_meas_abs_snd_ge_le_of_isWarm
    (truncatedMetropolisKernel q I oracle sigma2 ^ walkSteps)
    hrev hpsd hne hweight hmem hmean hB hweightBound hgap hwarm samples hc

end ArlibCommunity.Algorithms.CV18

#print axioms ArlibCommunity.Algorithms.CV18.runEstimate_collectWalkWeights_eq_frontMarkovCollectLaw
#print axioms ArlibCommunity.Algorithms.CV18.bind_runEstimate_collectWalkWeights_meas_abs_fst_ge_le_of_isWarm
