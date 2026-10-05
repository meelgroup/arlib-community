/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyImportanceLaw
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofCollectSemantics

/-! # Successful-law domination for capped proper collectors -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open Arlib.MarkovChains
open scoped ENNReal

/-- The successful `Option` outcomes whose payload lies in `A`. -/
def optionSomeEvent {α : Type*} (A : Set α) : Set (Option α) :=
  {value | match value with
    | none => False
    | some x => x ∈ A}

/-- Discard a failed optional collector result and retain the endpoint of a
successful result.  The resulting law is generally a subprobability measure. -/
noncomputable def successfulEndpointKernel
    {S : Type*} [MeasurableSpace S] :
    Option (ℝ × S) → Measure S
  | none => 0
  | some output => Measure.dirac output.2

theorem measurable_successfulEndpointKernel
    {S : Type*} [MeasurableSpace S] :
    Measurable (successfulEndpointKernel : Option (ℝ × S) → Measure S) := by
  have hsome : Measurable fun output : ℝ × S => Measure.dirac output.2 :=
    Measure.measurable_dirac.comp measurable_snd
  convert Measurable.optionElim (0 : Measure S) hsome using 1
  funext output
  cases output <;> rfl

noncomputable def successfulEndpointLaw
    {S : Type*} [MeasurableSpace S]
    (L : Measure (Option (ℝ × S))) : Measure S :=
  L.bind successfulEndpointKernel

theorem measurableSet_optionSomeEvent {α : Type*} [MeasurableSpace α]
    {A : Set α} (hA : MeasurableSet A) :
    MeasurableSet (optionSomeEvent A) := by
  classical
  let member : α → Bool := fun x => if x ∈ A then true else false
  have hmember : Measurable member :=
    Measurable.ite hA measurable_const measurable_const
  have hoption : Measurable fun value : Option α =>
      match value with
      | none => false
      | some x => member x :=
    Measurable.optionElim false hmember
  rw [show optionSomeEvent A = (fun value : Option α =>
      match value with
      | none => false
      | some x => member x) ⁻¹' {true} by
    ext value
    cases value with
    | none => simp [optionSomeEvent]
    | some x =>
        by_cases hx : x ∈ A <;> simp [optionSomeEvent, member, hx]]
  exact hoption (measurableSet_singleton true)

theorem successfulEndpointLaw_apply
    {S : Type*} [MeasurableSpace S]
    (L : Measure (Option (ℝ × S))) {B : Set S} (hB : MeasurableSet B) :
    successfulEndpointLaw L B =
      L (optionSomeEvent ((fun output : ℝ × S => output.2) ⁻¹' B)) := by
  rw [successfulEndpointLaw,
    Measure.bind_apply hB measurable_successfulEndpointKernel.aemeasurable]
  have hevent : MeasurableSet
      (optionSomeEvent ((fun output : ℝ × S => output.2) ⁻¹' B)) :=
    measurableSet_optionSomeEvent (measurable_snd hB)
  have hfun : (fun output : Option (ℝ × S) =>
      successfulEndpointKernel output B) =
      (optionSomeEvent ((fun output : ℝ × S => output.2) ⁻¹' B)).indicator 1 := by
    funext output
    cases output with
    | none => simp [successfulEndpointKernel, optionSomeEvent]
    | some value =>
        rw [successfulEndpointKernel, Measure.dirac_apply' _ hB]
        by_cases hv : value.2 ∈ B <;>
          simp [optionSomeEvent, hv]
  rw [hfun, lintegral_indicator_one hevent]

/-- The uncapped collector: advance `remainingProper` ideal proper steps,
record the first observation, then use full `properStride` blocks. -/
noncomputable def idealProperCollectLawAux
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) (f : S → ℝ) (properStride : ℕ) :
    ℕ → ℕ → ℝ → S → Measure (ℝ × S)
  | _, 0, total, current => Measure.dirac (total, current)
  | remainingProper, samples + 1, total, current =>
      ((P ^ remainingProper) current).bind fun first =>
        (frontMarkovCollectLaw (P ^ properStride) f samples first).map fun tail =>
          (total + f first + tail.1, tail.2)

noncomputable def idealProperCollectLaw
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) (f : S → ℝ)
    (properStride samples : ℕ) (current : S) : Measure (ℝ × S) :=
  idealProperCollectLawAux P f properStride properStride samples 0 current

theorem idealProperCollectLawAux_measurable_and_probability
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {f : S → ℝ} (hf : Measurable f) (properStride : ℕ) :
    ∀ samples remainingProper,
      Measurable (fun state : ℝ × S =>
        idealProperCollectLawAux P f properStride remainingProper samples
          state.1 state.2) ∧
      ∀ total current, IsProbabilityMeasure
        (idealProperCollectLawAux P f properStride remainingProper samples
          total current) := by
  intro samples remainingProper
  cases samples with
  | zero =>
      simp only [idealProperCollectLawAux]
      constructor
      · exact Measure.measurable_dirac.comp <|
          measurable_fst.prodMk measurable_snd
      · intro total current
        infer_instance
  | succ samples =>
      let R := P ^ remainingProper
      let B := P ^ properStride
      let tail : (ℝ × S) → S → Measure (ℝ × S) := fun state first =>
        (frontMarkovCollectLaw B f samples first).map fun rest =>
          (state.1 + f first + rest.1, rest.2)
      have hfront := frontMarkovCollectLaw_measurable_and_probability B hf samples
      have htail : Measurable fun p : (ℝ × S) × S => tail p.1 p.2 := by
        dsimp only [tail]
        apply measurable_measure_map_param_variable
          (hfront.1.comp measurable_snd)
          (fun p => hfront.2 p.2)
        exact (((measurable_fst.comp
            (measurable_fst.comp measurable_fst)).add
          (hf.comp (measurable_snd.comp measurable_fst))).add
            (measurable_fst.comp measurable_snd)).prodMk
              (measurable_snd.comp measurable_snd)
      have htailProb : ∀ state first,
          IsProbabilityMeasure (tail state first) := by
        intro state first
        dsimp only [tail]
        let _ : IsProbabilityMeasure (frontMarkovCollectLaw B f samples first) :=
          hfront.2 first
        exact Measure.isProbabilityMeasure_map (by fun_prop)
      simp only [idealProperCollectLawAux]
      constructor
      · change Measurable fun state : ℝ × S =>
          (R state.2).bind (tail state)
        exact measurable_measure_bind_param_variable
          (R.measurable.comp measurable_snd)
          (fun state => IsMarkovKernel.isProbabilityMeasure state.2)
          htail
      · intro total current
        change IsProbabilityMeasure ((R current).bind (tail (total, current)))
        exact MeasureTheory.isProbabilityMeasure_bind
          (htail.comp
            (measurable_const.prodMk measurable_id)).aemeasurable <|
          ae_of_all _ (htailProb (total, current))

/-- At a full stride, the closed-form ideal law is exactly the usual
front-recursive block-kernel collector, with an arbitrary accumulated prefix. -/
theorem idealProperCollectLawAux_stride_eq_front
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {f : S → ℝ} (hf : Measurable f) (properStride samples : ℕ)
    (total : ℝ) (current : S) :
    idealProperCollectLawAux P f properStride properStride samples total current =
      (frontMarkovCollectLaw (P ^ properStride) f samples current).map
        (fun tail => (total + tail.1, tail.2)) := by
  cases samples with
  | zero =>
      simp only [idealProperCollectLawAux, frontMarkovCollectLaw]
      rw [Measure.map_dirac' (by fun_prop)]
      simp
  | succ samples =>
      let B := P ^ properStride
      let F : S → Measure (ℝ × S) := fun first =>
        (frontMarkovCollectLaw B f samples first).map fun rest =>
          (f first + rest.1, rest.2)
      have hfront := frontMarkovCollectLaw_measurable_and_probability B hf samples
      have hF : Measurable F := by
        dsimp only [F]
        apply measurable_measure_map_param_variable hfront.1 hfront.2
        exact ((hf.comp measurable_fst).add
          (measurable_fst.comp measurable_snd)).prodMk
            (measurable_snd.comp measurable_snd)
      rw [idealProperCollectLawAux, frontMarkovCollectLaw]
      change (B current).bind (fun first =>
          (frontMarkovCollectLaw B f samples first).map fun rest =>
            (total + f first + rest.1, rest.2)) =
        ((B current).bind F).map (fun tail => (total + tail.1, tail.2))
      rw [map_bind_eq_bind_map_of_measurable (B current) hF (by fun_prop)]
      apply Measure.bind_congr_right
      filter_upwards with first
      dsimp only [F]
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext rest
      simp only [Function.comp_apply]
      congr 1
      ring

/-- With no proper steps remaining, the current state is observed immediately
and the next full stride begins. -/
theorem idealProperCollectLawAux_zero_succ
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {f : S → ℝ} (hf : Measurable f) (properStride samples : ℕ)
    (total : ℝ) (current : S) :
    idealProperCollectLawAux P f properStride 0 (samples + 1) total current =
      idealProperCollectLawAux P f properStride properStride samples
        (total + f current) current := by
  rw [idealProperCollectLawAux_stride_eq_front P hf]
  simp only [idealProperCollectLawAux, pow_zero]
  change (Measure.dirac current).bind (fun first =>
      (frontMarkovCollectLaw (P ^ properStride) f samples first).map fun rest =>
        (total + f first + rest.1, rest.2)) = _
  have htail : Measurable fun first =>
      (frontMarkovCollectLaw (P ^ properStride) f samples first).map fun rest =>
        (total + f first + rest.1, rest.2) := by
    have hfront := frontMarkovCollectLaw_measurable_and_probability
      (P ^ properStride) hf samples
    apply measurable_measure_map_param_variable hfront.1 hfront.2
    fun_prop
  rw [Measure.dirac_bind htail]

/-- One remaining ideal proper step can be exposed at the front. -/
theorem idealProperCollectLawAux_succ_succ
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {f : S → ℝ} (hf : Measurable f) (properStride remainingProper samples : ℕ)
    (total : ℝ) (current : S) :
    idealProperCollectLawAux P f properStride (remainingProper + 1)
        (samples + 1) total current =
      (P current).bind fun next =>
        idealProperCollectLawAux P f properStride remainingProper
          (samples + 1) total next := by
  let F : S → Measure (ℝ × S) := fun first =>
    (frontMarkovCollectLaw (P ^ properStride) f samples first).map fun rest =>
      (total + f first + rest.1, rest.2)
  have hF : Measurable F := by
    dsimp only [F]
    have hfront := frontMarkovCollectLaw_measurable_and_probability
      (P ^ properStride) hf samples
    apply measurable_measure_map_param_variable hfront.1 hfront.2
    fun_prop
  simp only [idealProperCollectLawAux]
  rw [pow_succ]
  change (((P ^ remainingProper) ∘ₖ P) current).bind F =
    (P current).bind fun next => ((P ^ remainingProper) next).bind F
  change (((P current).bind fun next => (P ^ remainingProper) next).bind F) = _
  exact Measure.bind_bind
    (P ^ remainingProper).measurable.aemeasurable hF.aemeasurable

theorem idealProperCollectLaw_eq_frontMarkovCollectLaw
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {f : S → ℝ} (hf : Measurable f) (properStride samples : ℕ)
    (current : S) :
    idealProperCollectLaw P f properStride samples current =
      frontMarkovCollectLaw (P ^ properStride) f samples current := by
  unfold idealProperCollectLaw
  rw [idealProperCollectLawAux_stride_eq_front P hf]
  simp only [zero_add]
  rw [show (fun tail : ℝ × S => (tail.1, tail.2)) = id by
    funext tail
    rfl, Measure.map_id]

/-- Subtracting a constant from every observation is equivalent to subtracting
`samples * m` from the final accumulated sum. -/
theorem frontMarkovCollectLaw_map_sub_const
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {f : S → ℝ} (hf : Measurable f) (m : ℝ) : ∀ samples current,
    (frontMarkovCollectLaw P f samples current).map
        (fun output => (output.1 - (samples : ℝ) * m, output.2)) =
      frontMarkovCollectLaw P (fun x => f x - m) samples current := by
  intro samples
  induction samples with
  | zero =>
      intro current
      simp only [frontMarkovCollectLaw, Nat.cast_zero, zero_mul, sub_zero]
      rw [Measure.map_dirac' (by fun_prop)]
  | succ samples ih =>
      intro current
      let T : S → Measure (ℝ × S) := fun next =>
        (frontMarkovCollectLaw P f samples next).map fun tail =>
          (f next + tail.1, tail.2)
      have hT : Measurable T := by
        dsimp only [T]
        have hfront := frontMarkovCollectLaw_measurable_and_probability P hf samples
        apply measurable_measure_map_param_variable hfront.1 hfront.2
        fun_prop
      rw [frontMarkovCollectLaw, frontMarkovCollectLaw]
      change ((P current).bind T).map
          (fun output =>
            (output.1 - ((samples + 1 : ℕ) : ℝ) * m, output.2)) = _
      rw [map_bind_eq_bind_map_of_measurable (P current) hT (by fun_prop)]
      apply Measure.bind_congr_right
      filter_upwards with next
      dsimp only [T]
      rw [← ih next]
      rw [Measure.map_map (by fun_prop) (by fun_prop),
        Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext tail
      simp only [Function.comp_apply]
      congr 1
      push_cast
      ring

/-- The successful part of the globally capped executable proper collector is
dominated by the uncapped lazy-speedy collector.  The missing mass is exactly
the explicit `none` outcome caused by exhausting the raw-proposal cap. -/
theorem cappedProperCollectLawAux_optionSomeEvent_le_ideal
    {n : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (delta s : ℝ) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Measurable f) (properStride : ℕ) :
    ∀ rawCap remainingProper samples total current A,
      MeasurableSet A →
      cappedProperCollectLawAux
          (lazyProperProposalGaussianAux K hK delta s) f properStride
          rawCap remainingProper samples total current (optionSomeEvent A) ≤
        idealProperCollectLawAux
          (lazy (speedyMetropolisGaussian K delta s)) f properStride
          remainingProper samples total current A := by
  intro rawCap
  induction rawCap with
  | zero =>
      intro remainingProper samples
      induction samples generalizing remainingProper with
      | zero =>
          intro total current A hA
          simp only [cappedProperCollectLawAux, idealProperCollectLawAux]
          rw [Measure.dirac_apply' _ (measurableSet_optionSomeEvent hA),
            Measure.dirac_apply' _ hA]
          rfl
      | succ samples ihSamples =>
          intro total current A hA
          cases remainingProper with
          | zero =>
              rw [cappedProperCollectLawAux,
                idealProperCollectLawAux_zero_succ
                  (lazy (speedyMetropolisGaussian K delta s)) hf]
              exact ihSamples properStride (total + f current) current A hA
          | succ remainingProper =>
              simp only [cappedProperCollectLawAux]
              rw [Measure.dirac_apply' _ (measurableSet_optionSomeEvent hA)]
              simp [optionSomeEvent]
  | succ rawCap ihRaw =>
      intro remainingProper samples
      induction samples generalizing remainingProper with
      | zero =>
          intro total current A hA
          simp only [cappedProperCollectLawAux, idealProperCollectLawAux]
          rw [Measure.dirac_apply' _ (measurableSet_optionSomeEvent hA),
            Measure.dirac_apply' _ hA]
          rfl
      | succ samples ihSamples =>
          intro total current A hA
          cases remainingProper with
          | zero =>
              rw [cappedProperCollectLawAux,
                idealProperCollectLawAux_zero_succ
                  (lazy (speedyMetropolisGaussian K delta s)) hf]
              exact ihSamples properStride (total + f current) current A hA
          | succ remainingProper =>
              let P : Kernel (EuclideanSpace ℝ (Fin n))
                  (EuclideanSpace ℝ (Fin n)) :=
                lazy (speedyMetropolisGaussian K delta s)
              let C : Bool × EuclideanSpace ℝ (Fin n) →
                  Measure (Option (ℝ × EuclideanSpace ℝ (Fin n))) :=
                fun result =>
                  if result.1 then
                    match remainingProper with
                    | 0 => cappedProperCollectLawAux
                        (lazyProperProposalGaussianAux K hK delta s) f properStride
                        rawCap properStride samples (total + f result.2) result.2
                    | nextRemaining + 1 => cappedProperCollectLawAux
                        (lazyProperProposalGaussianAux K hK delta s) f properStride
                        rawCap (nextRemaining + 1) (samples + 1) total result.2
                  else cappedProperCollectLawAux
                    (lazyProperProposalGaussianAux K hK delta s) f properStride
                    rawCap (remainingProper + 1) (samples + 1) total result.2
              have hC : Measurable C := by
                dsimp only [C]
                apply Measurable.ite
                · exact measurable_fst (measurableSet_singleton true)
                · cases remainingProper with
                  | zero =>
                      exact (cappedProperCollectLawAux_measurable_and_probability
                        (lazyProperProposalGaussianAux K hK delta s) hf properStride
                        rawCap properStride samples).1.comp <|
                          ((measurable_const.add (hf.comp measurable_snd)).prodMk
                            measurable_snd)
                  | succ nextRemaining =>
                      exact (cappedProperCollectLawAux_measurable_and_probability
                        (lazyProperProposalGaussianAux K hK delta s) hf properStride
                        rawCap (nextRemaining + 1) (samples + 1)).1.comp <|
                          measurable_const.prodMk measurable_snd
                · exact (cappedProperCollectLawAux_measurable_and_probability
                    (lazyProperProposalGaussianAux K hK delta s) hf properStride
                    rawCap (remainingProper + 1) (samples + 1)).1.comp <|
                      measurable_const.prodMk measurable_snd
              have hsome := measurableSet_optionSomeEvent hA
              let g : Bool × EuclideanSpace ℝ (Fin n) → ℝ≥0∞ :=
                fun result => C result (optionSomeEvent A)
              have hg : Measurable g :=
                (Measure.measurable_coe hsome).comp hC
              let p : ℝ≥0∞ := ell K delta current
              have hp : p ≤ 1 := ell_le_one K delta current
              have htrue : Measurable
                  (fun y : EuclideanSpace ℝ (Fin n) => (true, y)) := by fun_prop
              have hsplit : (∫⁻ result, g result
                    ∂lazyProperProposalGaussianAux K hK delta s current) =
                  p * (∫⁻ next, g (true, next) ∂P current) +
                    (1 - p) * g (false, current) := by
                change (∫⁻ result, g result ∂
                    (p • (P current).map (fun y => (true, y)) +
                      (1 - p) • Measure.dirac (false, current))) = _
                rw [lintegral_add_measure, lintegral_smul_measure,
                  lintegral_smul_measure, lintegral_map hg htrue,
                  lintegral_dirac' _ hg]
                simp only [smul_eq_mul]
              have hP : (∫⁻ next, g (true, next) ∂P current) ≤
                  idealProperCollectLawAux P f properStride
                    (remainingProper + 1) (samples + 1) total current A := by
                rw [idealProperCollectLawAux_succ_succ P hf]
                rw [Measure.bind_apply hA]
                · apply lintegral_mono
                  intro next
                  cases remainingProper with
                  | zero =>
                      dsimp only [g, C]
                      simp only [if_true]
                      rw [idealProperCollectLawAux_zero_succ P hf]
                      exact ihRaw properStride samples (total + f next) next A hA
                  | succ nextRemaining =>
                      dsimp only [g, C]
                      simp only [if_true]
                      exact ihRaw (nextRemaining + 1) (samples + 1)
                        total next A hA
                · exact ((idealProperCollectLawAux_measurable_and_probability
                    P hf properStride (samples + 1) remainingProper).1.comp
                      (measurable_const.prodMk measurable_id)).aemeasurable
              have hstay : g (false, current) ≤
                  idealProperCollectLawAux P f properStride
                    (remainingProper + 1) (samples + 1) total current A := by
                dsimp only [g, C]
                simp only [Bool.false_eq_true, if_false]
                exact ihRaw (remainingProper + 1) (samples + 1)
                  total current A hA
              rw [cappedProperCollectLawAux]
              change ((lazyProperProposalGaussianAux K hK delta s current).bind C)
                (optionSomeEvent A) ≤ _
              rw [Measure.bind_apply hsome hC.aemeasurable]
              change (∫⁻ result, g result
                ∂lazyProperProposalGaussianAux K hK delta s current) ≤ _
              rw [hsplit]
              calc
                p * (∫⁻ next, g (true, next) ∂P current) +
                      (1 - p) * g (false, current) ≤
                    p * idealProperCollectLawAux P f properStride
                        (remainingProper + 1) (samples + 1) total current A +
                      (1 - p) * idealProperCollectLawAux P f properStride
                        (remainingProper + 1) (samples + 1) total current A := by
                  gcongr
                _ = idealProperCollectLawAux P f properStride
                      (remainingProper + 1) (samples + 1) total current A := by
                  rw [← add_mul, add_tsub_cancel_of_le hp, one_mul]

/-- Public, zero-initialized form of successful-law domination. -/
theorem cappedProperCollectLaw_optionSomeEvent_le_frontMarkovCollectLaw
    {n : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (delta s : ℝ) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Measurable f) (rawCap properStride samples : ℕ)
    (current : EuclideanSpace ℝ (Fin n)) {A : Set (ℝ ×
      EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) :
    cappedProperCollectLaw
        (lazyProperProposalGaussianAux K hK delta s) f
        rawCap properStride samples current (optionSomeEvent A) ≤
      frontMarkovCollectLaw
        ((lazy (speedyMetropolisGaussian K delta s)) ^ properStride)
        f samples current A := by
  unfold cappedProperCollectLaw
  calc
    _ ≤ idealProperCollectLawAux
          (lazy (speedyMetropolisGaussian K delta s)) f properStride
          properStride samples 0 current A :=
      cappedProperCollectLawAux_optionSomeEvent_le_ideal
        K hK delta s hf properStride rawCap properStride samples 0 current A hA
    _ = _ := by
      rw [idealProperCollectLawAux_stride_eq_front
        (lazy (speedyMetropolisGaussian K delta s)) hf]
      rw [Measure.map_apply (by fun_prop) hA]
      congr 1
      ext tail
      simp

/-- Domination remains valid after drawing the initial state from an
arbitrary measure.  No conditioning or probability normalization is used. -/
theorem bind_cappedProperCollectLaw_optionSomeEvent_le_frontMarkovCollectLaw
    {n : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (delta s : ℝ) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Measurable f) (rawCap properStride samples : ℕ)
    (mu : Measure (EuclideanSpace ℝ (Fin n)))
    {A : Set (ℝ × EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) :
    (mu.bind fun current => cappedProperCollectLaw
        (lazyProperProposalGaussianAux K hK delta s) f
        rawCap properStride samples current) (optionSomeEvent A) ≤
      (mu.bind <| frontMarkovCollectLaw
        ((lazy (speedyMetropolisGaussian K delta s)) ^ properStride)
        f samples) A := by
  let Q := lazyProperProposalGaussianAux K hK delta s
  let P := (lazy (speedyMetropolisGaussian K delta s)) ^ properStride
  have hcap : Measurable fun current =>
      cappedProperCollectLaw Q f rawCap properStride samples current := by
    unfold cappedProperCollectLaw
    exact (cappedProperCollectLawAux_measurable_and_probability
      Q hf properStride rawCap properStride samples).1.comp
        (measurable_const.prodMk measurable_id)
  have hfront : Measurable (frontMarkovCollectLaw P f samples) :=
    (frontMarkovCollectLaw_measurable_and_probability P hf samples).1
  rw [Measure.bind_apply (measurableSet_optionSomeEvent hA) hcap.aemeasurable,
    Measure.bind_apply hA hfront.aemeasurable]
  apply lintegral_mono
  intro current
  exact cappedProperCollectLaw_optionSomeEvent_le_frontMarkovCollectLaw
    K hK delta s hf rawCap properStride samples current hA

/-- The successful endpoint sublaw is dominated by the ordinary endpoint of
the ideal lazy-speedy trajectory. -/
theorem successfulEndpointLaw_bind_cappedProperCollectLaw_le_iterate
    {n : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (delta s : ℝ) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Measurable f) (rawCap properStride samples : ℕ)
    (mu : Measure (EuclideanSpace ℝ (Fin n))) :
    successfulEndpointLaw
        (mu.bind fun current => cappedProperCollectLaw
          (lazyProperProposalGaussianAux K hK delta s) f
          rawCap properStride samples current) ≤
      iterate ((lazy (speedyMetropolisGaussian K delta s)) ^ properStride)
        mu samples := by
  let P := (lazy (speedyMetropolisGaussian K delta s)) ^ properStride
  apply Measure.le_iff.mpr
  intro B hB
  rw [successfulEndpointLaw_apply _ hB]
  calc
    (mu.bind fun current => cappedProperCollectLaw
        (lazyProperProposalGaussianAux K hK delta s) f
        rawCap properStride samples current)
        (optionSomeEvent ((fun output : ℝ × EuclideanSpace ℝ (Fin n) =>
          output.2) ⁻¹' B)) ≤
      (mu.bind <| frontMarkovCollectLaw P f samples)
        ((fun output : ℝ × EuclideanSpace ℝ (Fin n) => output.2) ⁻¹' B) :=
      bind_cappedProperCollectLaw_optionSomeEvent_le_frontMarkovCollectLaw
        K hK delta s hf rawCap properStride samples mu (measurable_snd hB)
    _ = ((markovSumLaw P f samples mu).map
        (fun stateSum => (stateSum.2, stateSum.1)))
          ((fun output : ℝ × EuclideanSpace ℝ (Fin n) => output.2) ⁻¹' B) := by
      rw [bind_frontMarkovCollectLaw_eq_markovSumLaw_map_swap P hf]
    _ = (markovSumLaw P f samples mu)
        ((fun stateSum : EuclideanSpace ℝ (Fin n) × ℝ => stateSum.1) ⁻¹' B) := by
      rw [Measure.map_apply (by fun_prop) (measurable_snd hB)]
      rfl
    _ = ((markovSumLaw P f samples mu).map
        (fun stateSum : EuclideanSpace ℝ (Fin n) × ℝ => stateSum.1)) B := by
      rw [Measure.map_apply (by fun_prop) hB]
    _ = iterate P mu samples B := by
      rw [markovSumLaw_map_fst P hf]

/-- Consequently a warm initial law yields an equally warm successful
endpoint sublaw; loss of success mass never worsens warmness. -/
theorem successfulEndpointLaw_bind_cappedProperCollectLaw_isWarm
    {n : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (delta s : ℝ) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Measurable f) (rawCap properStride samples : ℕ)
    {mu pi : Measure (EuclideanSpace ℝ (Fin n))} {M : ℝ≥0∞}
    (hwarm : Arlib.IsWarm M mu pi)
    (hinv : Kernel.Invariant
      ((lazy (speedyMetropolisGaussian K delta s)) ^ properStride) pi) :
    Arlib.IsWarm M
      (successfulEndpointLaw
        (mu.bind fun current => cappedProperCollectLaw
          (lazyProperProposalGaussianAux K hK delta s) f
          rawCap properStride samples current)) pi := by
  let P := (lazy (speedyMetropolisGaussian K delta s)) ^ properStride
  have hle := successfulEndpointLaw_bind_cappedProperCollectLaw_le_iterate
    K hK delta s hf rawCap properStride samples mu
  have hwarmIter : Arlib.IsWarm M (iterate P mu samples) pi :=
    isWarm_iterate_of_invariant hwarm hinv samples
  intro B hB
  exact (Measure.le_iff.mp hle B hB).trans (hwarmIter B hB)

/-- Warm-start concentration for the successful output of a capped proper
collector.  The cap-failure outcome is deliberately excluded here and can be
combined separately with the explicit cutoff theorem. -/
theorem bind_cappedProperCollectLaw_success_deviation_le_of_isWarm
    {n : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (delta s : ℝ) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Measurable f) (rawCap properStride samples : ℕ)
    {mu pi : Measure (EuclideanSpace ℝ (Fin n))}
    [IsProbabilityMeasure pi]
    (hrev : IsReversible
      ((lazy (speedyMetropolisGaussian K delta s)) ^ properStride) pi)
    (hpsd : HasNonnegSpectrum
      ((lazy (speedyMetropolisGaussian K delta s)) ^ properStride) pi)
    (hne : (rayleighSet
      ((lazy (speedyMetropolisGaussian K delta s)) ^ properStride) pi).Nonempty)
    (m : ℝ)
    (hmean : ∫ x, (f x - m) ∂pi = 0)
    (hmem : MemLp (fun x => f x - m) 2 pi)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ x, |f x - m| ≤ B)
    (hgap : 0 < spectralGap
      ((lazy (speedyMetropolisGaussian K delta s)) ^ properStride) pi)
    {M : ℝ≥0∞} (hwarm : Arlib.IsWarm M mu pi)
    {c : ℝ} (hc : 0 < c) :
    (mu.bind fun current => cappedProperCollectLaw
        (lazyProperProposalGaussianAux K hK delta s) f
        rawCap properStride samples current)
      (optionSomeEvent {output | c ≤
        |output.1 - (samples : ℝ) * m|}) ≤
      M * ENNReal.ofReal (((samples : ℝ) *
        (3 * ((spectralGap
          ((lazy (speedyMetropolisGaussian K delta s)) ^ properStride) pi)⁻¹ *
            varianceReal pi (fun x => f x - m)))) / c ^ 2) := by
  let P := (lazy (speedyMetropolisGaussian K delta s)) ^ properStride
  let centered : EuclideanSpace ℝ (Fin n) → ℝ := fun x => f x - m
  let A : Set (ℝ × EuclideanSpace ℝ (Fin n)) :=
    {output | c ≤ |output.1 - (samples : ℝ) * m|}
  let A0 : Set (ℝ × EuclideanSpace ℝ (Fin n)) :=
    {output | c ≤ |output.1|}
  have hA : MeasurableSet A :=
    measurableSet_le measurable_const <| by fun_prop
  have hA0 : MeasurableSet A0 :=
    measurableSet_le measurable_const <| by fun_prop
  calc
    (mu.bind fun current => cappedProperCollectLaw
        (lazyProperProposalGaussianAux K hK delta s) f
        rawCap properStride samples current) (optionSomeEvent A) ≤
      (mu.bind <| frontMarkovCollectLaw P f samples) A := by
        exact bind_cappedProperCollectLaw_optionSomeEvent_le_frontMarkovCollectLaw
          K hK delta s hf rawCap properStride samples mu hA
    _ = (mu.bind <| frontMarkovCollectLaw P centered samples) A0 := by
      have hfrontF : Measurable (frontMarkovCollectLaw P f samples) :=
        (frontMarkovCollectLaw_measurable_and_probability P hf samples).1
      have hcentered : Measurable centered := hf.sub measurable_const
      have hfrontC : Measurable (frontMarkovCollectLaw P centered samples) :=
        (frontMarkovCollectLaw_measurable_and_probability P hcentered samples).1
      rw [Measure.bind_apply hA hfrontF.aemeasurable,
        Measure.bind_apply hA0 hfrontC.aemeasurable]
      apply lintegral_congr
      intro current
      have hshift := frontMarkovCollectLaw_map_sub_const P hf m samples current
      rw [← hshift, Measure.map_apply (by fun_prop) hA0]
      rfl
    _ = (markovSumLaw P centered samples mu).map
        (fun stateSum => (stateSum.2, stateSum.1)) A0 := by
      exact congrArg (fun ν : Measure (ℝ × EuclideanSpace ℝ (Fin n)) => ν A0)
        (bind_frontMarkovCollectLaw_eq_markovSumLaw_map_swap
          P (hf.sub measurable_const) samples mu)
    _ = markovSumLaw P centered samples mu
        {stateSum | c ≤ |stateSum.2|} := by
      rw [Measure.map_apply (by fun_prop) hA0]
      rfl
    _ ≤ M * ENNReal.ofReal (((samples : ℝ) *
        (3 * ((spectralGap P pi)⁻¹ *
          varianceReal pi centered))) / c ^ 2) :=
      markovSumLaw_meas_abs_snd_ge_le_of_isWarm P hrev hpsd hne
        (hf.sub measurable_const) hmem hmean hB hbound hgap hwarm samples hc

end ArlibCommunity.Algorithms.CV18
