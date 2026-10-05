/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedPhaseInstantiation

/-!
# Additive exact-chance replacement for finite CV18 histories

The `exact-chance` step in the CV18 proof sequentially replaces finite-walk
draws by ideal stationary draws.  An explicit maximal coupling is stronger
than the final accuracy proof needs.  This file gives the equivalent
one-sided event-transfer interface: if each ideal prefix followed by the
executable next kernel is dominated by the corresponding ideal extension
with error `nu`, then a length-`t` executable history is dominated by the
ideal history with total error `t * nu`.

Crucially, the hypothesis is integrated against the ideal prefix law.  No
false pointwise warm-start assertion for a Dirac starting point is required.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

/-- Iterate a possibly time-inhomogeneous probability kernel. -/
noncomputable def iteratedKernelLaw
    {S : Type*} [MeasurableSpace S]
    (K : ℕ → S → Measure S) (initial : Measure S) : ℕ → Measure S
  | 0 => initial
  | t + 1 => (iteratedKernelLaw K initial t).bind (K t)

@[simp] theorem iteratedKernelLaw_zero
    {S : Type*} [MeasurableSpace S]
    (K : ℕ → S → Measure S) (initial : Measure S) :
    iteratedKernelLaw K initial 0 = initial := rfl

theorem iteratedKernelLaw_succ
    {S : Type*} [MeasurableSpace S]
    (K : ℕ → S → Measure S) (initial : Measure S) (t : ℕ) :
    iteratedKernelLaw K initial (t + 1) =
      (iteratedKernelLaw K initial t).bind (K t) := rfl

theorem iteratedKernelLaw_isProbabilityMeasure
    {S : Type*} [MeasurableSpace S]
    (K : ℕ → S → Measure S) (initial : Measure S)
    (hinitial : IsProbabilityMeasure initial)
    (hKmeas : ∀ t, Measurable (K t))
    (hKprob : ∀ t state, IsProbabilityMeasure (K t state)) :
    ∀ t, IsProbabilityMeasure (iteratedKernelLaw K initial t)
  | 0 => hinitial
  | t + 1 => by
      let _ : IsProbabilityMeasure (iteratedKernelLaw K initial t) :=
        iteratedKernelLaw_isProbabilityMeasure K initial hinitial hKmeas hKprob t
      exact MeasureTheory.isProbabilityMeasure_bind
        (hKmeas t).aemeasurable (ae_of_all _ (hKprob t))

/-- Apply the same next executable kernel to an old domination estimate, then
replace its action on the ideal prefix by the next ideal prefix.  This is the
single induction step behind the paper's additive `exact-chance` bound. -/
theorem MeasureLeUpTo.bind_then_replace
    {S : Type*} [MeasurableSpace S]
    {actual ideal nextIdeal : Measure S} {oldError stepError : ENNReal}
    (hold : MeasureLeUpTo actual ideal oldError)
    (K : S → Measure S) (hKmeas : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state))
    (hstep : MeasureLeUpTo (ideal.bind K) nextIdeal stepError) :
    MeasureLeUpTo (actual.bind K) nextIdeal (oldError + stepError) := by
  exact (hold.bind_same hKmeas hKprob).trans hstep

/-- Integrating pointwise transition TV estimates against a probability
prefix loses no extra factor.  This converts the usual per-transition mixing
statement into the integrated step premise of `iteratedKernelLaw_le`. -/
theorem tvLe_bind_of_pointwise
    {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (prefixLaw : Measure S) [IsProbabilityMeasure prefixLaw]
    (actualK idealK : S → Measure T)
    (hactualMeas : Measurable actualK) (hidealMeas : Measurable idealK)
    {nu : ENNReal}
    (hpoint : ∀ state, Arlib.TVLe (actualK state) (idealK state) nu) :
    Arlib.TVLe (prefixLaw.bind actualK) (prefixLaw.bind idealK) nu := by
  intro event hevent
  have hactualEvent : Measurable fun state => actualK state event :=
    (Measure.measurable_coe hevent).comp hactualMeas
  have hidealEvent : Measurable fun state => idealK state event :=
    (Measure.measurable_coe hevent).comp hidealMeas
  rw [Measure.bind_apply hevent hactualMeas.aemeasurable,
    Measure.bind_apply hevent hidealMeas.aemeasurable]
  constructor
  · calc
      (∫⁻ state, actualK state event ∂prefixLaw) ≤
          ∫⁻ state, idealK state event + nu ∂prefixLaw :=
        lintegral_mono fun state => (hpoint state event hevent).1
      _ = (∫⁻ state, idealK state event ∂prefixLaw) +
          ∫⁻ _state, nu ∂prefixLaw :=
        lintegral_add_left hidealEvent _
      _ = (∫⁻ state, idealK state event ∂prefixLaw) + nu := by simp
  · calc
      (∫⁻ state, idealK state event ∂prefixLaw) ≤
          ∫⁻ state, actualK state event + nu ∂prefixLaw :=
        lintegral_mono fun state => (hpoint state event hevent).2
      _ = (∫⁻ state, actualK state event ∂prefixLaw) +
          ∫⁻ _state, nu ∂prefixLaw :=
        lintegral_add_left hactualEvent _
      _ = (∫⁻ state, actualK state event ∂prefixLaw) + nu := by simp

theorem MeasureLeUpTo.bind_of_pointwise_tvLe
    {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (prefixLaw : Measure S) [IsProbabilityMeasure prefixLaw]
    (actualK idealK : S → Measure T)
    (hactualMeas : Measurable actualK) (hidealMeas : Measurable idealK)
    (hactualProb : ∀ state, IsProbabilityMeasure (actualK state))
    (hidealProb : ∀ state, IsProbabilityMeasure (idealK state))
    {nu : ENNReal}
    (hpoint : ∀ state, Arlib.TVLe (actualK state) (idealK state) nu) :
    MeasureLeUpTo (prefixLaw.bind actualK) (prefixLaw.bind idealK) nu := by
  let _ : IsProbabilityMeasure (prefixLaw.bind actualK) :=
    MeasureTheory.isProbabilityMeasure_bind hactualMeas.aemeasurable
      (ae_of_all _ hactualProb)
  let _ : IsProbabilityMeasure (prefixLaw.bind idealK) :=
    MeasureTheory.isProbabilityMeasure_bind hidealMeas.aemeasurable
      (ae_of_all _ hidealProb)
  exact MeasureLeUpTo.of_tvLe <|
    tvLe_bind_of_pointwise prefixLaw actualK idealK hactualMeas hidealMeas hpoint

/-- Nonhomogeneous sequential exact-chance replacement.  At time `i`, the
only required new estimate is the law obtained by applying the executable
kernel to the *ideal* length-`i` prefix. -/
theorem MeasureLeUpTo.iteratedKernelLaw_le
    {S : Type*} [MeasurableSpace S]
    (actualK idealK : ℕ → S → Measure S)
    (actualInitial idealInitial : Measure S)
    {initialError : ENNReal} (stepError : ℕ → ENNReal)
    (hinitial : MeasureLeUpTo actualInitial idealInitial initialError)
    (hactualMeas : ∀ i, Measurable (actualK i))
    (hactualProb : ∀ i state, IsProbabilityMeasure (actualK i state))
    (hstep : ∀ i,
      MeasureLeUpTo
        ((iteratedKernelLaw idealK idealInitial i).bind (actualK i))
        (iteratedKernelLaw idealK idealInitial (i + 1))
        (stepError i)) :
    ∀ t, MeasureLeUpTo
      (iteratedKernelLaw actualK actualInitial t)
      (iteratedKernelLaw idealK idealInitial t)
      (initialError + ∑ i ∈ Finset.range t, stepError i) := by
  intro t
  induction t with
  | zero => simpa using hinitial
  | succ t ih =>
      have hnext := MeasureLeUpTo.bind_then_replace ih (actualK t)
        (hactualMeas t) (hactualProb t) (hstep t)
      simpa only [iteratedKernelLaw_succ, Finset.sum_range_succ,
        add_assoc] using hnext

/-- Constant-error form: `t` sequential replacements cost exactly `t • nu`
in `ENNReal`, with no geometric amplification. -/
theorem MeasureLeUpTo.iteratedKernelLaw_const
    {S : Type*} [MeasurableSpace S]
    (actualK idealK : ℕ → S → Measure S)
    (actualInitial idealInitial : Measure S)
    {initialError nu : ENNReal}
    (hinitial : MeasureLeUpTo actualInitial idealInitial initialError)
    (hactualMeas : ∀ i, Measurable (actualK i))
    (hactualProb : ∀ i state, IsProbabilityMeasure (actualK i state))
    (hstep : ∀ i,
      MeasureLeUpTo
        ((iteratedKernelLaw idealK idealInitial i).bind (actualK i))
        (iteratedKernelLaw idealK idealInitial (i + 1)) nu)
    (t : ℕ) :
    MeasureLeUpTo
      (iteratedKernelLaw actualK actualInitial t)
      (iteratedKernelLaw idealK idealInitial t)
      (initialError + t • nu) := by
  simpa using MeasureLeUpTo.iteratedKernelLaw_le actualK idealK
    actualInitial idealInitial (fun _ => nu) hinitial hactualMeas
      hactualProb hstep t

/-- Starting both histories from the same law removes the initial-error term,
giving exactly the paper's `t * nu` chance of any replacement failure. -/
theorem MeasureLeUpTo.iteratedKernelLaw_exactChance
    {S : Type*} [MeasurableSpace S]
    (actualK idealK : ℕ → S → Measure S)
    (initial : Measure S) {nu : ENNReal}
    (hactualMeas : ∀ i, Measurable (actualK i))
    (hactualProb : ∀ i state, IsProbabilityMeasure (actualK i state))
    (hstep : ∀ i,
      MeasureLeUpTo
        ((iteratedKernelLaw idealK initial i).bind (actualK i))
        (iteratedKernelLaw idealK initial (i + 1)) nu)
    (t : ℕ) :
    MeasureLeUpTo
      (iteratedKernelLaw actualK initial t)
      (iteratedKernelLaw idealK initial t)
      (t • nu) := by
  simpa using MeasureLeUpTo.iteratedKernelLaw_const actualK idealK
    initial initial (MeasureLeUpTo.refl initial) hactualMeas hactualProb
      hstep t

/-- Pointwise per-transition form of exact-chance replacement. -/
theorem MeasureLeUpTo.iteratedKernelLaw_exactChance_of_pointwise
    {S : Type*} [MeasurableSpace S]
    (actualK idealK : ℕ → S → Measure S)
    (initial : Measure S) [IsProbabilityMeasure initial]
    {nu : ENNReal}
    (hactualMeas : ∀ i, Measurable (actualK i))
    (hactualProb : ∀ i state, IsProbabilityMeasure (actualK i state))
    (hidealMeas : ∀ i, Measurable (idealK i))
    (hidealProb : ∀ i state, IsProbabilityMeasure (idealK i state))
    (hpoint : ∀ i state,
      Arlib.TVLe (actualK i state) (idealK i state) nu)
    (t : ℕ) :
    MeasureLeUpTo
      (iteratedKernelLaw actualK initial t)
      (iteratedKernelLaw idealK initial t)
      (t • nu) := by
  apply MeasureLeUpTo.iteratedKernelLaw_exactChance actualK idealK initial
    hactualMeas hactualProb
  intro i
  let _ : IsProbabilityMeasure (iteratedKernelLaw idealK initial i) :=
    iteratedKernelLaw_isProbabilityMeasure idealK initial inferInstance
      hidealMeas hidealProb i
  exact MeasureLeUpTo.bind_of_pointwise_tvLe
    (iteratedKernelLaw idealK initial i) (actualK i) (idealK i)
      (hactualMeas i) (hidealMeas i) (hactualProb i) (hidealProb i) (hpoint i)

/-- Deterministic postprocessing turns the history domination directly into
the same domination for a phase average or accumulated product. -/
theorem MeasureLeUpTo.map_iteratedKernelLaw_exactChance
    {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (actualK idealK : ℕ → S → Measure S)
    (initial : Measure S) {nu : ENNReal}
    (hactualMeas : ∀ i, Measurable (actualK i))
    (hactualProb : ∀ i state, IsProbabilityMeasure (actualK i state))
    (hstep : ∀ i,
      MeasureLeUpTo
        ((iteratedKernelLaw idealK initial i).bind (actualK i))
        (iteratedKernelLaw idealK initial (i + 1)) nu)
    (t : ℕ) (output : S → T) (houtput : Measurable output) :
    MeasureLeUpTo
      ((iteratedKernelLaw actualK initial t).map output)
      ((iteratedKernelLaw idealK initial t).map output)
      (t • nu) := by
  exact (MeasureLeUpTo.iteratedKernelLaw_exactChance actualK idealK
    initial hactualMeas hactualProb hstep t).map houtput

/-- Exact event-transfer form used by the final probability estimate. -/
theorem measure_map_iteratedKernelLaw_event_le_exactChance
    {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (actualK idealK : ℕ → S → Measure S)
    (initial : Measure S) {nu : ENNReal}
    (hactualMeas : ∀ i, Measurable (actualK i))
    (hactualProb : ∀ i state, IsProbabilityMeasure (actualK i state))
    (hstep : ∀ i,
      MeasureLeUpTo
        ((iteratedKernelLaw idealK initial i).bind (actualK i))
        (iteratedKernelLaw idealK initial (i + 1)) nu)
    (t : ℕ) (output : S → T) (houtput : Measurable output)
    (event : Set T) :
    ((iteratedKernelLaw actualK initial t).map output) event ≤
      ((iteratedKernelLaw idealK initial t).map output) event + t • nu := by
  exact (MeasureLeUpTo.map_iteratedKernelLaw_exactChance actualK idealK
    initial hactualMeas hactualProb hstep t output houtput).event_le event

/-- A law within `delta` of a law under which `X` and `Y` are exactly
independent makes them `3 * delta`-independent.  The three errors are the
joint rectangle and its two marginals; this is the factor three in CV18
Lemma 7.17(c). -/
theorem ApproxIndepFun.of_tvLe_of_exact
    {Omega S T : Type*} [MeasurableSpace Omega]
    [MeasurableSpace S] [MeasurableSpace T]
    (mu nu : Measure Omega) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {delta : ENNReal} (hdelta : delta ≠ ⊤)
    (X : Omega → S) (Y : Omega → T)
    (hX : Measurable X) (hY : Measurable Y)
    (htv : Arlib.TVLe mu nu delta)
    (hexact : ApproxIndepFun 0 X Y nu) :
    ApproxIndepFun (3 * delta.toReal) X Y mu := by
  intro A hA B hB
  let XA : Set Omega := X ⁻¹' A
  let YB : Set Omega := Y ⁻¹' B
  have hXA : MeasurableSet XA := hX hA
  have hYB : MeasurableSet YB := hY hB
  have hXY : MeasurableSet (XA ∩ YB) := hXA.inter hYB
  have hjoint := htv.abs_measureReal_sub_le hdelta hXY
  have hleft := htv.abs_measureReal_sub_le hdelta hXA
  have hright := htv.abs_measureReal_sub_le hdelta hYB
  have hexact0 := hexact A hA B hB
  have hexactEq : nu.real (XA ∩ YB) = nu.real XA * nu.real YB := by
    have hz : |nu.real (XA ∩ YB) - nu.real XA * nu.real YB| = 0 :=
      le_antisymm hexact0 (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp hz)
  have hmuLeft0 : 0 ≤ mu.real XA := measureReal_nonneg
  have hmuLeft1 : mu.real XA ≤ 1 := by
    simpa using probReal_le_one (μ := mu) XA
  have hnuRight0 : 0 ≤ nu.real YB := measureReal_nonneg
  have hnuRight1 : nu.real YB ≤ 1 := by
    simpa using probReal_le_one (μ := nu) YB
  have hproduct :
      |nu.real XA * nu.real YB - mu.real XA * mu.real YB| ≤
        2 * delta.toReal := by
    calc
      |nu.real XA * nu.real YB - mu.real XA * mu.real YB| =
          |(nu.real XA - mu.real XA) * nu.real YB +
            mu.real XA * (nu.real YB - mu.real YB)| := by ring_nf
      _ ≤ |nu.real XA - mu.real XA| * |nu.real YB| +
          |mu.real XA| * |nu.real YB - mu.real YB| := by
            simpa only [abs_mul] using abs_add_le
              ((nu.real XA - mu.real XA) * nu.real YB)
              (mu.real XA * (nu.real YB - mu.real YB))
      _ ≤ delta.toReal * 1 + 1 * delta.toReal := by
        gcongr
        · simpa [abs_sub_comm] using hleft
        · rw [abs_of_nonneg hnuRight0]
          exact hnuRight1
        · rw [abs_of_nonneg hmuLeft0]
          exact hmuLeft1
        · simpa [abs_sub_comm] using hright
      _ = 2 * delta.toReal := by ring
  change |mu.real (XA ∩ YB) - mu.real XA * mu.real YB| ≤
    3 * delta.toReal
  calc
    |mu.real (XA ∩ YB) - mu.real XA * mu.real YB| ≤
        |mu.real (XA ∩ YB) - nu.real (XA ∩ YB)| +
          |nu.real (XA ∩ YB) - mu.real XA * mu.real YB| := by
            simpa only using abs_sub_le _ _ _
    _ = |mu.real (XA ∩ YB) - nu.real (XA ∩ YB)| +
          |nu.real XA * nu.real YB - mu.real XA * mu.real YB| := by
            rw [hexactEq]
    _ ≤ delta.toReal + 2 * delta.toReal := add_le_add hjoint hproduct
    _ = 3 * delta.toReal := by ring

theorem ApproxIndepFun.of_measureLeUpTo_of_exact
    {Omega S T : Type*} [MeasurableSpace Omega]
    [MeasurableSpace S] [MeasurableSpace T]
    (mu nu : Measure Omega) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {delta : ENNReal} (hdelta : delta ≠ ⊤)
    (X : Omega → S) (Y : Omega → T)
    (hX : Measurable X) (hY : Measurable Y)
    (hdom : MeasureLeUpTo mu nu delta)
    (hexact : ApproxIndepFun 0 X Y nu) :
    ApproxIndepFun (3 * delta.toReal) X Y mu :=
  ApproxIndepFun.of_tvLe_of_exact mu nu hdelta X Y hX hY
    hdom.to_tvLe hexact

/-- Lemma 7.17(c) directly from the additive exact-chance history
replacement.  The variables may be the past accumulated product and the
complete averaged next phase, so this is the needed lift beyond a single
transition output. -/
theorem ApproxIndepFun.of_iteratedKernelLaw_exactChance
    {State S T : Type*} [MeasurableSpace State]
    [MeasurableSpace S] [MeasurableSpace T]
    (actualK idealK : ℕ → State → Measure State)
    (initial : Measure State) [IsProbabilityMeasure initial]
    {nu : ENNReal} (hnu : nu ≠ ⊤)
    (hactualMeas : ∀ i, Measurable (actualK i))
    (hactualProb : ∀ i state, IsProbabilityMeasure (actualK i state))
    (hidealMeas : ∀ i, Measurable (idealK i))
    (hidealProb : ∀ i state, IsProbabilityMeasure (idealK i state))
    (hstep : ∀ i,
      MeasureLeUpTo
        ((iteratedKernelLaw idealK initial i).bind (actualK i))
        (iteratedKernelLaw idealK initial (i + 1)) nu)
    (t : ℕ) (X : State → S) (Y : State → T)
    (hX : Measurable X) (hY : Measurable Y)
    (hexact : ApproxIndepFun 0 X Y
      (iteratedKernelLaw idealK initial t)) :
    ApproxIndepFun (3 * (t • nu).toReal) X Y
      (iteratedKernelLaw actualK initial t) := by
  let _ : IsProbabilityMeasure (iteratedKernelLaw actualK initial t) :=
    iteratedKernelLaw_isProbabilityMeasure actualK initial inferInstance
      hactualMeas hactualProb t
  let _ : IsProbabilityMeasure (iteratedKernelLaw idealK initial t) :=
    iteratedKernelLaw_isProbabilityMeasure idealK initial inferInstance
      hidealMeas hidealProb t
  apply ApproxIndepFun.of_measureLeUpTo_of_exact
    (iteratedKernelLaw actualK initial t)
    (iteratedKernelLaw idealK initial t)
  · rw [nsmul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top t) hnu
  · exact hX
  · exact hY
  · exact MeasureLeUpTo.iteratedKernelLaw_exactChance actualK idealK
      initial hactualMeas hactualProb hstep t
  · exact hexact

/-- The Figure-One choice of per-sample error makes the factor-three
exact-chance loss over `maxSampleCount * phaseCount` samples exactly the
dependent-product independence budget. -/
theorem figureOne_exactChance_budget (q : VolumeParams) :
    3 * (((figureOneDependentMaxSampleCount q *
      figureOneDependentPhaseCount q) •
        ENNReal.ofReal (figureOnePerSampleMixingError q)).toReal) =
      figureOneDependentEpsilon q := by
  rw [nsmul_eq_mul, ENNReal.toReal_mul]
  simp only [ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (figureOnePerSampleMixingError_pos q).le]
  rw [Nat.cast_mul]
  simpa only [mul_assoc] using figureOne_lemma717c_budget q

/-- Fully budgeted exact-chance route to the coefficient used in Lemma
7.17(c).  This accepts a complete averaged phase/history observable, rather
than only the endpoint of one transition. -/
theorem ApproxIndepFun.of_figureOne_exactChance
    {State S T : Type*} [MeasurableSpace State]
    [MeasurableSpace S] [MeasurableSpace T]
    (q : VolumeParams)
    (actualK idealK : ℕ → State → Measure State)
    (initial : Measure State) [IsProbabilityMeasure initial]
    (hactualMeas : ∀ i, Measurable (actualK i))
    (hactualProb : ∀ i state, IsProbabilityMeasure (actualK i state))
    (hidealMeas : ∀ i, Measurable (idealK i))
    (hidealProb : ∀ i state, IsProbabilityMeasure (idealK i state))
    (hstep : ∀ i,
      MeasureLeUpTo
        ((iteratedKernelLaw idealK initial i).bind (actualK i))
        (iteratedKernelLaw idealK initial (i + 1))
        (ENNReal.ofReal (figureOnePerSampleMixingError q)))
    (X : State → S) (Y : State → T)
    (hX : Measurable X) (hY : Measurable Y)
    (hexact : ApproxIndepFun 0 X Y
      (iteratedKernelLaw idealK initial
        (figureOneDependentMaxSampleCount q *
          figureOneDependentPhaseCount q))) :
    ApproxIndepFun (figureOneDependentEpsilon q) X Y
      (iteratedKernelLaw actualK initial
        (figureOneDependentMaxSampleCount q *
          figureOneDependentPhaseCount q)) := by
  have h := ApproxIndepFun.of_iteratedKernelLaw_exactChance
    actualK idealK initial ENNReal.ofReal_ne_top hactualMeas hactualProb
      hidealMeas hidealProb hstep
      (figureOneDependentMaxSampleCount q *
        figureOneDependentPhaseCount q) X Y hX hY hexact
  rw [figureOne_exactChance_budget q] at h
  exact h

#print axioms MeasureLeUpTo.iteratedKernelLaw_exactChance
#print axioms measure_map_iteratedKernelLaw_event_le_exactChance
#print axioms ApproxIndepFun.of_iteratedKernelLaw_exactChance
#print axioms ApproxIndepFun.of_figureOne_exactChance

end ArlibCommunity.Algorithms.CV18
