/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedConcreteTransition
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofExactChance

/-!
# Componentwise error allocation for finite balanced transitions

The error of one accepted sample has three distinct sources: mixing in each
proper block, exhausting the geometric acceptance retries, and replacing the
stationary KLS accepted target by the restricted Gaussian target.  This file
keeps those sources separate and proves the exact envelope consumed by the
chronological `exact-chance` construction.

Proposal-cap exhaustion is intentionally absent.  It belongs to the outer
whole-run query cutoff, not to every sample's TV budget.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem MeasureLeUpTo.mono_error
    {A : Type*} [MeasurableSpace A]
    {mu nu : Measure A} {delta eta : ENNReal}
    (h : MeasureLeUpTo mu nu delta) (hde : delta ≤ eta) :
    MeasureLeUpTo mu nu eta := by
  obtain ⟨error, hle, hmass⟩ := h
  exact ⟨error, hle, hmass.trans hde⟩

/-- Total per-accepted-sample budget already selected by the Figure-One
dependent-product schedule. -/
noncomputable def figureOneCorrectedTransitionBudget
    (q : VolumeParams) : ENNReal :=
  ENNReal.ofReal (figureOnePerSampleMixingError q)

/-- One quarter is reserved for exhausting the geometric retry loop. -/
noncomputable def figureOneCorrectedRetryTailBudget
    (q : VolumeParams) : ENNReal :=
  figureOneCorrectedTransitionBudget q / 4

/-- One quarter is reserved for the stationary accepted-target correction. -/
noncomputable def figureOneCorrectedTargetBudget
    (q : VolumeParams) : ENNReal :=
  figureOneCorrectedTransitionBudget q / 4

/-- The remaining half-budget is spread across the first block and every
possible retry block.  A factor `4`, rather than `2`, leaves one additional
quarter of slack in the component sum. -/
noncomputable def figureOneCorrectedBlockMixingError
    (q : VolumeParams) (attempts : ℕ) : ℝ :=
  figureOnePerSampleMixingError q / (4 * (attempts + 1 : ℝ))

/-- The block-mixing component as a measure-error budget. -/
noncomputable def figureOneCorrectedBlockBudget
    (q : VolumeParams) (attempts : ℕ) : ENNReal :=
  ENNReal.ofReal (figureOneCorrectedBlockMixingError q attempts)

theorem figureOneCorrectedBlockMixingError_pos
    (q : VolumeParams) (attempts : ℕ) :
    0 < figureOneCorrectedBlockMixingError q attempts := by
  unfold figureOneCorrectedBlockMixingError
  positivity [figureOnePerSampleMixingError_pos q]

/-- Retuning the internal components does not change the global
`exact-chance` accounting: after all phase samples and its factor-three
transfer loss, the total is exactly the Lemma 7.15 dependence budget. -/
theorem figureOneCorrected_exactChance_budget (q : VolumeParams) :
    3 * (((figureOneDependentMaxSampleCount q *
      figureOneDependentPhaseCount q) •
        figureOneCorrectedTransitionBudget q).toReal) =
      figureOneDependentEpsilon q := by
  simpa [figureOneCorrectedTransitionBudget] using
    figureOne_exactChance_budget q

/-- The concrete quarter-budget split leaves one quarter of slack.  In
particular, after the first block and all possible retry blocks, the retry
tail and target correction still fit the original per-sample budget. -/
theorem figureOneCorrected_components_le
    (q : VolumeParams) (attempts : ℕ) :
    (attempts + 1) • figureOneCorrectedBlockBudget q attempts +
        figureOneCorrectedRetryTailBudget q +
      figureOneCorrectedTargetBudget q ≤
        figureOneCorrectedTransitionBudget q := by
  have hblock : figureOneCorrectedBlockBudget q attempts ≠ ∞ := by
    simp [figureOneCorrectedBlockBudget]
  have htotal : figureOneCorrectedTransitionBudget q ≠ ∞ := by
    simp [figureOneCorrectedTransitionBudget]
  have hretry : figureOneCorrectedRetryTailBudget q ≠ ∞ := by
    exact ENNReal.div_ne_top htotal (by norm_num)
  have htarget : figureOneCorrectedTargetBudget q ≠ ∞ := by
    exact ENNReal.div_ne_top htotal (by norm_num)
  have hblocks :
      (attempts + 1) • figureOneCorrectedBlockBudget q attempts ≠ ∞ := by
    rw [nsmul_eq_mul]
    exact ENNReal.mul_ne_top (by simp) hblock
  have hblocksRetry :
      (attempts + 1) • figureOneCorrectedBlockBudget q attempts +
          figureOneCorrectedRetryTailBudget q ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨hblocks, hretry⟩
  apply (ENNReal.toReal_le_toReal
    (ENNReal.add_ne_top.2 ⟨hblocksRetry, htarget⟩) htotal).mp
  rw [ENNReal.toReal_add hblocksRetry htarget]
  rw [ENNReal.toReal_add hblocks hretry]
  rw [ENNReal.toReal_nsmul]
  simp only [figureOneCorrectedBlockBudget,
    figureOneCorrectedRetryTailBudget,
    figureOneCorrectedTargetBudget,
    figureOneCorrectedTransitionBudget, ENNReal.toReal_div,
    ENNReal.toReal_ofNat, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  rw [ENNReal.toReal_ofReal
    (figureOneCorrectedBlockMixingError_pos q attempts).le]
  rw [ENNReal.toReal_ofReal (figureOnePerSampleMixingError_pos q).le]
  unfold figureOneCorrectedBlockMixingError
  have hden : (0 : ℝ) < attempts + 1 := by positivity
  field_simp
  nlinarith [figureOnePerSampleMixingError_pos q]

/-- The first block after a retained accepted state must allow the proved
`16`-warm accepted branch, followed by adjacent-phase warmness. -/
noncomputable def figureOneCorrectedFirstWalkRequirement
    (q : VolumeParams) (sigma2 : ℝ) (attempts : ℕ) : ℝ :=
  4 * ((Real.log (16 * speedyAdjacentWarmConstant q) +
      2 * Real.log (1 / figureOneCorrectedBlockMixingError q attempts)) /
    (figureOneProposalRadius q sigma2 * Real.log 2 /
      (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1

noncomputable def figureOneCorrectedRetryWalkRequirement
    (q : VolumeParams) (sigma2 : ℝ) (attempts : ℕ) : ℝ :=
  4 * ((Real.log 2 +
      2 * Real.log (1 / figureOneCorrectedBlockMixingError q attempts)) /
    (figureOneProposalRadius q sigma2 * Real.log 2 /
      (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1

/-- Stride strengthened to cover both the accepted-state first block and
stationary rejected retries at their smaller component mixing tolerance. -/
noncomputable def figureOneCorrectedProperStride
    (q : VolumeParams) (sigma2 : ℝ) (attempts : ℕ) : ℕ :=
  Nat.ceil (max 1 (max
    (figureOneCorrectedFirstWalkRequirement q sigma2 attempts)
    (figureOneCorrectedRetryWalkRequirement q sigma2 attempts)))

theorem figureOneCorrectedFirstWalkRequirement_le_stride
    (q : VolumeParams) (sigma2 : ℝ) (attempts : ℕ) :
    figureOneCorrectedFirstWalkRequirement q sigma2 attempts ≤
      (figureOneCorrectedProperStride q sigma2 attempts : ℝ) := by
  apply le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
  exact Nat.le_ceil _

theorem figureOneCorrectedRetryWalkRequirement_le_stride
    (q : VolumeParams) (sigma2 : ℝ) (attempts : ℕ) :
    figureOneCorrectedRetryWalkRequirement q sigma2 attempts ≤
      (figureOneCorrectedProperStride q sigma2 attempts : ℝ) := by
  apply le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
  exact Nat.le_ceil _

/-- Multiplication by the rejection probability turns the recursive retry
error into at most `attempts` further block errors plus the probability of
exhausting all remaining attempts. -/
theorem reject_mul_balancedRetryError_le
    {blockError rejectMass : ENNReal} (hreject : rejectMass ≤ 1) :
    ∀ attempts,
      rejectMass * balancedRetryError blockError rejectMass attempts ≤
        attempts • blockError + rejectMass ^ (attempts + 1) := by
  intro attempts
  have hrec := balancedRetryError_le_nsmul_add_pow
    (delta := blockError) hreject attempts
  have hscaled : rejectMass * (attempts • blockError) ≤
      attempts • blockError := by
    calc
      rejectMass * (attempts • blockError) ≤
          1 * (attempts • blockError) := mul_le_mul' hreject le_rfl
      _ = attempts • blockError := one_mul _
  calc
    rejectMass * balancedRetryError blockError rejectMass attempts ≤
        rejectMass * (attempts • blockError + rejectMass ^ attempts) :=
      mul_le_mul' le_rfl hrec
    _ = rejectMass * (attempts • blockError) +
        rejectMass ^ (attempts + 1) := by rw [mul_add, pow_succ']
    _ ≤ attempts • blockError + rejectMass ^ (attempts + 1) :=
      add_le_add hscaled le_rfl

/-- A corrected per-transition allocation.  `blockBudget` is paid once for
the first block and at most once for every rejected retry; `retryTailBudget`
covers exhausting all attempts; `targetBudget` covers the KLS target change.
The final field is precisely the compatibility condition with the chosen
per-sample exact-chance budget. -/
structure BalancedTransitionErrorAllocation
    (q : VolumeParams) (rejectMass : ENNReal) (attempts : ℕ)
    (targetError : ENNReal := balancedStationaryTargetError q) where
  totalBudget : ENNReal
  blockBudget : ENNReal
  retryTailBudget : ENNReal
  targetBudget : ENNReal
  reject_le_one : rejectMass ≤ 1
  retryTail_le : rejectMass ^ (attempts + 1) ≤ retryTailBudget
  targetError_le : targetError ≤ targetBudget
  components_le :
    (attempts + 1) • blockBudget + retryTailBudget + targetBudget ≤
      totalBudget

/-- The canonical Figure-One allocation.  Only the two genuine numerical
compatibility facts remain as inputs: enough retries to make the geometric
tail small, and a sufficiently accurate KLS accepted-target replacement. -/
noncomputable def figureOneCorrectedErrorAllocation
    (q : VolumeParams) (rejectMass : ENNReal) (attempts : ℕ)
    (hreject : rejectMass ≤ 1)
    (hretry : rejectMass ^ (attempts + 1) ≤
      figureOneCorrectedRetryTailBudget q)
    (htarget : balancedStationaryTargetError q ≤
      figureOneCorrectedTargetBudget q) :
    BalancedTransitionErrorAllocation (q := q) rejectMass attempts where
  totalBudget := figureOneCorrectedTransitionBudget q
  blockBudget := figureOneCorrectedBlockBudget q attempts
  retryTailBudget := figureOneCorrectedRetryTailBudget q
  targetBudget := figureOneCorrectedTargetBudget q
  reject_le_one := hreject
  retryTail_le := hretry
  targetError_le := htarget
  components_le := figureOneCorrected_components_le q attempts

theorem balancedTransitionError_le_allocation
    {rejectMass : ENNReal} {attempts : ℕ}
    {targetError : ENNReal}
    (allocation : BalancedTransitionErrorAllocation
      (q := q) rejectMass attempts targetError) :
    allocation.blockBudget + rejectMass *
        balancedRetryError allocation.blockBudget rejectMass attempts +
      targetError ≤ allocation.totalBudget := by
  have hretry := reject_mul_balancedRetryError_le
    (blockError := allocation.blockBudget)
    allocation.reject_le_one attempts
  calc
    allocation.blockBudget + rejectMass *
          balancedRetryError allocation.blockBudget rejectMass attempts +
        targetError ≤
      allocation.blockBudget +
          (attempts • allocation.blockBudget +
            rejectMass ^ (attempts + 1)) +
        targetError := by gcongr
    _ = (attempts + 1) • allocation.blockBudget +
          rejectMass ^ (attempts + 1) +
        targetError := by
      rw [add_nsmul]
      simp only [one_nsmul]
      ac_rfl
    _ ≤ (attempts + 1) • allocation.blockBudget +
          allocation.retryTailBudget + allocation.targetBudget := by
      exact add_le_add
        (add_le_add le_rfl allocation.retryTail_le)
        allocation.targetError_le
    _ ≤ allocation.totalBudget := allocation.components_le

/-- The concrete one-transition theorem with a sound component allocation.
This is the corrected replacement for assigning the full per-sample error to
each proper block before accounting for retries and target approximation. -/
theorem bind_balancedTransition_tvLe_truncatedGaussian_of_allocation
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride attempts : ℕ)
    (rho : Measure (AmbientSpace q.n)) [IsProbabilityMeasure rho]
    (allocation :
      let pi := Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2
      BalancedTransitionErrorAllocation (q := q)
        (balancedRejectedStateMeasure q I sigma2 pi Set.univ) attempts)
    (hfirstBlock :
      let pi := Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2
      MeasureLeUpTo
        ((rho.bind
          (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap
            properStride)).map optionSnd)
        (pi.map some) allocation.blockBudget)
    (hretryBlock :
      let pi := Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2
      let rejected := balancedRejectedStateMeasure q I sigma2 pi
      let rejectedProb := Arlib.condOn rejected Set.univ
      MeasureLeUpTo
        ((rejectedProb.bind
          (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap
            properStride)).map optionSnd)
        (pi.map some) allocation.blockBudget) :
    Arlib.TVLe
      (rho.bind
        (balancedAccuracyTransitionLawAux q I sigma2 proposalCap
          properStride (attempts + 1)))
      ((truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)).map some)
      allocation.totalBudget := by
  let pi := Arlib.MarkovChains.ellGaussianProb
    (accuracyPhaseTruncatedBody q I sigma2)
    (figureOneProposalRadius q sigma2) sigma2
  let rejectMass := balancedRejectedStateMeasure q I sigma2 pi Set.univ
  have hraw := bind_balancedTransition_tvLe_truncatedGaussian
    q I hsigma2 proposalCap properStride attempts rho hfirstBlock hretryBlock
  apply hraw.mono
  exact balancedTransitionError_le_allocation allocation

/-- A complete `k`-sample phase replacement: once every ideal-prefix step is
covered by the corrected total budget, any measurable averaged estimator has
the same additive `k * totalBudget` event-transfer bound. -/
theorem MeasureLeUpTo.map_iteratedKernelLaw_of_corrected_phase_budget
    {State Output : Type*} [MeasurableSpace State] [MeasurableSpace Output]
    (actualK idealK : ℕ → State → Measure State)
    (initial : Measure State)
    (hactualMeas : ∀ i, Measurable (actualK i))
    (hactualProb : ∀ i state, IsProbabilityMeasure (actualK i state))
    {totalBudget nu : ENNReal}
    (hstep : ∀ i, MeasureLeUpTo
      ((iteratedKernelLaw idealK initial i).bind (actualK i))
      (iteratedKernelLaw idealK initial (i + 1)) totalBudget)
    (hbudget : totalBudget ≤ nu)
    (k : ℕ) (average : State → Output) (haverage : Measurable average) :
    MeasureLeUpTo
      ((iteratedKernelLaw actualK initial k).map average)
      ((iteratedKernelLaw idealK initial k).map average)
      (k • nu) := by
  have hraw := MeasureLeUpTo.map_iteratedKernelLaw_exactChance
    actualK idealK initial hactualMeas hactualProb hstep k average haverage
  exact hraw.mono_error (nsmul_le_nsmul_right hbudget k)

/-- Exact Figure-One budget form of the complete averaged phase theorem. -/
theorem MeasureLeUpTo.map_iteratedKernelLaw_of_figureOne_phase_budget
    {State Output : Type*} [MeasurableSpace State] [MeasurableSpace Output]
    (q : VolumeParams)
    (actualK idealK : ℕ → State → Measure State)
    (initial : Measure State)
    (hactualMeas : ∀ i, Measurable (actualK i))
    (hactualProb : ∀ i state, IsProbabilityMeasure (actualK i state))
    {totalBudget : ENNReal}
    (hstep : ∀ i, MeasureLeUpTo
      ((iteratedKernelLaw idealK initial i).bind (actualK i))
      (iteratedKernelLaw idealK initial (i + 1)) totalBudget)
    (hbudget : totalBudget ≤
      ENNReal.ofReal (figureOnePerSampleMixingError q))
    (k : ℕ) (average : State → Output) (haverage : Measurable average) :
    MeasureLeUpTo
      ((iteratedKernelLaw actualK initial k).map average)
      ((iteratedKernelLaw idealK initial k).map average)
      (k • ENNReal.ofReal (figureOnePerSampleMixingError q)) :=
  MeasureLeUpTo.map_iteratedKernelLaw_of_corrected_phase_budget
    actualK idealK initial hactualMeas hactualProb hstep hbudget
      k average haverage

#print axioms reject_mul_balancedRetryError_le
#print axioms balancedTransitionError_le_allocation
#print axioms bind_balancedTransition_tvLe_truncatedGaussian_of_allocation
#print axioms MeasureLeUpTo.map_iteratedKernelLaw_of_figureOne_phase_budget

end ArlibCommunity.Algorithms.CV18
