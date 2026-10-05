/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofPrimitives
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofSchedule
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofCost
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofProductAccuracy
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofInitialCoupling
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofIdealProduct
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofSharpMoments
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofMeasureApproximation
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofRadialTruncation

open MeasureTheory

namespace ArlibCommunity.Algorithms.CV18

/-!
# Analytic core of the CV18 base run

All operational, measure-theoretic, warm-start, terminal-moment, and structural
query-count obligations have been discharged before this point.  The radial
tail and sharp phase-amortized ratio moments are also discharged.  The public
theorem in this module makes the remaining dependent ball-walk estimate
explicit as one hypothesis.
-/

/-- A strong, reusable sufficient condition for the post-initial sampling
step: domination of the entire dependent output law by the independent output
law plus an error measure of mass at most `1/16`. -/
def FigureOnePostInitialLawCoupling
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) : Prop :=
  MeasureLeUpTo
    ((truncatedGaussianProbability q I (initialVariance q)
        (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind
      (figureOneContinuationLaw explicitVolumeCoolingSchedule q I oracle))
    (figureOneIdealEstimateLaw q I)
    (ENNReal.ofReal (1 / 16 : ℝ))

/-- The exact remaining sampling statement used by the accuracy theorem.  It
allows the paper's covariance/truncation analysis and does not unnecessarily
require simultaneous coupling of every sample in a long cooling schedule. -/
def FigureOnePostInitialMixingBound
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) : Prop :=
  ((truncatedGaussianProbability q I (initialVariance q)
      (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind
    (figureOneContinuationLaw explicitVolumeCoolingSchedule q I oracle))
      (accurateOutcome q I)ᶜ ≤
    (figureOneIdealExperimentLaw q I)
      {samples | initialGaussianIntegral q * figureOneIdealProduct q samples ∉
        accurateOutcome q I} + ENNReal.ofReal (1 / 16 : ℝ)

theorem figureOnePostInitialMixingBound_of_lawCoupling
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I)
    (hmixing : FigureOnePostInitialLawCoupling q I oracle) :
    FigureOnePostInitialMixingBound q I oracle := by
  have h := MeasureLeUpTo.event_le hmixing (accurateOutcome q I)ᶜ
  rw [figureOneIdealEstimateLaw_apply q I
    (accurateOutcome_measurable q I).compl] at h
  exact h

theorem figureOne_base_accuracy_of_analytic_inputs
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I)
    (hsharp : FigureOneSharpAcceleratedMoments q I)
    (htrunc : FigureOneRadialTruncationBound q I)
    (hmixing : FigureOnePostInitialMixingBound q I oracle) :
    3 / 4 ≤
      outcomeProbability
        (volumeAlgorithmLaw
          (fun q => baseVolumeCooling figureOnePrimitives
            explicitVolumeCoolingSchedule q) q I oracle)
        (accurateOutcome q I) := by
  let μ : Measure ℝ :=
    volumeAlgorithmLaw
      (fun q => baseVolumeCooling figureOnePrimitives
        explicitVolumeCoolingSchedule q) q I oracle
  have hstrong := figureOneBaseVolumeCooling_stronglyMeasurable
    explicitVolumeCoolingSchedule q I oracle
  let _ : IsProbabilityMeasure μ := by
    unfold μ volumeAlgorithmLaw
    exact MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle.query _
      hstrong.estimateMeasurable
  apply outcomeProbability_ge_three_quarters_of_failure_le μ q I
  change
    (baseVolumeCooling figureOnePrimitives explicitVolumeCoolingSchedule q).runEstimate
        oracle.query (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (1 / 4 : ℝ)
  calc
    _ ≤ ((truncatedGaussianProbability q I (initialVariance q)
          (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind
        (figureOneContinuationLaw explicitVolumeCoolingSchedule q I oracle))
          (accurateOutcome q I)ᶜ + ENNReal.ofReal (q.eps / 64) :=
      figureOneBaseVolumeCooling_event_le_idealStart_add
        explicitVolumeCoolingSchedule q I oracle (accurateOutcome q I)ᶜ
          (accurateOutcome_measurable q I).compl
    _ ≤ ((figureOneIdealExperimentLaw q I)
          {samples | initialGaussianIntegral q * figureOneIdealProduct q samples ∉
          accurateOutcome q I} + ENNReal.ofReal (1 / 16 : ℝ)) +
          ENNReal.ofReal (q.eps / 64) := by
      gcongr
      exact hmixing
    _ ≤ (ENNReal.ofReal (1 / 8 : ℝ) + ENNReal.ofReal (1 / 16 : ℝ)) +
          ENNReal.ofReal (q.eps / 64) := by
      gcongr
      exact figureOneIdealScaledProduct_realVolume_failure_le_one_div_8
        q I hsharp htrunc
    _ ≤ (ENNReal.ofReal (1 / 8 : ℝ) + ENNReal.ofReal (1 / 16 : ℝ)) +
          ENNReal.ofReal (1 / 64 : ℝ) := by
      gcongr
      exact q.heps.2.le
    _ ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 8)
          (by norm_num : (0 : ℝ) ≤ 1 / 16),
        ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 8 + 1 / 16)
          (by norm_num : (0 : ℝ) ≤ 1 / 64)]
      apply ENNReal.ofReal_le_ofReal
      norm_num

/-- The accelerated localization/moment input is discharged unconditionally;
this intermediate form keeps radial truncation explicit for reuse. -/
theorem figureOne_base_accuracy_of_truncation_and_mixing
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I)
    (htrunc : FigureOneRadialTruncationBound q I)
    (hmixing : FigureOnePostInitialMixingBound q I oracle) :
    3 / 4 ≤
      outcomeProbability
        (volumeAlgorithmLaw
          (fun q => baseVolumeCooling figureOnePrimitives
            explicitVolumeCoolingSchedule q) q I oracle)
        (accurateOutcome q I) :=
  figureOne_base_accuracy_of_analytic_inputs q I oracle
    (figureOneSharpAcceleratedMoments q I) htrunc hmixing

/-- The complete Figure-1 base-run accuracy theorem, conditional only on the
post-initial walk bound.  Radial truncation follows from the input's
well-roundedness promise. -/
theorem figureOne_base_accuracy_of_mixing
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I)
    (hrounded : WellRounded q I)
    (hmixing : FigureOnePostInitialMixingBound q I oracle) :
    3 / 4 ≤
      outcomeProbability
        (volumeAlgorithmLaw
          (fun q => baseVolumeCooling figureOnePrimitives
            explicitVolumeCoolingSchedule q) q I oracle)
        (accurateOutcome q I) :=
  figureOne_base_accuracy_of_truncation_and_mixing q I oracle
    (figureOneRadialTruncationBound q I hrounded) hmixing

/-!
The unconditional CV18 capstone is intentionally not asserted here.  The
radial-tail and accelerated-localization inputs are discharged.  Closing the
capstone now requires only `FigureOnePostInitialMixingBound` for the executable
walk.
-/

end ArlibCommunity.Algorithms.CV18
