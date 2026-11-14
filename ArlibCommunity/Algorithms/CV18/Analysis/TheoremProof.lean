/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAnalyticCore
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAmplification

/-!
# Proof assembly for the CV18 volume theorem

As in `Algorithms/HitAndRun/Analysis/TheoremProof.lean`, this module is the
small model-facing assembly of the problem-specific analysis.  Every input to
Theorem 1.1 except the executable post-initial walk bound is discharged here.
-/

namespace ArlibCommunity.Algorithms.CV18

/-- Theorem 1.1 for the concrete Figure-1 implementation, conditional only on
the post-initial dependent-walk estimate.  The constant is uniform over all
parameters, inputs, and exact membership oracles. -/
theorem volumeTheorem_of_postInitialMixing :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : VolumeParams) (I : VolumeInput q.n)
        (oracle : MembershipOracle I),
        WellRounded q I →
        FigureOnePostInitialMixingBound q I oracle →
          1 - q.p ≤
              outcomeProbability
                (volumeAlgorithmLaw
                  (volumeCoolingAlgorithm figureOnePrimitives
                    explicitVolumeCoolingSchedule) q I oracle)
                (accurateOutcome q I) ∧
            ∃ calls,
              (volumeCoolingAlgorithm figureOnePrimitives
                explicitVolumeCoolingSchedule q).QueryBound calls ∧
              calls ≤ Nat.ceil (C * volumeComplexityRate q) := by
  obtain ⟨C₀, hC₀, hbaseCost⟩ := figureOne_base_query_cost
  obtain ⟨C, hC, hamp⟩ := volume_proof_amplification C₀ hC₀
  refine ⟨C, hC, ?_⟩
  intro q I oracle hrounded hmixing
  apply hamp figureOnePrimitives explicitVolumeCoolingSchedule q I oracle
  · exact figureOne_base_accuracy_of_mixing q I oracle hrounded hmixing
  · exact figureOneBaseVolumeCooling_stronglyMeasurable
      explicitVolumeCoolingSchedule q I oracle
  · refine ⟨_, figureOneBaseVolumeCooling_queryBound
        explicitVolumeCoolingSchedule q, ?_⟩
    exact hbaseCost q

#print axioms volumeTheorem_of_postInitialMixing

end ArlibCommunity.Algorithms.CV18
