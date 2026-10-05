/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofCappedDominance
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledRetryKernel

/-! # Cap-free domination at the scheduled phase geometry

These are direct scheduled instances of the generic killed-submeasure theorem.
In particular, exhausting the finite local proposal cap removes mass and never
has to be charged in the warmness invariant used for expected-cost analysis.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open Arlib.MarkovChains

/-- Successful scheduled block endpoints are dominated by one stride of the
uncapped lazy speedy walk, independently of the local proposal cap. -/
theorem successfulEndpointLaw_bind_scheduledBalancedAccuracyRetryBlockKernel_le
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (proposalCap properStride : ℕ)
    (mu : Measure (AmbientSpace q.n)) :
    successfulEndpointLaw
        (mu.bind (scheduledBalancedAccuracyRetryBlockKernel q I sigma2
          proposalCap properStride)) ≤
      iterate
        ((lazy (speedyMetropolisGaussian
          (figureOneScheduledPhaseBody q I sigma2)
          (figureOneScheduledProposalRadius q sigma2) sigma2)) ^ properStride)
        mu 1 := by
  change successfulEndpointLaw
      (mu.bind fun current => cappedProperCollectLaw
        (lazyProperProposalGaussianAux
          (figureOneScheduledPhaseBody q I sigma2)
          (figureOneScheduledPhaseBody_measurable q I sigma2)
          (figureOneScheduledProposalRadius q sigma2) sigma2)
        (fun _ => 0) proposalCap properStride 1 current) ≤ _
  exact
    successfulEndpointLaw_bind_cappedProperCollectLaw_le_iterate
      (figureOneScheduledPhaseBody q I sigma2)
      (figureOneScheduledPhaseBody_measurable q I sigma2)
      (figureOneScheduledProposalRadius q sigma2) sigma2
      measurable_const proposalCap properStride 1 mu

/-- A warm input law therefore gives an equally warm successful endpoint
sublaw for the finite scheduled block. -/
theorem successfulEndpointLaw_bind_scheduledBalancedAccuracyRetryBlockKernel_isWarm
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (proposalCap properStride : ℕ)
    {mu pi : Measure (AmbientSpace q.n)} {M : ENNReal}
    (hwarm : Arlib.IsWarm M mu pi)
    (hinv : Kernel.Invariant
      ((lazy (speedyMetropolisGaussian
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2)) ^ properStride) pi) :
    Arlib.IsWarm M
      (successfulEndpointLaw
        (mu.bind (scheduledBalancedAccuracyRetryBlockKernel q I sigma2
          proposalCap properStride))) pi := by
  change Arlib.IsWarm M
      (successfulEndpointLaw
        (mu.bind fun current => cappedProperCollectLaw
          (lazyProperProposalGaussianAux
            (figureOneScheduledPhaseBody q I sigma2)
            (figureOneScheduledPhaseBody_measurable q I sigma2)
            (figureOneScheduledProposalRadius q sigma2) sigma2)
          (fun _ => 0) proposalCap properStride 1 current)) pi
  exact
    successfulEndpointLaw_bind_cappedProperCollectLaw_isWarm
      (figureOneScheduledPhaseBody q I sigma2)
      (figureOneScheduledPhaseBody_measurable q I sigma2)
      (figureOneScheduledProposalRadius q sigma2) sigma2
      measurable_const proposalCap properStride 1 hwarm hinv

#print axioms
  successfulEndpointLaw_bind_scheduledBalancedAccuracyRetryBlockKernel_le
#print axioms
  successfulEndpointLaw_bind_scheduledBalancedAccuracyRetryBlockKernel_isWarm

end ArlibCommunity.Algorithms.CV18
