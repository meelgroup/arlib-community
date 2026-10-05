/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofRatios

namespace ArlibCommunity.Algorithms.CV18

theorem terminalVariance_pos' (q : VolumeParams) : 0 < terminalVariance q := by
  unfold terminalVariance
  exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem terminalVariance_one_le (q : VolumeParams) : 1 ≤ terminalVariance q := by
  unfold terminalVariance
  exact le_max_left _ _

theorem truncatedBody_measurable (q : VolumeParams) (I : VolumeInput q.n) :
    MeasurableSet (truncatedBody q I) :=
  I.body.isClosed.measurableSet.inter Metric.isClosed_closedBall.measurableSet

theorem unitBall_subset_truncatedBody (q : VolumeParams) (I : VolumeInput q.n) :
    unitBall q.n ⊆ truncatedBody q I := by
  intro x hx
  refine ⟨I.unitBall_subset hx, ?_⟩
  have hxone : dist x 0 ≤ 1 := by
    simpa [unitBall, Metric.mem_closedBall] using hx
  have hsqrt : 1 ≤ Real.sqrt (terminalVariance q) :=
    Real.one_le_sqrt.mpr (terminalVariance_one_le q)
  exact Metric.mem_closedBall.mpr (hxone.trans hsqrt)

/-- The paper's high-probability radius truncation is itself an admissible
convex-volume input and still contains the known unit ball. -/
noncomputable def truncatedVolumeInput (q : VolumeParams) (I : VolumeInput q.n) :
    VolumeInput q.n where
  body :=
    { carrier := truncatedBody q I
      convex' := I.body.convex.inter (convex_closedBall (0 : AmbientSpace q.n)
        (Real.sqrt (terminalVariance q)))
      isCompact' := I.body.isCompact.inter (isCompact_closedBall _ _)
      nonempty' := ⟨0, unitBall_subset_truncatedBody q I (by simp [unitBall])⟩ }
  unitBall_subset := unitBall_subset_truncatedBody q I

@[simp] theorem truncatedVolumeInput_coe (q : VolumeParams) (I : VolumeInput q.n) :
    ((truncatedVolumeInput q I).body : Set (AmbientSpace q.n)) = truncatedBody q I := rfl

/-- The already-proved all-epsilon starting-tail estimate applies unchanged to
the truncated body used by the operational volume algorithm. -/
theorem volume_proof_truncated_initial_tail
    (q : VolumeParams) (I : VolumeInput q.n) :
    RelativeApprox (q.eps / 32)
      (gaussianIntegral (truncatedBody q I) (initialVariance q))
      (initialGaussianIntegral q) := by
  simpa using volume_proof_initial_tail q (truncatedVolumeInput q I)

theorem norm_sq_le_terminalVariance_of_mem_truncatedBody
    (q : VolumeParams) (I : VolumeInput q.n) {x : AmbientSpace q.n}
    (hx : x ∈ truncatedBody q I) :
    ‖x‖ ^ 2 ≤ terminalVariance q := by
  have hnorm : ‖x‖ ≤ Real.sqrt (terminalVariance q) := by
    have := hx.2
    simpa [Metric.mem_closedBall, dist_zero_right] using this
  nlinarith [norm_nonneg x, Real.sqrt_nonneg (terminalVariance q),
    Real.sq_sqrt (terminalVariance_one_le q |>.trans' zero_le_one)]

/-- At terminal variance the Gaussian-to-uniform importance weight on the
truncated body lies in the constant interval `[1, exp(1/2)]`. -/
theorem uniformRatio_terminal_bounds
    (q : VolumeParams) (I : VolumeInput q.n) {x : AmbientSpace q.n}
    (hx : x ∈ truncatedBody q I) :
    1 ≤ uniformRatioSample (truncatedBody q I) (terminalVariance q) x ∧
      uniformRatioSample (truncatedBody q I) (terminalVariance q) x ≤
        Real.exp (1 / 2) := by
  rw [uniformRatioSample, Set.indicator_of_mem hx]
  have ht := terminalVariance_pos' q
  constructor
  · exact Real.one_le_exp (div_nonneg (sq_nonneg _) (by positivity))
  · apply Real.exp_le_exp.mpr
    have hsq := norm_sq_le_terminalVariance_of_mem_truncatedBody q I hx
    apply (div_le_iff₀ (show 0 < 2 * terminalVariance q by positivity)).2
    nlinarith

end ArlibCommunity.Algorithms.CV18
