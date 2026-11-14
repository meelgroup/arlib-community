import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofPhaseMomentAssembly

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-- The elementary moment package used after CV18 Lemma 7.14.  It is stated
around the *actual* mean, so an approximate phase law is sufficient. -/
theorem actualMeanTruncation_moment_package
    {S : Type*} [MeasurableSpace S]
    (mu : Measure S) [IsProbabilityMeasure mu]
    {W : S → ℝ} (hWmeas : Measurable W) (hW0 : ∀ x, 0 ≤ W x)
    (hWmem : MemLp W 2 mu)
    {raw alpha : ℝ} (hraw : raw = ∫ x, W x ∂mu)
    (hrawPos : 0 < raw) (halpha : 1024 ≤ alpha)
    (hWsecond : (∫ x, W x ^ 2 ∂mu) ≤ 4 * raw ^ 2) :
    let V := fun x => min (W x) (alpha * raw)
    let mean := ∫ x, V x ∂mu
    let second := ∫ x, V x ^ 2 ∂mu
    0 < mean ∧ raw ≤ 2 * mean ∧ mean ^ 2 ≤ second ∧
      raw ^ 2 ≤ 2 * second := by
  dsimp only
  have halphaPos : 0 < alpha := by linarith
  have hcapPos : 0 < alpha * raw := mul_pos halphaPos hrawPos
  have htrunc := integral_min_ge_integral_sub_secondMoment_div_four mu
    (hWmem.integrable (by norm_num)) hWmem.integrable_sq hW0 hcapPos
  rw [← hraw] at htrunc
  have hloss : (∫ x, W x ^ 2 ∂mu) / (4 * (alpha * raw)) ≤ raw / 1024 := by
    rw [div_le_iff₀ (mul_pos (by norm_num) hcapPos)]
    have hscaled := mul_le_mul_of_nonneg_right halpha hrawPos.le
    nlinarith [hWsecond]
  have hmeanLower : (3 / 4 : ℝ) * raw ≤
      ∫ x, min (W x) (alpha * raw) ∂mu := by
    linarith
  have hVmeas : Measurable fun x => min (W x) (alpha * raw) :=
    hWmeas.min measurable_const
  have hV0 : ∀ x, 0 ≤ min (W x) (alpha * raw) := by
    intro x
    exact le_min (hW0 x) hcapPos.le
  have hVmem : MemLp (fun x => min (W x) (alpha * raw)) 2 mu := by
    apply MemLp.of_bound hVmeas.aestronglyMeasurable (alpha * raw)
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hV0 x)]
    exact min_le_right _ _
  have hvariance : 0 ≤ ∫ x,
      (min (W x) (alpha * raw) -
        (∫ y, min (W y) (alpha * raw) ∂mu)) ^ 2 ∂mu :=
    integral_nonneg fun _ => sq_nonneg _
  rw [integral_sub_const_sq_eq mu hVmem
    (∫ y, min (W y) (alpha * raw) ∂mu)] at hvariance
  have hmeanSq : (∫ x, min (W x) (alpha * raw) ∂mu) ^ 2 ≤
      ∫ x, min (W x) (alpha * raw) ^ 2 ∂mu := by
    nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · exact hmeanSq
  · nlinarith [sq_nonneg
      ((∫ x, min (W x) (alpha * raw) ∂mu) - (3 / 4) * raw)]

#print axioms actualMeanTruncation_moment_package

end ArlibCommunity.Algorithms.CV18
