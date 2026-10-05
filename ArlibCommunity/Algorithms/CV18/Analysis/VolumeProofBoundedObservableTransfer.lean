import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofMeasureApproximation

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open Arlib

/-- Total variation transfers an observable bounded in `[0, B]`, with the
expected factor `B` in the additive error. -/
theorem Arlib.TVLe.integral_le_of_nonnegative_le
    {S : Type*} [MeasurableSpace S]
    {mu nu : Measure S} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {epsilon : ENNReal} (h : TVLe mu nu epsilon) (hepsilon : epsilon ≠ ⊤)
    {f : S → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 < B)
    (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B) :
    |∫ x, f x ∂mu - ∫ x, f x ∂nu| ≤ B * epsilon.toReal := by
  let g : S → ℝ := fun x => f x / B
  have hg : Measurable g := hf.div_const B
  have hg0 : ∀ x, 0 ≤ g x := by
    intro x
    exact div_nonneg (hf0 x) hB.le
  have hg1 : ∀ x, g x ≤ 1 := by
    intro x
    exact (div_le_one hB).2 (hfB x)
  have hscaled := h.integral_le hepsilon hg hg0 hg1
  have hmu : (∫ x, g x ∂mu) = (∫ x, f x ∂mu) / B := by
    change (∫ x, f x / B ∂mu) = _
    exact integral_div B f
  have hnu : (∫ x, g x ∂nu) = (∫ x, f x ∂nu) / B := by
    change (∫ x, f x / B ∂nu) = _
    exact integral_div B f
  rw [hmu, hnu, ← sub_div] at hscaled
  rw [abs_div, abs_of_pos hB] at hscaled
  simpa [mul_comm] using (div_le_iff₀ hB).mp hscaled

/-- The corresponding second-moment transfer for an observable in `[0, B]`. -/
theorem Arlib.TVLe.integral_sq_le_of_nonnegative_le
    {S : Type*} [MeasurableSpace S]
    {mu nu : Measure S} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {epsilon : ENNReal} (h : TVLe mu nu epsilon) (hepsilon : epsilon ≠ ⊤)
    {f : S → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 < B)
    (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B) :
    |∫ x, f x ^ 2 ∂mu - ∫ x, f x ^ 2 ∂nu| ≤
      B ^ 2 * epsilon.toReal := by
  apply Arlib.TVLe.integral_le_of_nonnegative_le h hepsilon
    (hf.pow_const 2) (sq_pos_of_pos hB)
  · intro x
    exact sq_nonneg (f x)
  · intro x
    nlinarith [hf0 x, hfB x]

/-- `MeasureLeUpTo` form of the bounded first-moment transfer. -/
theorem MeasureLeUpTo.integral_le_of_nonnegative_le
    {S : Type*} [MeasurableSpace S]
    {mu nu : Measure S} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {epsilon : ENNReal} (h : MeasureLeUpTo mu nu epsilon)
    (hepsilon : epsilon ≠ ⊤)
    {f : S → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 < B)
    (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B) :
    |∫ x, f x ∂mu - ∫ x, f x ∂nu| ≤ B * epsilon.toReal :=
  Arlib.TVLe.integral_le_of_nonnegative_le h.to_tvLe hepsilon hf hB hf0 hfB

/-- `MeasureLeUpTo` form of the bounded second-moment transfer. -/
theorem MeasureLeUpTo.integral_sq_le_of_nonnegative_le
    {S : Type*} [MeasurableSpace S]
    {mu nu : Measure S} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {epsilon : ENNReal} (h : MeasureLeUpTo mu nu epsilon)
    (hepsilon : epsilon ≠ ⊤)
    {f : S → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 < B)
    (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B) :
    |∫ x, f x ^ 2 ∂mu - ∫ x, f x ^ 2 ∂nu| ≤
      B ^ 2 * epsilon.toReal :=
  Arlib.TVLe.integral_sq_le_of_nonnegative_le h.to_tvLe hepsilon hf hB hf0 hfB

/-- A small TV perturbation of a phase law preserves a positive first moment
and a constant relative second-moment bound.  The deliberately slack factor
`4` is the input expected by `actualMeanTruncation_moment_package`. -/
theorem Arlib.TVLe.positive_mean_and_second_le_four
    {S : Type*} [MeasurableSpace S]
    {mu nu : Measure S} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {epsilon : ENNReal} (h : Arlib.TVLe mu nu epsilon)
    (hepsilon : epsilon ≠ ⊤)
    {f : S → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 < B)
    (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B)
    {idealMean : ℝ} (hidealMean : idealMean = ∫ x, f x ∂nu)
    (hidealMeanPos : 0 < idealMean)
    (hidealSecond : (∫ x, f x ^ 2 ∂nu) ≤ 2 * idealMean ^ 2)
    (hmeanError : B * epsilon.toReal ≤ idealMean / 8)
    (hsecondError : B ^ 2 * epsilon.toReal ≤ idealMean ^ 2 / 8) :
    0 < ∫ x, f x ∂mu ∧
      (∫ x, f x ^ 2 ∂mu) ≤ 4 * (∫ x, f x ∂mu) ^ 2 := by
  have hmeanAbs := Arlib.TVLe.integral_le_of_nonnegative_le
    h hepsilon hf hB hf0 hfB
  rw [← hidealMean] at hmeanAbs
  have hmeanBounds := abs_le.mp hmeanAbs
  have hrawLower : (7 / 8 : ℝ) * idealMean ≤ ∫ x, f x ∂mu := by
    nlinarith
  have hrawPos : 0 < ∫ x, f x ∂mu := by
    nlinarith
  have hsecondAbs := Arlib.TVLe.integral_sq_le_of_nonnegative_le
    h hepsilon hf hB hf0 hfB
  have hsecondBounds := abs_le.mp hsecondAbs
  have hactualSecond : (∫ x, f x ^ 2 ∂mu) ≤
      (17 / 8 : ℝ) * idealMean ^ 2 := by
    nlinarith
  constructor
  · exact hrawPos
  · nlinarith [sq_nonneg
      ((∫ x, f x ∂mu) - (7 / 8 : ℝ) * idealMean)]

#print axioms Arlib.TVLe.integral_le_of_nonnegative_le
#print axioms Arlib.TVLe.integral_sq_le_of_nonnegative_le
#print axioms MeasureLeUpTo.integral_le_of_nonnegative_le
#print axioms MeasureLeUpTo.integral_sq_le_of_nonnegative_le
#print axioms Arlib.TVLe.positive_mean_and_second_le_four

end ArlibCommunity.Algorithms.CV18
