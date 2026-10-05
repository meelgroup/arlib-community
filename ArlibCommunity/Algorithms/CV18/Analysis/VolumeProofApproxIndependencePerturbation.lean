/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofExactChance

/-! # Stability of approximate independence under law perturbations -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory Set

/-- Pushforward form of approximate independence.  This is useful after a
future history kernel has been represented by a measurable trace map that
preserves the two already-created coordinates. -/
theorem ApproxIndepFun.map
    {Omega Omega' S T : Type*} [MeasurableSpace Omega]
    [MeasurableSpace Omega'] [MeasurableSpace S] [MeasurableSpace T]
    {epsilon : ℝ} {mu : Measure Omega} (f : Omega → Omega')
    (hf : Measurable f) (X : Omega' → S) (Y : Omega' → T)
    (hX : Measurable X) (hY : Measurable Y)
    (h : ApproxIndepFun epsilon (X ∘ f) (Y ∘ f) mu) :
    ApproxIndepFun epsilon X Y (mu.map f) := by
  intro A hA B hB
  have hXA : MeasurableSet (X ⁻¹' A) := hX hA
  have hYB : MeasurableSet (Y ⁻¹' B) := hY hB
  have hjoint : (mu.map f).real (X ⁻¹' A ∩ Y ⁻¹' B) =
      mu.real (f ⁻¹' (X ⁻¹' A ∩ Y ⁻¹' B)) :=
    congrArg ENNReal.toReal (Measure.map_apply hf (hXA.inter hYB))
  have hleft : (mu.map f).real (X ⁻¹' A) =
      mu.real (f ⁻¹' (X ⁻¹' A)) :=
    congrArg ENNReal.toReal (Measure.map_apply hf hXA)
  have hright : (mu.map f).real (Y ⁻¹' B) =
      mu.real (f ⁻¹' (Y ⁻¹' B)) :=
    congrArg ENNReal.toReal (Measure.map_apply hf hYB)
  rw [hjoint, hleft, hright]
  change |mu.real (((X ∘ f) ⁻¹' A) ∩ ((Y ∘ f) ⁻¹' B)) -
      mu.real ((X ∘ f) ⁻¹' A) * mu.real ((Y ∘ f) ⁻¹' B)| ≤ epsilon
  exact h A hA B hB

/-- Changing the ambient probability law by total variation `delta` changes
the strong-mixing coefficient by at most `3 * delta`.  One copy pays for the
joint rectangle and two copies pay for its marginal product. -/
theorem ApproxIndepFun.of_tvLe
    {Omega S T : Type*} [MeasurableSpace Omega]
    [MeasurableSpace S] [MeasurableSpace T]
    (mu nu : Measure Omega) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {delta : ENNReal} (hdelta : delta ≠ ⊤)
    {epsilon : ℝ} (X : Omega → S) (Y : Omega → T)
    (hX : Measurable X) (hY : Measurable Y)
    (htv : Arlib.TVLe mu nu delta)
    (hind : ApproxIndepFun epsilon X Y nu) :
    ApproxIndepFun (epsilon + 3 * delta.toReal) X Y mu := by
  intro A hA B hB
  let XA : Set Omega := X ⁻¹' A
  let YB : Set Omega := Y ⁻¹' B
  have hXA : MeasurableSet XA := hX hA
  have hYB : MeasurableSet YB := hY hB
  have hXY : MeasurableSet (XA ∩ YB) := hXA.inter hYB
  have hjoint := htv.abs_measureReal_sub_le hdelta hXY
  have hleft := htv.abs_measureReal_sub_le hdelta hXA
  have hright := htv.abs_measureReal_sub_le hdelta hYB
  have hnuIndep := hind A hA B hB
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
    epsilon + 3 * delta.toReal
  calc
    |mu.real (XA ∩ YB) - mu.real XA * mu.real YB| ≤
        |mu.real (XA ∩ YB) - nu.real (XA ∩ YB)| +
          |nu.real (XA ∩ YB) - nu.real XA * nu.real YB| +
          |nu.real XA * nu.real YB - mu.real XA * mu.real YB| := by
      calc
        _ ≤ |mu.real (XA ∩ YB) - nu.real (XA ∩ YB)| +
            |nu.real (XA ∩ YB) - mu.real XA * mu.real YB| :=
          abs_sub_le _ _ _
        _ ≤ |mu.real (XA ∩ YB) - nu.real (XA ∩ YB)| +
            (|nu.real (XA ∩ YB) - nu.real XA * nu.real YB| +
              |nu.real XA * nu.real YB - mu.real XA * mu.real YB|) := by
          gcongr
          exact abs_sub_le _ _ _
        _ = _ := by ring
    _ ≤ delta.toReal + epsilon + 2 * delta.toReal := by
      gcongr
    _ = epsilon + 3 * delta.toReal := by ring

/-- Additive domination form of `ApproxIndepFun.of_tvLe`. -/
theorem ApproxIndepFun.of_measureLeUpTo
    {Omega S T : Type*} [MeasurableSpace Omega]
    [MeasurableSpace S] [MeasurableSpace T]
    (mu nu : Measure Omega) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {delta : ENNReal} (hdelta : delta ≠ ⊤)
    {epsilon : ℝ} (X : Omega → S) (Y : Omega → T)
    (hX : Measurable X) (hY : Measurable Y)
    (hdom : MeasureLeUpTo mu nu delta)
    (hind : ApproxIndepFun epsilon X Y nu) :
    ApproxIndepFun (epsilon + 3 * delta.toReal) X Y mu :=
  ApproxIndepFun.of_tvLe mu nu hdelta X Y hX hY hdom.to_tvLe hind

#print axioms ApproxIndepFun.of_tvLe
#print axioms ApproxIndepFun.of_measureLeUpTo
#print axioms ApproxIndepFun.map

end ArlibCommunity.Algorithms.CV18
