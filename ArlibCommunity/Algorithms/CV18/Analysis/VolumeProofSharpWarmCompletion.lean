/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledGoodBadTransition

/-! # Completing a warm subprobability without losing warmness

The elementary completion used by the first good/bad bridge adds an entire
copy of the stationary law and therefore changes `M` to `M + 1`.  At the
finite scheduled CV18 constants there is no spare unit: conditioning uses the
available factor two exactly.  The construction below fills only a suitable
fraction of the unused capacity `M • pi - residual`, preserving `M`.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open _root_.Arlib _root_.Arlib.MarkovChains

/-- A probability law dominated by an `M`-warm good measure plus a small bad
measure can be repaired, at the bad-mass cost, to an exactly `M`-warm
probability law.  The assumptions `1 ≤ M < ∞` are necessary capacity
conditions. -/
theorem exists_warm_probability_measureLeUpTo_of_le_good_add_bad_sharp
    {Omega : Type*} [MeasurableSpace Omega]
    (mu good bad pi : Measure Omega)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure pi] [IsFiniteMeasure bad]
    {M eta : ENNReal} (hM : 1 ≤ M) (hMtop : M ≠ ⊤)
    (hle : mu ≤ good + bad) (hgood : Arlib.IsWarm M good pi)
    (hbad : bad Set.univ ≤ eta) :
    ∃ nu : Measure Omega, IsProbabilityMeasure nu ∧
      Arlib.IsWarm M nu pi ∧ MeasureLeUpTo mu nu eta := by
  let residual := mu - bad
  have hresidualLeGood : residual ≤ good :=
    Measure.sub_le_of_le_add hle
  have hgoodLe : good ≤ M • pi :=
    (isWarm_iff_le_smul good pi).1 hgood
  have hresidualLe : residual ≤ M • pi :=
    hresidualLeGood.trans hgoodLe
  have hresidualMass : residual Set.univ ≤ 1 := by
    calc
      residual Set.univ ≤ mu Set.univ :=
        Measure.le_iff'.mp (Measure.sub_le (μ := mu) (ν := bad)) Set.univ
      _ = 1 := measure_univ
  let missing := 1 - residual Set.univ
  let capacity := M • pi - residual
  have hcapacityMass : capacity Set.univ = M - residual Set.univ := by
    rw [show capacity = M • pi - residual by rfl,
      Measure.sub_apply MeasurableSet.univ hresidualLe,
      Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  have hmissingLeCapacity : missing ≤ capacity Set.univ := by
    rw [hcapacityMass]
    exact tsub_le_tsub_right hM (residual Set.univ)
  by_cases hmissing0 : missing = 0
  · refine ⟨residual, ?_, ?_, ?_⟩
    · refine ⟨?_⟩
      have hmass : residual Set.univ = 1 := by
        apply le_antisymm hresidualMass
        exact (tsub_eq_zero_iff_le).mp hmissing0
      exact hmass
    · exact (isWarm_iff_le_smul residual pi).2 hresidualLe
    · refine ⟨bad, ?_, hbad⟩
      exact (Measure.sub_le_iff_le_add (μ := mu) (ν := bad)
        (ξ := residual)).mp le_rfl
  · have hcapacity0 : capacity Set.univ ≠ 0 := by
      intro hzero
      apply hmissing0
      apply bot_unique
      simpa [hzero] using hmissingLeCapacity
    have hcapacityTop : capacity Set.univ ≠ ⊤ := by
      rw [hcapacityMass]
      exact ne_top_of_le_ne_top hMtop tsub_le_self
    let coefficient := missing / capacity Set.univ
    have hcoefficientLe : coefficient ≤ 1 := by
      exact ENNReal.div_le_iff_le_mul (Or.inl hcapacity0)
        (Or.inl hcapacityTop) |>.2 <| by
        simpa using hmissingLeCapacity
    let filler := coefficient • capacity
    let nu := residual + filler
    have hfillerLe : filler ≤ capacity := by
      apply Measure.le_iff'.mpr
      intro S
      rw [show filler = coefficient • capacity by rfl,
        Measure.smul_apply, smul_eq_mul]
      exact (mul_le_of_le_one_left bot_le hcoefficientLe)
    have hnuLe : nu ≤ M • pi := by
      calc
        nu = residual + filler := rfl
        _ ≤ residual + capacity := by gcongr
        _ = M • pi := by
          rw [show capacity = M • pi - residual by rfl, add_comm,
            Measure.sub_add_cancel_of_le hresidualLe]
    have hfillerMass : filler Set.univ = missing := by
      rw [show filler = coefficient • capacity by rfl,
        Measure.smul_apply, smul_eq_mul]
      exact ENNReal.div_mul_cancel hcapacity0 hcapacityTop
    have hnuMass : nu Set.univ = 1 := by
      rw [show nu = residual + filler by rfl, Measure.add_apply,
        hfillerMass, show missing = 1 - residual Set.univ by rfl]
      exact add_tsub_cancel_of_le hresidualMass
    let hnuProb : IsProbabilityMeasure nu := ⟨hnuMass⟩
    refine ⟨nu, hnuProb, (isWarm_iff_le_smul nu pi).2 hnuLe, ?_⟩
    refine ⟨bad, ?_, hbad⟩
    calc
      mu ≤ residual + bad :=
        (Measure.sub_le_iff_le_add (μ := mu) (ν := bad)
          (ξ := residual)).mp le_rfl
      _ ≤ nu + bad := by
        gcongr
        exact Measure.le_add_right le_rfl

#print axioms exists_warm_probability_measureLeUpTo_of_le_good_add_bad_sharp

end ArlibCommunity.Algorithms.CV18
