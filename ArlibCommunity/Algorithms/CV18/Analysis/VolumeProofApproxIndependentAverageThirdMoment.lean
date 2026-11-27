/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofApproxIndependentAverage
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofApproxIndependentThirdMoment

/-!
# Equation (6) for unbounded `L³` observables

This is the unbounded replacement for CV18's IID cross-term calculation.
Approximate independence and third moments contribute an explicit
`3 * epsilon^(1/3)` covariance term.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

variable {Omega : Type*} [MeasurableSpace Omega]

set_option maxHeartbeats 1000000 in
/-- Sequential equation (6) using the optimized `L³` covariance bound.
The prefix third-moment premise is naturally obtained from Minkowski (or the
elementary cube-of-a-sum inequality) when every coordinate has third moment
at most `A³`. -/
theorem sequentialAverage_secondMoment_le_of_approxIndepPrefix_thirdMoment
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {Y : Nat → Omega → ℝ} (hYmeas : ∀ i, Measurable (Y i))
    (k : Nat) (hk : 0 < k) {A mean factor epsilon : ℝ}
    (hA : 0 < A) (hmean0 : 0 ≤ mean) (hepsilon : 0 < epsilon)
    (hY0 : ∀ i, i < k → ∀ omega, 0 ≤ Y i omega)
    (hY3 : ∀ i, i < k → MemLp (Y i) 3 mu)
    (hmean : ∀ i, i < k → ∫ omega, Y i omega ∂mu ≤ mean)
    (hsecond : ∀ i, i < k →
      (∫ omega, (Y i omega) ^ 2 ∂mu) ≤ factor * mean ^ 2)
    (hprefix3 : ∀ i, i ≤ k →
      MemLp (sequentialPrefixSum Y i) 3 mu)
    (hprefixCube : ∀ i, i ≤ k →
      (∫ omega, sequentialPrefixSum Y i omega ^ 3 ∂mu) ≤
        ((i : ℝ) * A) ^ 3)
    (hYcube : ∀ i, i < k →
      (∫ omega, Y i omega ^ 3 ∂mu) ≤ A ^ 3)
    (hind : ∀ i, i < k →
      ApproxIndepFun epsilon (sequentialPrefixSum Y i) (Y i) mu) :
    let average : Omega → ℝ := fun omega =>
      sequentialPrefixSum Y k omega / (k : ℝ)
    (∫ omega, average omega ^ 2 ∂mu) ≤
      (1 + (factor - 1) / (k : ℝ)) * mean ^ 2 +
        3 * epsilon ^ (1 / 3 : ℝ) *
          (1 - 1 / (k : ℝ)) * A ^ 2 := by
  dsimp only
  let S : Nat → Omega → ℝ := sequentialPrefixSum Y
  have hSmeas : ∀ i, Measurable (S i) :=
    fun i => measurable_sequentialPrefixSum hYmeas i
  have hS0 : ∀ i, i ≤ k → ∀ omega, 0 ≤ S i omega := by
    intro i hi omega
    unfold S sequentialPrefixSum
    exact Finset.sum_nonneg fun j hj => hY0 j (by
      have : j < i := Finset.mem_range.mp hj
      omega) omega
  have hYint : ∀ i, i < k → Integrable (Y i) mu :=
    fun i hi => (hY3 i hi).integrable (by norm_num)
  have hYsqInt : ∀ i, i < k →
      Integrable (fun omega => (Y i omega) ^ 2) mu := by
    intro i hi
    exact ((hY3 i hi).mono_exponent (by norm_num)).integrable_sq
  have hSint : ∀ i, i ≤ k → Integrable (S i) mu :=
    fun i hi => (hprefix3 i hi).integrable (by norm_num)
  have hSsqInt : ∀ i, i ≤ k →
      Integrable (fun omega => (S i omega) ^ 2) mu := by
    intro i hi
    exact ((hprefix3 i hi).mono_exponent (by norm_num)).integrable_sq
  have hSYint : ∀ i, i < k →
      Integrable (fun omega => S i omega * Y i omega) mu := by
    intro i hi
    exact ((hprefix3 i (Nat.le_of_lt hi)).mono_exponent
      (by norm_num : (2 : ENNReal) ≤ 3)).integrable_mul
        ((hY3 i hi).mono_exponent (by norm_num : (2 : ENNReal) ≤ 3))
  have hSmean : ∀ i, i ≤ k →
      ∫ omega, S i omega ∂mu ≤ (i : ℝ) * mean := by
    intro i hi
    unfold S sequentialPrefixSum
    rw [integral_finsetSum (Finset.range i) (fun j hj =>
      hYint j (by
        have : j < i := Finset.mem_range.mp hj
        omega))]
    calc
      ∑ j ∈ Finset.range i, ∫ omega, Y j omega ∂mu ≤
          ∑ _j ∈ Finset.range i, mean := by
        exact Finset.sum_le_sum fun j hj => hmean j (by
          have : j < i := Finset.mem_range.mp hj
          omega)
      _ = (i : ℝ) * mean := by simp
  have hcross : ∀ i, i < k →
      (∫ omega, S i omega * Y i omega ∂mu) ≤
        (i : ℝ) * mean ^ 2 +
          3 * epsilon ^ (1 / 3 : ℝ) * (i : ℝ) * A ^ 2 := by
    intro i hi
    cases i with
    | zero => simp [S, sequentialPrefixSum]
    | succ i =>
        have hiLe : i + 1 ≤ k := Nat.le_of_lt hi
        have hscale : 0 < ((i + 1 : Nat) : ℝ) * A := by positivity
        have hcov := (hind (i + 1) hi).integral_mul_le_mul_integral_add_three_cbrt_mul
            mu (hSmeas (i + 1)) (hYmeas (i + 1))
            (hprefix3 (i + 1) hiLe) (hY3 (i + 1) hi)
            hscale hA hepsilon (hS0 (i + 1) hiLe) (hY0 (i + 1) hi)
            (hprefixCube (i + 1) hiLe) (hYcube (i + 1) hi)
        have hSi0 : 0 ≤ ∫ omega, S (i + 1) omega ∂mu :=
          integral_nonneg (hS0 (i + 1) hiLe)
        have hYi0 : 0 ≤ ∫ omega, Y (i + 1) omega ∂mu :=
          integral_nonneg (hY0 (i + 1) hi)
        have hprod :
            (∫ omega, S (i + 1) omega ∂mu) *
                (∫ omega, Y (i + 1) omega ∂mu) ≤
              ((i + 1 : Nat) : ℝ) * mean ^ 2 := by
          calc
            _ ≤ (((i + 1 : Nat) : ℝ) * mean) * mean :=
              mul_le_mul (hSmean (i + 1) hiLe) (hmean (i + 1) hi)
                hYi0 (mul_nonneg (Nat.cast_nonneg _) hmean0)
            _ = ((i + 1 : Nat) : ℝ) * mean ^ 2 := by ring
        calc
          (∫ omega, S (i + 1) omega * Y (i + 1) omega ∂mu) ≤
              (∫ omega, S (i + 1) omega ∂mu) *
                  (∫ omega, Y (i + 1) omega ∂mu) +
                3 * epsilon ^ (1 / 3 : ℝ) *
                  (((i + 1 : Nat) : ℝ) * A) * A := hcov
          _ ≤ ((i + 1 : Nat) : ℝ) * mean ^ 2 +
                3 * epsilon ^ (1 / 3 : ℝ) *
                  (((i + 1 : Nat) : ℝ) * A) * A := by gcongr
          _ = ((i + 1 : Nat) : ℝ) * mean ^ 2 +
                3 * epsilon ^ (1 / 3 : ℝ) *
                  ((i + 1 : Nat) : ℝ) * A ^ 2 := by ring
  have hsum : ∀ i, i ≤ k →
      (∫ omega, (S i omega) ^ 2 ∂mu) ≤
        (i : ℝ) * factor * mean ^ 2 +
          ((i : ℝ) ^ 2 - (i : ℝ)) * mean ^ 2 +
          3 * epsilon ^ (1 / 3 : ℝ) *
            ((i : ℝ) ^ 2 - (i : ℝ)) * A ^ 2 := by
    intro i hi
    induction i with
    | zero => simp [S, sequentialPrefixSum]
    | succ i ih =>
        have hiK : i < k := by omega
        have hiLe : i ≤ k := Nat.le_of_lt hiK
        have hrec : S (i + 1) = fun omega => S i omega + Y i omega := by
          funext omega
          simpa [S, sequentialPrefixSum, Nat.succ_eq_add_one] using
            (Finset.sum_range_succ (fun j => Y j omega) i)
        have hexpand :
            (∫ omega, (S (i + 1) omega) ^ 2 ∂mu) =
              (∫ omega, (S i omega) ^ 2 ∂mu) +
                2 * (∫ omega, S i omega * Y i omega ∂mu) +
                  ∫ omega, (Y i omega) ^ 2 ∂mu := by
          rw [hrec]
          have hSiSq := hSsqInt i hiLe
          have hcrossInt := hSYint i hiK
          have hYiSq := hYsqInt i hiK
          calc
            (∫ omega, (S i omega + Y i omega) ^ 2 ∂mu) =
                ∫ omega, (S i omega) ^ 2 +
                  2 * (S i omega * Y i omega) + (Y i omega) ^ 2 ∂mu := by
              apply integral_congr_ae
              filter_upwards with omega
              ring
            _ = (∫ omega, (S i omega) ^ 2 +
                    2 * (S i omega * Y i omega) ∂mu) +
                  ∫ omega, (Y i omega) ^ 2 ∂mu :=
              integral_add (hSiSq.add (hcrossInt.const_mul 2)) hYiSq
            _ = (∫ omega, (S i omega) ^ 2 ∂mu) +
                  2 * (∫ omega, S i omega * Y i omega ∂mu) +
                    ∫ omega, (Y i omega) ^ 2 ∂mu := by
              rw [integral_add hSiSq (hcrossInt.const_mul 2), integral_const_mul]
        rw [hexpand]
        calc
          _ ≤ ((i : ℝ) * factor * mean ^ 2 +
                ((i : ℝ) ^ 2 - (i : ℝ)) * mean ^ 2 +
                3 * epsilon ^ (1 / 3 : ℝ) *
                  ((i : ℝ) ^ 2 - (i : ℝ)) * A ^ 2) +
              2 * ((i : ℝ) * mean ^ 2 +
                3 * epsilon ^ (1 / 3 : ℝ) * (i : ℝ) * A ^ 2) +
              factor * mean ^ 2 := by
            gcongr
            · exact ih hiLe
            · exact hcross i hiK
            · exact hsecond i hiK
          _ = (((i + 1 : Nat) : ℝ) * factor * mean ^ 2 +
                (((i + 1 : Nat) : ℝ) ^ 2 - ((i + 1 : Nat) : ℝ)) * mean ^ 2 +
                3 * epsilon ^ (1 / 3 : ℝ) *
                  (((i + 1 : Nat) : ℝ) ^ 2 - ((i + 1 : Nat) : ℝ)) *
                    A ^ 2) := by
            push_cast
            ring
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hfinal := hsum k le_rfl
  rw [show (∫ omega, (S k omega / (k : ℝ)) ^ 2 ∂mu) =
      (∫ omega, (S k omega) ^ 2 ∂mu) / (k : ℝ) ^ 2 by
    simp_rw [div_pow]
    rw [integral_div]]
  apply (div_le_iff₀ (sq_pos_of_pos hkR)).2
  calc
    (∫ omega, (S k omega) ^ 2 ∂mu) ≤
        (k : ℝ) * factor * mean ^ 2 +
          ((k : ℝ) ^ 2 - (k : ℝ)) * mean ^ 2 +
          3 * epsilon ^ (1 / 3 : ℝ) *
            ((k : ℝ) ^ 2 - (k : ℝ)) * A ^ 2 := hfinal
    _ = ((1 + (factor - 1) / (k : ℝ)) * mean ^ 2 +
          3 * epsilon ^ (1 / 3 : ℝ) *
            (1 - 1 / (k : ℝ)) * A ^ 2) * (k : ℝ) ^ 2 := by
      field_simp [hkR.ne']
      ring

#print axioms sequentialAverage_secondMoment_le_of_approxIndepPrefix_thirdMoment

end ArlibCommunity.Algorithms.CV18
