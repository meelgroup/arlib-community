/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofApproxIndependence

/-!
# Second moment of a sequential approximately independent average

CV18 writes the within-phase empirical second moment using the independent
sample identity.  For an executable Markov collector, exact independence is
stronger than necessary: it is enough that the accumulated prefix sum and the
next bounded observation are approximately independent.  This file records
that recurrence directly.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The first `i` observations of a sequential family. -/
noncomputable def sequentialPrefixSum (Y : Nat → Omega → ℝ)
    (i : Nat) (omega : Omega) : ℝ :=
  ∑ j ∈ Finset.range i, Y j omega

theorem measurable_sequentialPrefixSum
    {Y : Nat → Omega → ℝ} (hY : ∀ i, Measurable (Y i)) (i : Nat) :
    Measurable (sequentialPrefixSum Y i) := by
  unfold sequentialPrefixSum
  exact (Finset.range i).measurable_fun_sum fun j _ => hY j

/-- A paper-style replacement for the IID calculation in CV18 equation (6).
If every bounded next observation is `epsilon`-independent of the accumulated
prefix, then the empirical average pays only the usual IID moment factor plus
an explicit additive covariance term. -/
theorem sequentialAverage_secondMoment_le_of_approxIndepPrefix
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {Y : Nat → Omega → ℝ} (hYmeas : ∀ i, Measurable (Y i))
    (k : Nat) (hk : 0 < k) {B mean factor epsilon : ℝ}
    (hB0 : 0 ≤ B) (hmean0 : 0 ≤ mean) (hepsilon0 : 0 ≤ epsilon)
    (hY0 : ∀ i, i < k → ∀ omega, 0 ≤ Y i omega)
    (hYB : ∀ i, i < k → ∀ omega, Y i omega ≤ B)
    (hmean : ∀ i, i < k → ∫ omega, Y i omega ∂mu ≤ mean)
    (hsecond : ∀ i, i < k →
      (∫ omega, (Y i omega) ^ 2 ∂mu) ≤ factor * mean ^ 2)
    (hind : ∀ i, i < k →
      ApproxIndepFun epsilon (sequentialPrefixSum Y i) (Y i) mu) :
    let average : Omega → ℝ := fun omega =>
      sequentialPrefixSum Y k omega / (k : ℝ)
    (∫ omega, average omega ^ 2 ∂mu) ≤
      (1 + (factor - 1) / (k : ℝ)) * mean ^ 2 +
        epsilon * (1 - 1 / (k : ℝ)) * B ^ 2 := by
  dsimp only
  let S : Nat → Omega → ℝ := sequentialPrefixSum Y
  have hSmeas : ∀ i, Measurable (S i) :=
    fun i => measurable_sequentialPrefixSum hYmeas i
  have hYint : ∀ i, i < k → Integrable (Y i) mu := by
    intro i hi
    refine (integrable_const B).mono' (hYmeas i).aestronglyMeasurable ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (hY0 i hi omega)]
    simpa [Real.norm_eq_abs, abs_of_nonneg hB0] using hYB i hi omega
  have hYsqInt : ∀ i, i < k → Integrable (fun omega => (Y i omega) ^ 2) mu := by
    intro i hi
    refine (integrable_const (B ^ 2)).mono'
      ((hYmeas i).pow_const 2).aestronglyMeasurable ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Y i omega))]
    nlinarith [hY0 i hi omega, hYB i hi omega, hB0]
  have hS0 : ∀ i, i ≤ k → ∀ omega, 0 ≤ S i omega := by
    intro i hi omega
    unfold S sequentialPrefixSum
    exact Finset.sum_nonneg fun j hj => hY0 j (by
      have : j < i := Finset.mem_range.mp hj
      omega) omega
  have hSB : ∀ i, i ≤ k → ∀ omega, S i omega ≤ (i : ℝ) * B := by
    intro i hi omega
    unfold S sequentialPrefixSum
    calc
      ∑ j ∈ Finset.range i, Y j omega ≤ ∑ _j ∈ Finset.range i, B := by
        exact Finset.sum_le_sum fun j hj => hYB j (by
          have : j < i := Finset.mem_range.mp hj
          omega) omega
      _ = (i : ℝ) * B := by simp
  have hSint : ∀ i, i ≤ k → Integrable (S i) mu := by
    intro i hi
    refine (integrable_const ((i : ℝ) * B)).mono'
      (hSmeas i).aestronglyMeasurable ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (hS0 i hi omega)]
    simpa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg i) hB0)]
      using hSB i hi omega
  have hSsqInt : ∀ i, i ≤ k →
      Integrable (fun omega => (S i omega) ^ 2) mu := by
    intro i hi
    refine (integrable_const (((i : ℝ) * B) ^ 2)).mono'
      ((hSmeas i).pow_const 2).aestronglyMeasurable ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (S i omega))]
    nlinarith [hS0 i hi omega, hSB i hi omega,
      mul_nonneg (Nat.cast_nonneg i) hB0]
  have hSYint : ∀ i, i < k →
      Integrable (fun omega => S i omega * Y i omega) mu := by
    intro i hi
    refine (integrable_const (((i : ℝ) * B) * B)).mono'
      ((hSmeas i).mul (hYmeas i)).aestronglyMeasurable ?_
    filter_upwards with omega
    have hSnonneg := hS0 i (Nat.le_of_lt hi) omega
    have hSbound := hSB i (Nat.le_of_lt hi) omega
    have hYnonneg := hY0 i hi omega
    have hYbound := hYB i hi omega
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hSnonneg hYnonneg)]
    exact mul_le_mul hSbound hYbound hYnonneg
      (mul_nonneg (Nat.cast_nonneg i) hB0)
  have hSmean : ∀ i, i ≤ k → ∫ omega, S i omega ∂mu ≤ (i : ℝ) * mean := by
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
  have hsum : ∀ i, i ≤ k →
      (∫ omega, (S i omega) ^ 2 ∂mu) ≤
        (i : ℝ) * factor * mean ^ 2 +
          ((i : ℝ) ^ 2 - (i : ℝ)) * mean ^ 2 +
          epsilon * ((i : ℝ) ^ 2 - (i : ℝ)) * B ^ 2 := by
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
          have hcross := hSYint i hiK
          have hYiSq := hYsqInt i hiK
          calc
            (∫ omega, (S i omega + Y i omega) ^ 2 ∂mu) =
                ∫ omega,
                  (S i omega) ^ 2 + 2 * (S i omega * Y i omega) +
                    (Y i omega) ^ 2 ∂mu := by
              apply integral_congr_ae
              filter_upwards with omega
              ring
            _ = (∫ omega,
                    (S i omega) ^ 2 + 2 * (S i omega * Y i omega) ∂mu) +
                  ∫ omega, (Y i omega) ^ 2 ∂mu :=
              integral_add (hSiSq.add (hcross.const_mul 2)) hYiSq
            _ = (∫ omega, (S i omega) ^ 2 ∂mu) +
                  2 * (∫ omega, S i omega * Y i omega ∂mu) +
                    ∫ omega, (Y i omega) ^ 2 ∂mu := by
              rw [integral_add hSiSq (hcross.const_mul 2), integral_const_mul]
        have hcov := (hind i hiK).abs_integral_mul_sub_mul_integral_le
          mu (hSmeas i) (hYmeas i)
          (mul_nonneg (Nat.cast_nonneg i) hB0) hB0 hepsilon0
          (hS0 i hiLe) (hSB i hiLe) (hY0 i hiK) (hYB i hiK)
        have hcross : (∫ omega, S i omega * Y i omega ∂mu) ≤
            (i : ℝ) * mean ^ 2 + epsilon * ((i : ℝ) * B) * B := by
          have hcovUpper := (abs_le.mp hcov).2
          have hSi0 : 0 ≤ ∫ omega, S i omega ∂mu :=
            integral_nonneg (hS0 i hiLe)
          have hYi0 : 0 ≤ ∫ omega, Y i omega ∂mu :=
            integral_nonneg (hY0 i hiK)
          have hprod :
              (∫ omega, S i omega ∂mu) *
                  (∫ omega, Y i omega ∂mu) ≤
                (i : ℝ) * mean ^ 2 := by
            calc
              (∫ omega, S i omega ∂mu) *
                    (∫ omega, Y i omega ∂mu) ≤
                  ((i : ℝ) * mean) * mean :=
                mul_le_mul (hSmean i hiLe) (hmean i hiK)
                  hYi0 (mul_nonneg (Nat.cast_nonneg i) hmean0)
              _ = (i : ℝ) * mean ^ 2 := by ring
          linarith
        rw [hexpand]
        calc
          (∫ omega, (S i omega) ^ 2 ∂mu) +
                2 * (∫ omega, S i omega * Y i omega ∂mu) +
              ∫ omega, (Y i omega) ^ 2 ∂mu ≤
              ((i : ℝ) * factor * mean ^ 2 +
                ((i : ℝ) ^ 2 - (i : ℝ)) * mean ^ 2 +
                epsilon * ((i : ℝ) ^ 2 - (i : ℝ)) * B ^ 2) +
              2 * ((i : ℝ) * mean ^ 2 +
                epsilon * ((i : ℝ) * B) * B) +
              factor * mean ^ 2 := by
                linarith [ih hiLe, hcross, hsecond i hiK]
          _ = ((i + 1 : Nat) : ℝ) * factor * mean ^ 2 +
                (((i + 1 : Nat) : ℝ) ^ 2 - ((i + 1 : Nat) : ℝ)) *
                  mean ^ 2 +
                epsilon *
                  (((i + 1 : Nat) : ℝ) ^ 2 - ((i + 1 : Nat) : ℝ)) *
                    B ^ 2 := by
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
          epsilon * ((k : ℝ) ^ 2 - (k : ℝ)) * B ^ 2 := hfinal
    _ = ((1 + (factor - 1) / (k : ℝ)) * mean ^ 2 +
          epsilon * (1 - 1 / (k : ℝ)) * B ^ 2) * (k : ℝ) ^ 2 := by
      field_simp [hkR.ne']
      ring

#print axioms sequentialAverage_secondMoment_le_of_approxIndepPrefix

end ArlibCommunity.Algorithms.CV18
