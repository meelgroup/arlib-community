/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Foundations.MarkovChainTheory.Basic.Warmness

/-!
# Two Markov chains whose steps are close

If two Markov kernels `Q` and `P` give every event masses within `β x` from every point
`x`, the chains they drive stay close (`tvLe_iterate_of_close`): after `m` steps, within
the sum over the steps of the average of `β` under the `P`-chain.

`tvLe_iterate_split` specialises this to a start `σ` that is `M`-warm with respect to a
`P`-invariant `π` outside an exceptional set `S`: the warm part pays `M · ∫ β dπ` per step,
and the exceptional part pays its mass `σ(S)` once.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ArlibCommunity.Algorithms.HitAndRun

open ArlibCommunity.Foundations.MarkovChainTheory (iterate step step_apply lintegral_le_of_tvLe
  iterate_zero iterate_succ isWarm_iterate_of_invariant isWarm_iff_le_smul)
open ArlibCommunity.Foundations.Convex (TVLe IsWarm)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **One step of two close kernels.** -/
theorem tvLe_step_of_close (Q P : Kernel Ω Ω) [IsMarkovKernel Q] [IsMarkovKernel P]
    {β : Ω → ℝ≥0∞}
    (hclose : ∀ x S, MeasurableSet S → Q x S ≤ P x S + β x ∧ P x S ≤ Q x S + β x)
    {μ ν : Measure Ω} {a : ℝ≥0∞} (h : TVLe μ ν a) :
    TVLe (step Q μ) (step P ν) (a + ∫⁻ x, β x ∂ν) := by
  intro S hS
  have hQm : Measurable fun x => Q x S := Kernel.measurable_coe Q hS
  have hPm : Measurable fun x => P x S := Kernel.measurable_coe P hS
  rw [step_apply Q μ hS, step_apply P ν hS]
  constructor
  · calc ∫⁻ x, Q x S ∂μ ≤ ∫⁻ x, Q x S ∂ν + a :=
          lintegral_le_of_tvLe h hQm fun _ => prob_le_one
      _ ≤ ∫⁻ x, (P x S + β x) ∂ν + a := by
          gcongr with x; exact (hclose x S hS).1
      _ = ∫⁻ x, P x S ∂ν + (a + ∫⁻ x, β x ∂ν) := by
          rw [lintegral_add_left hPm]; ring
  · calc ∫⁻ x, P x S ∂ν ≤ ∫⁻ x, (Q x S + β x) ∂ν :=
          lintegral_mono fun x => (hclose x S hS).2
      _ = ∫⁻ x, Q x S ∂ν + ∫⁻ x, β x ∂ν := lintegral_add_left hQm _
      _ ≤ (∫⁻ x, Q x S ∂μ + a) + ∫⁻ x, β x ∂ν := by
          gcongr; exact lintegral_le_of_tvLe h.symm hQm fun _ => prob_le_one
      _ = ∫⁻ x, Q x S ∂μ + (a + ∫⁻ x, β x ∂ν) := by ring

/-- **`m` steps of two close kernels**, from the same start. -/
theorem tvLe_iterate_of_close (Q P : Kernel Ω Ω) [IsMarkovKernel Q] [IsMarkovKernel P]
    {β : Ω → ℝ≥0∞} (hβ : Measurable β)
    (hclose : ∀ x S, MeasurableSet S → Q x S ≤ P x S + β x ∧ P x S ≤ Q x S + β x)
    (μ : Measure Ω) :
    ∀ m : ℕ, TVLe (iterate Q μ m) (iterate P μ m)
      (∑ j ∈ Finset.range m, ∫⁻ x, β x ∂(iterate P μ j))
  | 0 => by simp
  | m + 1 => by
      rw [Finset.sum_range_succ, iterate_succ, iterate_succ]
      exact tvLe_step_of_close Q P hclose (tvLe_iterate_of_close Q P hβ hclose μ m)

/-- A step of a Markov kernel preserves total mass. -/
theorem step_univ (P : Kernel Ω Ω) [IsMarkovKernel P] (μ : Measure Ω) :
    step P μ univ = μ univ := by
  rw [step_apply P μ MeasurableSet.univ]
  simp

theorem iterate_univ (P : Kernel Ω Ω) [IsMarkovKernel P] (μ : Measure Ω) :
    ∀ m : ℕ, iterate P μ m univ = μ univ
  | 0 => rfl
  | m + 1 => by rw [iterate_succ, step_univ, iterate_univ P μ m]

/-- A step is additive in the law. -/
theorem step_add (P : Kernel Ω Ω) (μ₁ μ₂ : Measure Ω) :
    step P (μ₁ + μ₂) = step P μ₁ + step P μ₂ := by
  ext S hS
  rw [Measure.add_apply, step_apply P _ hS, step_apply P _ hS, step_apply P _ hS,
    lintegral_add_measure]

theorem iterate_add_measure (P : Kernel Ω Ω) (μ₁ μ₂ : Measure Ω) :
    ∀ m : ℕ, iterate P (μ₁ + μ₂) m = iterate P μ₁ m + iterate P μ₂ m
  | 0 => rfl
  | m + 1 => by rw [iterate_succ, iterate_succ, iterate_succ, iterate_add_measure P μ₁ μ₂ m,
      step_add]

/-- **The exceptional-set split.**  If `σ` restricted off `S` is `M`-warm with respect to a
`P`-invariant `π`, the `Q`-chain and the `P`-chain from `σ` stay within
`m · M · ∫ β dπ + σ(S)` for `m` steps. -/
theorem tvLe_iterate_split (Q P : Kernel Ω Ω) [IsMarkovKernel Q] [IsMarkovKernel P]
    {β : Ω → ℝ≥0∞} (hβ : Measurable β)
    (hclose : ∀ x S, MeasurableSet S → Q x S ≤ P x S + β x ∧ P x S ≤ Q x S + β x)
    (σ : Measure Ω) {S : Set Ω} (hS : MeasurableSet S) {M : ℝ≥0∞} {π : Measure Ω}
    (hwarm : IsWarm M (σ.restrict Sᶜ) π) (hπ : Kernel.Invariant P π) (m : ℕ) :
    TVLe (iterate Q σ m) (iterate P σ m) (m * (M * ∫⁻ x, β x ∂π) + σ S) := by
  set σ₁ := σ.restrict Sᶜ
  set σ₂ := σ.restrict S
  have hsplit : σ = σ₁ + σ₂ := by rw [add_comm]; exact (Measure.restrict_add_restrict_compl hS).symm
  have hclose₁ := tvLe_iterate_of_close Q P hβ hclose σ₁ m
  have hsum : ∑ j ∈ Finset.range m, ∫⁻ x, β x ∂(iterate P σ₁ j) ≤ m * (M * ∫⁻ x, β x ∂π) := by
    calc ∑ j ∈ Finset.range m, ∫⁻ x, β x ∂(iterate P σ₁ j)
        ≤ ∑ _j ∈ Finset.range m, M * ∫⁻ x, β x ∂π := by
          refine Finset.sum_le_sum fun j _ => ?_
          have hle := (isWarm_iff_le_smul _ _).1 (isWarm_iterate_of_invariant hwarm hπ j)
          calc ∫⁻ x, β x ∂(iterate P σ₁ j) ≤ ∫⁻ x, β x ∂(M • π) := lintegral_mono' hle le_rfl
            _ = M * ∫⁻ x, β x ∂π := lintegral_smul_measure _ _
      _ = m * (M * ∫⁻ x, β x ∂π) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hmass : ∀ (R : Kernel Ω Ω) [IsMarkovKernel R] (A : Set Ω),
      iterate R σ₂ m A ≤ σ S := fun R _ A =>
    (measure_mono (subset_univ A)).trans
      (by rw [iterate_univ R σ₂ m, Measure.restrict_apply_univ])
  have hQσ : iterate Q σ m = iterate Q σ₁ m + iterate Q σ₂ m := by
    rw [hsplit, iterate_add_measure]
  have hPσ : iterate P σ m = iterate P σ₁ m + iterate P σ₂ m := by
    rw [hsplit, iterate_add_measure]
  intro A hA
  obtain ⟨h1, h2⟩ := hclose₁ A hA
  rw [hQσ, hPσ, Measure.add_apply, Measure.add_apply]
  constructor
  · calc iterate Q σ₁ m A + iterate Q σ₂ m A
        ≤ (iterate P σ₁ m A + m * (M * ∫⁻ x, β x ∂π)) + σ S :=
          add_le_add (h1.trans (add_le_add le_rfl hsum)) (hmass Q A)
      _ ≤ iterate P σ₁ m A + iterate P σ₂ m A + (m * (M * ∫⁻ x, β x ∂π) + σ S) := by
          rw [← add_assoc]; gcongr; exact le_self_add
  · calc iterate P σ₁ m A + iterate P σ₂ m A
        ≤ (iterate Q σ₁ m A + m * (M * ∫⁻ x, β x ∂π)) + σ S :=
          add_le_add (h2.trans (add_le_add le_rfl hsum)) (hmass P A)
      _ ≤ iterate Q σ₁ m A + iterate Q σ₂ m A + (m * (M * ∫⁻ x, β x ∂π) + σ S) := by
          rw [← add_assoc]; gcongr; exact le_self_add

end ArlibCommunity.Algorithms.HitAndRun
