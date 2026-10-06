import Formalization3sum.Meta.ModelClosure
import Formalization3sum.Model.Prior
import Formalization3sum.Model.Program
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Formalization3sum.Interface.Encoding
import Formalization3sum.Interface.Pseudocode
import Formalization3sum.Interface.ProgramModel

/-- INTERNAL: bounds partial sums of polynomially bounded integer matrix entries. -/
theorem Formalization3sum.Analysis.formalization3sum_word_magnitude_proof (hprior : Formalization3sum.Prior) : ∀ B : ℕ, ∃ C : ℕ, ∀ (N D : ℕ) (a : Formalization3sum.Model.Input N D), 0 < N → 0 < D → D ≤ N → Formalization3sum.Model.magnitudeBound B a → ∀ (p : Fin N × Fin N) (s : Finset (Fin D)), Int.natAbs (∑ k ∈ s, a.X p.1 k * a.Y k p.2) ≤ 2 ^ (C * (Nat.log2 (N + 1) + 1)) := by
  cases hprior
  intro B
  refine ⟨B + B + 1, ?_⟩
  intro N D a hN hD hDN hmag p s
  have hcard : s.card ≤ N := by
    calc
      s.card ≤ Fintype.card (Fin D) := Finset.card_le_univ s
      _ = D := Fintype.card_fin D
      _ ≤ N := hDN
  have hterm (k : Fin D) : (a.X p.1 k * a.Y k p.2).natAbs ≤ N ^ (B + B) := by
    rw [Int.natAbs_mul, pow_add]
    exact Nat.mul_le_mul (hmag.1 p.1 k) (hmag.2 k p.2)
  have hsum : (∑ k ∈ s, a.X p.1 k * a.Y k p.2).natAbs ≤ N ^ (B + B + 1) := by
    calc
      (∑ k ∈ s, a.X p.1 k * a.Y k p.2).natAbs
          ≤ ∑ k ∈ s, (a.X p.1 k * a.Y k p.2).natAbs :=
            Int.natAbs_sum_le s _
      _ ≤ ∑ _k ∈ s, N ^ (B + B) :=
        Finset.sum_le_sum (fun k _ => hterm k)
      _ = s.card * N ^ (B + B) := by simp
      _ ≤ N * N ^ (B + B) := Nat.mul_le_mul_right _ hcard
      _ = N ^ (B + B + 1) := by rw [pow_succ, mul_comm]
  have hlog : N ≤ 2 ^ (Nat.log2 (N + 1) + 1) := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by omega) (N + 1)
    rw [← Nat.log2_eq_log_two] at h
    omega
  calc
    (∑ k ∈ s, a.X p.1 k * a.Y k p.2).natAbs ≤ N ^ (B + B + 1) := hsum
    _ ≤ (2 ^ (Nat.log2 (N + 1) + 1)) ^ (B + B + 1) :=
      Nat.pow_le_pow_left hlog _
    _ = 2 ^ ((B + B + 1) * (Nat.log2 (N + 1) + 1)) := by rw [← pow_mul, mul_comm]

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · bounded each product, summed over at most `N` indices, and used the base-two logarithm bound.
-/
