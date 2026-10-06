import Auditable.Model.Prelude
import Mathlib.Data.Fintype.BigOperators

/-!
# Collisions of the affine GF(2) hash family

The one probabilistic fact about `AffHash` that the existence lemmas
(lm:holesexist, lm:stockexist) use, stated as a count: for two distinct points
`z₁ ≠ z₂ ∈ {0,1}^N`, at most a `2^{-m}` fraction of the matrices
`A : {0,1}^N → {0,1}^m` send them to the same cell (`collision_card_le`). The offset
`b` cancels from a collision (`AffHash.apply_eq_iff`), so collisions depend on `A`
only.

The count goes through the parity `xorFold` that `AffHash.apply` computes, its
linearity in the row, and the involution that toggles one coordinate of a row.
-/

set_option autoImplicit false

namespace Auditable.Analysis

open Auditable

/-- INTERNAL: the running xor `a ⊕ f(j₁) ⊕ … ⊕ f(jₖ)` over a list, written exactly as
`AffHash.apply` folds it.
TEXLINE: prelim.tex:82-118 -/
def xorFold {N : ℕ} (a : Bool) (l : List (Fin N)) (f : Fin N → Bool) : Bool :=
  l.foldl (fun acc j => xor acc (f j)) a

/-- INTERNAL: the initial value of `xorFold` factors out.
TEXLINE: prelim.tex:82-118 -/
theorem xorFold_init {N : ℕ} (a : Bool) (l : List (Fin N)) (f : Fin N → Bool) :
    xorFold a l f = xor a (xorFold false l f) := by
  induction l generalizing a with
  | nil => simp [xorFold]
  | cons j l ih =>
    simp only [xorFold, List.foldl_cons] at ih ⊢
    rw [ih, ih (xor false (f j))]
    simp

/-- INTERNAL: `xorFold` is additive in the summand.
TEXLINE: prelim.tex:82-118 -/
theorem xorFold_xor {N : ℕ} (l : List (Fin N)) (f g : Fin N → Bool) :
    xorFold false l (fun j => xor (f j) (g j)) = xor (xorFold false l f) (xorFold false l g) := by
  induction l with
  | nil => simp [xorFold]
  | cons j l ih =>
    have h1 := xorFold_init (xor false (xor (f j) (g j))) l (fun j => xor (f j) (g j))
    have h2 := xorFold_init (xor false (f j)) l f
    have h3 := xorFold_init (xor false (g j)) l g
    simp only [xorFold, List.foldl_cons] at h1 h2 h3 ih ⊢
    rw [h1, h2, h3, ih]
    simp only [Bool.false_xor]
    cases f j <;> cases g j <;> simp [Bool.xor_comm]

/-- INTERNAL: on a duplicate-free list, the xor of a summand supported at `j₀` is its
value at `j₀` if `j₀` occurs, and `false` otherwise.
TEXLINE: prelim.tex:82-118 -/
theorem xorFold_single {N : ℕ} (l : List (Fin N)) (hl : l.Nodup) (j₀ : Fin N) (c : Bool) :
    xorFold false l (fun j => if j = j₀ then c else false) = if j₀ ∈ l then c else false := by
  induction l with
  | nil => simp [xorFold]
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    have h := xorFold_init (xor false (if a = j₀ then c else false)) l
      (fun j => if j = j₀ then c else false)
    simp only [xorFold, List.foldl_cons] at h ih ⊢
    rw [h, ih hl.2]
    by_cases ha : a = j₀
    · subst ha; simp [hl.1]
    · simp [ha, Ne.symm ha]

/-- INTERNAL: one output bit of `z ↦ A z` (the linear part of an affine hash):
`⨁ⱼ (r j ∧ z j)` for the row `r`.
TEXLINE: prelim.tex:82-118 -/
def rowParity {N : ℕ} (r z : Fin N → Bool) : Bool :=
  xorFold false (List.finRange N) fun j => r j && z j

/-- INTERNAL: `AffHash.apply` is the offset xor the row parities.
TEXLINE: prelim.tex:82-118 -/
theorem AffHash.apply_eq {N m : ℕ} (h : AffHash N m) (z : Fin N → Bool) :
    h.apply z = fun i => xor (h.b i) (rowParity (h.A i) z) := rfl

/-- INTERNAL: two points collide under an affine hash iff every row has equal parity on
them; the offset `b` cancels.
TEXLINE: prelim.tex:82-118 -/
theorem AffHash.apply_eq_iff {N m : ℕ} (h : AffHash N m) (z₁ z₂ : Fin N → Bool) :
    h.apply z₁ = h.apply z₂ ↔ ∀ i, rowParity (h.A i) z₁ = rowParity (h.A i) z₂ := by
  rw [AffHash.apply_eq, AffHash.apply_eq, funext_iff]
  refine forall_congr' fun i => ?_
  cases h.b i <;> simp

/-- INTERNAL: toggling coordinate `j₀` of the row flips its parity on `z` by `z j₀`.
TEXLINE: prelim.tex:82-118 -/
theorem rowParity_toggle {N : ℕ} (r z : Fin N → Bool) (j₀ : Fin N) :
    rowParity (Function.update r j₀ (!r j₀)) z = xor (rowParity r z) (z j₀) := by
  have hfun : (fun j => Function.update r j₀ (!r j₀) j && z j) =
      fun j => xor (r j && z j) (if j = j₀ then z j₀ else false) := by
    funext j
    by_cases hj : j = j₀
    · subst hj; cases r j <;> cases z j <;> simp
    · simp [hj]
  unfold rowParity
  rw [hfun, xorFold_xor, xorFold_single _ (List.nodup_finRange N)]
  simp

/-- INTERNAL: for `z₁ ≠ z₂`, at most half of all rows have equal parity on them.
TEXLINE: prelim.tex:82-118 -/
theorem row_collision_card_le {N : ℕ} {z₁ z₂ : Fin N → Bool} (hz : z₁ ≠ z₂) :
    2 * (Finset.univ.filter fun r : Fin N → Bool => rowParity r z₁ = rowParity r z₂).card ≤
      2 ^ N := by
  obtain ⟨j₀, hj₀⟩ : ∃ j, z₁ j ≠ z₂ j := by
    by_contra h
    push Not at h
    exact hz (funext h)
  set R := Finset.univ.filter fun r : Fin N → Bool => rowParity r z₁ = rowParity r z₂
  set R' := Finset.univ.filter fun r : Fin N → Bool => ¬ rowParity r z₁ = rowParity r z₂
  have hsplit : R.card + R'.card = 2 ^ N := by
    rw [Finset.card_filter_add_card_filter_not]
    simp
  have hle : R.card ≤ R'.card := by
    refine Finset.card_le_card_of_injOn (fun r => Function.update r j₀ (!r j₀)) ?_ ?_
    · intro r hr
      simp only [R, R', Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hr ⊢
      rw [rowParity_toggle, rowParity_toggle, hr]
      cases rowParity r z₂ <;> cases h1 : z₁ j₀ <;> cases h2 : z₂ j₀ <;> simp_all
    · intro r _ r' _ h
      funext j
      by_cases hj : j = j₀
      · subst hj
        have := congrFun h j
        simpa using this
      · have := congrFun h j
        simpa [Function.update_of_ne hj] using this
  omega

/-- INTERNAL: **pairwise collision count of the affine family.** For `z₁ ≠ z₂`, at most
`2^{N m} / 2^m` matrices `A : {0,1}^N → {0,1}^m` give them equal parities in every row
(equivalently, `⟨A, b⟩.apply z₁ = ⟨A, b⟩.apply z₂` for any offset `b`).
TEXLINE: prelim.tex:82-118 -/
theorem collision_card_le {N m : ℕ} {z₁ z₂ : Fin N → Bool} (hz : z₁ ≠ z₂) :
    2 ^ m * (Finset.univ.filter fun A : Fin m → Fin N → Bool =>
      ∀ i, rowParity (A i) z₁ = rowParity (A i) z₂).card ≤ (2 ^ N) ^ m := by
  have heq : (Finset.univ.filter fun A : Fin m → Fin N → Bool =>
      ∀ i, rowParity (A i) z₁ = rowParity (A i) z₂) =
      Fintype.piFinset fun _ : Fin m =>
        Finset.univ.filter fun r : Fin N → Bool => rowParity r z₁ = rowParity r z₂ := by
    ext A; simp
  rw [heq, Fintype.card_piFinset_const, ← mul_pow]
  exact Nat.pow_le_pow_left (row_collision_card_le hz) m

end Auditable.Analysis
