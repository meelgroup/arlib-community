import Auditable.Analysis.AffHashCollision

/-!
# lm:stockexist — few solutions can be isolated by `m` affine hashes

If `2 · |sol G| ≤ 2^m`, there are `m` affine hashes `{0,1}^N → {0,1}^m` such that every
solution of `G` is alone in its cell under one of them (`stockWith G m`).

The paper (stock.tex:35-80) argues with random hashes: a fixed solution `z₁` shares
its cell under one random hash with probability at most `(|sol G| − 1) / 2^m`, so with
`m` independent hashes it is isolated by none with probability at most that to the
`m`-th power, and a union bound over `z₁` finishes. Here the same argument is a count
over all `m`-tuples of matrices (the offsets are `0`), using the pairwise collision
count `collision_card_le`. The hypothesis is `|sol G| ≤ 2^{m-1}`, weaker than the
paper's `|sol G| ≤ 2^{m-2}`, and it needs no `2 ≤ m` side condition.
-/

set_option autoImplicit false

namespace Auditable.Analysis

open Auditable

/-- INTERNAL: the numeric heart of the union bound: `S (S − 1)^m < 2^{m·m}` when
`2 S ≤ 2^m`.
TEXLINE: stock.tex:35-80 -/
theorem stock_union_numeric (S m : ℕ) (hS : 2 * S ≤ 2 ^ m) : S * (S - 1) ^ m < 2 ^ (m * m) := by
  rcases Nat.eq_zero_or_pos S with h0 | hpos
  · subst h0; simp
  rcases m with _ | k
  · simp at hS; omega
  have hSk : S ≤ 2 ^ k := by rw [pow_succ] at hS; omega
  have hlt : S - 1 < 2 ^ k := by omega
  calc S * (S - 1) ^ (k + 1) < 2 ^ k * (2 ^ k) ^ (k + 1) := by
        apply Nat.mul_lt_mul_of_le_of_lt hSk (Nat.pow_lt_pow_left hlt (Nat.succ_ne_zero k))
        positivity
    _ = 2 ^ (k + k * (k + 1)) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ ((k + 1) * (k + 1)) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

/-- INTERNAL: **lm:stockexist, counting form.** If `2 · |sol G| ≤ 2^m` then some `m`
affine hashes into `{0,1}^m` isolate every solution of `G` (isolation semantics).
TEXLINE: stock.tex:35-80 -/
theorem stock_exist {N : ℕ} (G : CNF N) (m : ℕ) (hS : 2 * solCount G ≤ 2 ^ m) :
    ∃ hs : Fin m → AffHash N m, stockWith G m hs := by
  classical
  set S := sol G with hSdef
  -- the matrices under which `z₁` is not isolated
  let bad : (Fin N → Bool) → Finset (Fin m → Fin N → Bool) := fun z₁ =>
    Finset.univ.filter fun A => ∃ z₂ ∈ S, z₂ ≠ z₁ ∧ ∀ i, rowParity (A i) z₂ = rowParity (A i) z₁
  have hbad : ∀ z₁ ∈ S, 2 ^ m * (bad z₁).card ≤ (S.card - 1) * (2 ^ N) ^ m := by
    intro z₁ hz₁
    have hsub : bad z₁ ⊆ (S.erase z₁).biUnion fun z₂ =>
        Finset.univ.filter fun A : Fin m → Fin N → Bool =>
          ∀ i, rowParity (A i) z₂ = rowParity (A i) z₁ := by
      intro A hA
      simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hA
      obtain ⟨z₂, hz₂, hne, hcol⟩ := hA
      simp only [Finset.mem_biUnion, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact ⟨z₂, ⟨hne, hz₂⟩, hcol⟩
    calc 2 ^ m * (bad z₁).card
        ≤ 2 ^ m * ∑ z₂ ∈ S.erase z₁, (Finset.univ.filter fun A : Fin m → Fin N → Bool =>
            ∀ i, rowParity (A i) z₂ = rowParity (A i) z₁).card :=
          Nat.mul_le_mul_left _ ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)
      _ = ∑ z₂ ∈ S.erase z₁, 2 ^ m * (Finset.univ.filter fun A : Fin m → Fin N → Bool =>
            ∀ i, rowParity (A i) z₂ = rowParity (A i) z₁).card := Finset.mul_sum _ _ _
      _ ≤ ∑ _z₂ ∈ S.erase z₁, (2 ^ N) ^ m := by
          apply Finset.sum_le_sum
          intro z₂ hz₂
          exact collision_card_le (Finset.ne_of_mem_erase hz₂)
      _ = (S.card - 1) * (2 ^ N) ^ m := by
          rw [Finset.sum_const, Finset.card_erase_of_mem hz₁, smul_eq_mul]
  -- tuples of matrices under which some solution is isolated by none of them
  let B : Finset (Fin m → Fin m → Fin N → Bool) :=
    S.biUnion fun z₁ => Fintype.piFinset fun _ : Fin m => bad z₁
  have hBcard : 2 ^ (m * m) * B.card ≤ S.card * (S.card - 1) ^ m * ((2 ^ N) ^ m) ^ m := by
    calc 2 ^ (m * m) * B.card ≤ 2 ^ (m * m) * ∑ z₁ ∈ S, (bad z₁).card ^ m := by
          apply Nat.mul_le_mul_left
          refine Finset.card_biUnion_le.trans (le_of_eq ?_)
          refine Finset.sum_congr rfl fun z₁ _ => ?_
          exact Fintype.card_piFinset_const _ _
      _ = ∑ z₁ ∈ S, (2 ^ m * (bad z₁).card) ^ m := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun z₁ _ => ?_
          rw [mul_pow, ← pow_mul]
      _ ≤ ∑ _z₁ ∈ S, ((S.card - 1) * (2 ^ N) ^ m) ^ m :=
          Finset.sum_le_sum fun z₁ hz₁ => Nat.pow_le_pow_left (hbad z₁ hz₁) m
      _ = S.card * (S.card - 1) ^ m * ((2 ^ N) ^ m) ^ m := by
          rw [Finset.sum_const, smul_eq_mul, mul_pow, mul_assoc]
  have huniv : (Finset.univ : Finset (Fin m → Fin m → Fin N → Bool)).card = ((2 ^ N) ^ m) ^ m := by
    simp
  have hlt : B.card < (Finset.univ : Finset (Fin m → Fin m → Fin N → Bool)).card := by
    rw [huniv]
    have hnum := stock_union_numeric S.card m hS
    have hpos : 0 < ((2 ^ N) ^ m) ^ m := by positivity
    by_contra hge
    push Not at hge
    have : 2 ^ (m * m) * ((2 ^ N) ^ m) ^ m ≤ S.card * (S.card - 1) ^ m * ((2 ^ N) ^ m) ^ m :=
      (Nat.mul_le_mul_left _ hge).trans hBcard
    have := Nat.le_of_mul_le_mul_right this hpos
    omega
  obtain ⟨T, -, hT⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨fun i => ⟨T i, fun _ => false⟩, ?_⟩
  intro z₁ hz₁
  have hz₁S : z₁ ∈ S := by simp [hSdef, sol, hz₁]
  have hnot : T ∉ Fintype.piFinset fun _ : Fin m => bad z₁ := by
    intro hmem
    exact hT (Finset.mem_biUnion.mpr ⟨z₁, hz₁S, hmem⟩)
  rw [Fintype.mem_piFinset] at hnot
  push Not at hnot
  obtain ⟨i, hi⟩ := hnot
  refine ⟨i, fun z₂ hz₂ hne hcol => hi ?_⟩
  simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨z₂, by simp [hSdef, sol, hz₂], hne, ?_⟩
  exact (AffHash.apply_eq_iff _ z₂ z₁).mp hcol

end Auditable.Analysis
