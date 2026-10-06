import Auditable.Analysis.AffHashCollision
import Mathlib.Algebra.Order.Chebyshev

/-!
# lm:holesexist — many solutions hit every cell under `m + 1` affine hashes

If `2^m ≤ |sol G|`, there are `m + 1` affine hashes `{0,1}^N → {0,1}^m` under which
every cell `α ∈ {0,1}^m` holds a solution of `G` for one of them (`holesWith G m`).

The paper (combined.tex:74-113) uses `m + 1` independent random hashes and a
second-moment bound per cell. Here the argument is a count, in three steps, all with
the same matrix `A` and `m + 1` different offsets:

1. some matrix `A` has few collisions on `sol G`: the average over all matrices of the
   number of ordered colliding pairs is at most `|sol G| + |sol G|² / 2^m`
   (`collision_card_le`);
2. so its image `A(sol G)` covers at least half of `{0,1}^m` (Cauchy–Schwarz,
   `sq_sum_le_card_mul_sum_sq`);
3. and `m + 1` translates of a set of at least half the cells cover all `2^m` of them
   for some choice of offsets (a union bound over cells, counted over all offset tuples).

The hypothesis `2^m ≤ |sol G|` is weaker than the paper's `2^{m+3} ≤ |sol G|`.
-/

set_option autoImplicit false

namespace Auditable.Analysis

open Auditable

/-- INTERNAL: the numeric step from the collision bound to "the image covers half":
if `x C ≤ s (x + s − 1)`, `s² ≤ I C` and `1 ≤ x ≤ s`, then `x ≤ 2 I`.
TEXLINE: combined.tex:74-113 -/
theorem holes_image_numeric (x s I C : ℕ) (hx : 1 ≤ x) (hxs : x ≤ s)
    (hC : x * C ≤ s * (x + s - 1)) (hCS : s ^ 2 ≤ I * C) : x ≤ 2 * I := by
  by_contra hlt
  push Not at hlt
  have hs : 1 ≤ s := hx.trans hxs
  -- `s² x ≤ I x C ≤ I s (x + s − 1)`, so `s x ≤ I (x + s − 1)`
  have h1 : s ^ 2 * x ≤ I * (s * (x + s - 1)) := by
    calc s ^ 2 * x ≤ I * C * x := Nat.mul_le_mul_right _ hCS
      _ = I * (x * C) := by ring
      _ ≤ I * (s * (x + s - 1)) := Nat.mul_le_mul_left _ hC
  have h2 : s * x ≤ I * (x + s - 1) := by
    have : s * (s * x) ≤ s * (I * (x + s - 1)) := by
      calc s * (s * x) = s ^ 2 * x := by ring
        _ ≤ I * (s * (x + s - 1)) := h1
        _ = s * (I * (x + s - 1)) := by ring
    exact Nat.le_of_mul_le_mul_left this hs
  obtain ⟨d, rfl⟩ : ∃ d, s = x + d := ⟨s - x, by omega⟩
  have hsub : x + (x + d) - 1 = (x - 1) + (x + d) := by omega
  rw [hsub] at h2
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h2
  nlinarith

/-- INTERNAL: the linear part `z ↦ A z` of an affine hash, as a bit vector.
TEXLINE: prelim.tex:82-118 -/
def linApply {N m : ℕ} (A : Fin m → Fin N → Bool) (z : Fin N → Bool) : Fin m → Bool :=
  fun i => rowParity (A i) z

/-- INTERNAL: **lm:holesexist, counting form.** If `2^m ≤ |sol G|` then some `m + 1`
affine hashes into `{0,1}^m` hit every cell with a solution of `G`.
TEXLINE: combined.tex:74-113 -/
theorem holes_exist {N : ℕ} (G : CNF N) (m : ℕ) (hS : 2 ^ m ≤ solCount G) :
    ∃ hs : Fin (m + 1) → AffHash N m, holesWith G m hs := by
  classical
  set S := sol G with hSdef
  have hSc : S.card = solCount G := rfl
  set s := S.card
  set x := 2 ^ m with hxdef
  have hx1 : 1 ≤ x := Nat.one_le_two_pow
  have hxs : x ≤ s := by rw [hSc]; exact hS
  set T := (2 ^ N) ^ m with hTdef
  -- number of ordered pairs of solutions that `A` sends to the same cell
  let coll : (Fin m → Fin N → Bool) → ℕ := fun A =>
    ∑ z₁ ∈ S, (S.filter fun z₂ => linApply A z₂ = linApply A z₁).card
  -- step 1: some matrix has few collisions
  have hpair : ∀ z₁ z₂ : Fin N → Bool,
      x * (Finset.univ.filter fun A : Fin m → Fin N → Bool =>
        linApply A z₂ = linApply A z₁).card ≤ (if z₂ = z₁ then x * T else T) := by
    intro z₁ z₂
    split_ifs with h
    · subst h
      apply Nat.mul_le_mul_left
      refine (Finset.card_filter_le _ _).trans (le_of_eq ?_)
      simp [hTdef]
    · have := collision_card_le (m := m) h
      simpa [linApply, funext_iff] using this
  have hsum : ∑ A : Fin m → Fin N → Bool, x * coll A ≤ ∑ _A : Fin m → Fin N → Bool, s * (x + s - 1) := by
    have hswap : ∑ A : Fin m → Fin N → Bool, x * coll A =
        ∑ z₁ ∈ S, ∑ z₂ ∈ S, x * (Finset.univ.filter fun A : Fin m → Fin N → Bool =>
          linApply A z₂ = linApply A z₁).card := by
      simp only [coll, Finset.mul_sum, Finset.card_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun z₁ _ => ?_
      rw [Finset.sum_comm]
    rw [hswap, Finset.sum_const, Finset.card_univ]
    have hinner : ∀ z₁ ∈ S, ∑ z₂ ∈ S, x * (Finset.univ.filter fun A : Fin m → Fin N → Bool =>
        linApply A z₂ = linApply A z₁).card ≤ x * T + (s - 1) * T := by
      intro z₁ hz₁
      rw [← Finset.add_sum_erase S _ hz₁]
      refine Nat.add_le_add ?_ ?_
      · simpa using hpair z₁ z₁
      · calc ∑ z₂ ∈ S.erase z₁, x * (Finset.univ.filter fun A : Fin m → Fin N → Bool =>
              linApply A z₂ = linApply A z₁).card ≤ ∑ _z₂ ∈ S.erase z₁, T := by
              refine Finset.sum_le_sum fun z₂ hz₂ => ?_
              have := hpair z₁ z₂
              rwa [if_neg (Finset.ne_of_mem_erase hz₂)] at this
          _ = (s - 1) * T := by rw [Finset.sum_const, Finset.card_erase_of_mem hz₁, smul_eq_mul]
    calc ∑ z₁ ∈ S, ∑ z₂ ∈ S, x * (Finset.univ.filter fun A : Fin m → Fin N → Bool =>
          linApply A z₂ = linApply A z₁).card ≤ ∑ _z₁ ∈ S, (x * T + (s - 1) * T) :=
          Finset.sum_le_sum hinner
      _ = s * (x * T + (s - 1) * T) := by rw [Finset.sum_const, smul_eq_mul]
      _ = Fintype.card (Fin m → Fin N → Bool) • (s * (x + s - 1)) := by
          rw [smul_eq_mul]
          have hcard : Fintype.card (Fin m → Fin N → Bool) = T := by simp [hTdef]
          rw [hcard]
          have : x + s - 1 = x + (s - 1) := by omega
          rw [this]; ring
  obtain ⟨A, -, hA⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  -- step 2: the image of `sol G` under `A` covers at least half of the cells
  set I := S.image (linApply A) with hIdef
  have hcollI : coll A = ∑ t ∈ I, (S.filter fun z => linApply A z = t).card ^ 2 := by
    have := Finset.sum_comp (s := S) (fun t => (S.filter fun z => linApply A z = t).card)
      (linApply A)
    simp only [coll, smul_eq_mul] at this ⊢
    rw [this]
    refine Finset.sum_congr rfl fun t _ => by ring
  have hsI : s = ∑ t ∈ I, (S.filter fun z => linApply A z = t).card :=
    Finset.card_eq_sum_card_image _ _
  have hCS : s ^ 2 ≤ I.card * coll A := by
    rw [hcollI]
    conv_lhs => rw [hsI]
    exact sq_sum_le_card_mul_sum_sq
  have hhalf : x ≤ 2 * I.card := holes_image_numeric x s I.card (coll A) hx1 hxs hA hCS
  -- step 3: `m + 1` translates of `I` cover every cell, for some offsets
  let shift : (Fin m → Bool) → (Fin m → Bool) → (Fin m → Bool) := fun α c i => xor (α i) (c i)
  have hshift_invol : ∀ α c, shift α (shift α c) = c := by
    intro α c; funext i; simp [shift]
  have hgood : ∀ α : Fin m → Bool,
      (Finset.univ.filter fun c : Fin m → Bool => shift α c ∈ I).card = I.card := by
    intro α
    have : (Finset.univ.filter fun c : Fin m → Bool => shift α c ∈ I) = I.image (shift α) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro h; exact ⟨shift α c, h, hshift_invol α c⟩
      · rintro ⟨t, ht, rfl⟩; rwa [hshift_invol]
    rw [this, Finset.card_image_of_injective]
    intro c c' h
    simpa [hshift_invol] using congrArg (shift α) h
  have hbadcell : ∀ α : Fin m → Bool,
      (Finset.univ.filter fun c : Fin m → Bool => shift α c ∉ I).card = x - I.card := by
    intro α
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun c : Fin m → Bool => shift α c ∈ I)
    rw [hgood α, Finset.card_univ] at h
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
    omega
  let B : Finset (Fin (m + 1) → Fin m → Bool) :=
    Finset.univ.biUnion fun α : Fin m → Bool =>
      Fintype.piFinset fun _ : Fin (m + 1) => Finset.univ.filter fun c => shift α c ∉ I
  have hBcard : B.card ≤ x * (x - I.card) ^ (m + 1) := by
    refine Finset.card_biUnion_le.trans (le_of_eq ?_)
    rw [Finset.sum_congr rfl fun α _ => by rw [Fintype.card_piFinset_const, hbadcell α]]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    simp [hxdef]
  have hlt : B.card < (Finset.univ : Finset (Fin (m + 1) → Fin m → Bool)).card := by
    have huniv : (Finset.univ : Finset (Fin (m + 1) → Fin m → Bool)).card = x ^ (m + 1) := by
      simp [hxdef]
    rw [huniv]
    have h2 : (2 * (x - I.card)) ^ (m + 1) ≤ x ^ (m + 1) :=
      Nat.pow_le_pow_left (by omega) _
    have h3 : 2 ^ (m + 1) * B.card ≤ x * x ^ (m + 1) := by
      calc 2 ^ (m + 1) * B.card ≤ 2 ^ (m + 1) * (x * (x - I.card) ^ (m + 1)) :=
            Nat.mul_le_mul_left _ hBcard
        _ = x * (2 * (x - I.card)) ^ (m + 1) := by rw [mul_pow]; ring
        _ ≤ x * x ^ (m + 1) := Nat.mul_le_mul_left _ h2
    have h4 : x < 2 ^ (m + 1) := by rw [hxdef, pow_succ]; omega
    by_contra hge
    push Not at hge
    have : 2 ^ (m + 1) * x ^ (m + 1) ≤ x * x ^ (m + 1) :=
      (Nat.mul_le_mul_left _ hge).trans h3
    have hpos : 0 < x ^ (m + 1) := by positivity
    have := Nat.le_of_mul_le_mul_right this hpos
    omega
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨fun i => ⟨A, c i⟩, ?_⟩
  intro α
  have hnot : c ∉ Fintype.piFinset fun _ : Fin (m + 1) =>
      Finset.univ.filter fun c => shift α c ∉ I := by
    intro hmem
    exact hc (Finset.mem_biUnion.mpr ⟨α, Finset.mem_univ _, hmem⟩)
  rw [Fintype.mem_piFinset] at hnot
  push Not at hnot
  obtain ⟨i, hi⟩ := hnot
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
  rw [hIdef, Finset.mem_image] at hi
  obtain ⟨z, hz, hzα⟩ := hi
  refine ⟨z, by simpa [hSdef, sol] using hz, i, ?_⟩
  rw [AffHash.apply_eq]
  funext j
  have := congrFun hzα j
  simp only [linApply, shift] at this
  simp only [this]
  cases α j <;> cases c i j <;> rfl

end Auditable.Analysis
