import Auditable.Model.Prelude
import Mathlib.LinearAlgebra.Lagrange

/-!
# `H(n, m, n)` is `n`-wise independent

The family `CellHash K n` (coefficient vectors `c : Fin n → K`, hash
`y ↦ first m bits of ∑ⱼ cⱼ xʲ`, `x = bits⁻¹ y`) is `n`-wise independent in the sense
of prelim.tex:92-107: for every set `T` of at most `n` distinct inputs and every
cell `α ∈ {0,1}^m` (`m ≤ n`), exactly a `(2^{-m})^{|T|}` fraction of coefficient
vectors sends all of `T` to `α`.

Why: evaluation at the `|T| ≤ n` distinct nodes `bits⁻¹ y` is a surjective additive
map `K^n → K^T` (Lagrange interpolation), so its fibers all have
`|K|^n / |K|^{|T|}` elements; and the first-`m`-bits map `K → {0,1}^m` has fibers of
equal size `|K| / 2^m`.
-/

set_option autoImplicit false

open Finset

namespace Auditable.Analysis

/-- A map all of whose fibers have the same size has fibers of size `|X| / |Y|`.

INTERNAL: counting step of `cellHash_indep`. -/
theorem card_fiber_mul_of_eq {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X → Y)
    (h : ∀ y y', (univ.filter fun x => f x = y).card = (univ.filter fun x => f x = y').card)
    (y : Y) : (univ.filter fun x => f x = y).card * Fintype.card Y = Fintype.card X := by
  have := Finset.card_eq_sum_card_fiberwise (f := f) (s := (univ : Finset X)) (t := univ)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  rw [Finset.card_univ] at this
  rw [this, Finset.sum_congr rfl fun y' _ => h y' y]
  simp [mul_comm]

/-- A surjective additive map of finite groups has fibers of size `|G| / |H|`.

INTERNAL: counting step of `cellHash_indep`. -/
theorem card_fiber_addHom {G H : Type} [AddCommGroup G] [AddCommGroup H] [Fintype G]
    [Fintype H] [DecidableEq H] (E : G →+ H) (hE : Function.Surjective E) (b : H) :
    (univ.filter fun g => E g = b).card * Fintype.card H = Fintype.card G := by
  apply card_fiber_mul_of_eq
  intro y y'
  obtain ⟨g, rfl⟩ := hE y
  obtain ⟨g', rfl⟩ := hE y'
  refine Finset.card_bij' (fun x _ => x + (g' - g)) (fun x _ => x - (g' - g)) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rw [map_add, hx, map_sub]; abel
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rw [map_sub, hx, map_sub]; abel
  · intro x _; abel
  · intro x _; abel

/-- The first `m` output bits of a field element, as `CellHash.apply` reads them. -/
def cellTrunc {K : Type} {n : ℕ} (bits : K ≃ (Fin n → Bool)) (m : ℕ) (k : K) :
    Fin m → Bool :=
  fun i => if hi : (i : ℕ) < n then bits k ⟨i, hi⟩ else false

/-- Every cell of the first-`m`-bits map `K → {0,1}^m` (`m ≤ n`) has `|K| / 2^m`
elements.

INTERNAL: counting step of `cellHash_indep`. -/
theorem card_cellTrunc_fiber {K : Type} [Fintype K] {n : ℕ} (bits : K ≃ (Fin n → Bool))
    (m : ℕ) (hm : m ≤ n) (α : Fin m → Bool) :
    (univ.filter fun k : K => cellTrunc bits m k = α).card * 2 ^ m = Fintype.card K := by
  classical
  have h := card_fiber_mul_of_eq (cellTrunc bits m) ?_ α
  · simpa using h
  intro a a'
  -- flip the first `m` bits by `δ = a xor a'`
  let fl : (Fin n → Bool) → (Fin n → Bool) := fun w j =>
    if hj : (j : ℕ) < m then xor (w j) (xor (a ⟨j, hj⟩) (a' ⟨j, hj⟩)) else w j
  have hfl : ∀ w, fl (fl w) = w := by
    intro w; funext j; simp only [fl]; split_ifs <;> simp
  have htr : ∀ k i, cellTrunc bits m (bits.symm (fl (bits k))) i =
      xor (cellTrunc bits m k i) (xor (a i) (a' i)) := by
    intro k i
    have hi : (i : ℕ) < n := lt_of_lt_of_le i.2 hm
    simp [cellTrunc, hi, fl]
  refine Finset.card_bij' (fun k _ => bits.symm (fl (bits k)))
    (fun k _ => bits.symm (fl (bits k))) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [mem_filter, mem_univ, true_and] at hk ⊢
    funext i; rw [htr, hk]; cases a i <;> cases a' i <;> rfl
  · intro k hk
    simp only [mem_filter, mem_univ, true_and] at hk ⊢
    funext i; rw [htr, hk]; cases a i <;> cases a' i <;> rfl
  · intro k _; simp [hfl]
  · intro k _; simp [hfl]

/-- **`H(n, m, n)` is `n`-wise independent** (prelim.tex:92-107 with the
coefficient construction of prelim.tex:109-115): for `m ≤ n` and a set `T` of at most
`n` inputs, the coefficient vectors sending every `y ∈ T` to the cell `α` are a
`(2^{-m})^{|T|}` fraction of all of them.

INTERNAL: the paper asserts that the family is `n`-wise independent ("Then
`{γ_{y,α}}` are `n`-wise independent", bgp.tex:177) and that such a family is given by
coefficient tuples (prelim.tex:109-115, citing [BGP2000]); this is the fact for the
concrete family `CellHash` that the formalization fixes.
TEXLINE: bgp.tex:175-177 -/
theorem cellHash_indep {K : Type} [Field K] [Fintype K] {n : ℕ}
    (bits : K ≃ (Fin n → Bool)) (m : ℕ) (hm : m ≤ n) (α : Fin m → Bool)
    (T : Finset (Fin n → Bool)) (hT : T.card ≤ n) :
    (univ.filter fun c : CellHash K n => ∀ y ∈ T, CellHash.apply bits c m y = α).card *
        (2 ^ m) ^ T.card = Fintype.card (CellHash K n) := by
  classical
  -- evaluation at the nodes `bits⁻¹ y`, `y ∈ T`
  let E : CellHash K n →+ ({y // y ∈ T} → K) :=
    { toFun := fun c y => ∑ j : Fin n, c j * (bits.symm y.1) ^ (j : ℕ)
      map_zero' := by funext y; simp
      map_add' := by intro c d; funext y; simp [add_mul, Finset.sum_add_distrib] }
  have hE : Function.Surjective E := by
    intro r
    let P := Lagrange.interpolate T (fun y => bits.symm y)
      (fun y => if h : y ∈ T then r ⟨y, h⟩ else 0)
    have hinj : Set.InjOn (fun y => bits.symm y) (T : Set (Fin n → Bool)) :=
      fun a _ b _ h => bits.symm.injective h
    have hdeg : P.natDegree < n ∨ T = ∅ := by
      by_cases hT0 : T = ∅
      · exact Or.inr hT0
      left
      have hlt : P.degree < T.card := Lagrange.degree_interpolate_lt _ hinj
      have hpos : 0 < T.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hT0)
      by_cases hP : P = 0
      · rw [hP]; simp; omega
      · have := (Polynomial.natDegree_lt_iff_degree_lt hP).2 hlt
        omega
    refine ⟨fun j => P.coeff j, ?_⟩
    funext y
    rcases hdeg with hdeg | hT0
    · show ∑ j : Fin n, P.coeff j * (bits.symm y.1) ^ (j : ℕ) = r y
      rw [Fin.sum_univ_eq_sum_range (fun j => P.coeff j * (bits.symm y.1) ^ j) n,
        ← Polynomial.eval_eq_sum_range' hdeg]
      have := Lagrange.eval_interpolate_at_node
        (fun y => if h : y ∈ T then r ⟨y, h⟩ else 0) hinj y.2
      simpa [P] using this
    · exact absurd y.2 (by simp [hT0])
  -- the cells of the first-`m`-bits map
  let S : Finset K := univ.filter fun k => cellTrunc bits m k = α
  let B : Finset ({y // y ∈ T} → K) := Fintype.piFinset fun _ => S
  have hset : (univ.filter fun c : CellHash K n => ∀ y ∈ T, CellHash.apply bits c m y = α) =
      univ.filter fun c => E c ∈ B := by
    ext c
    simp only [mem_filter, mem_univ, true_and, B, Fintype.mem_piFinset, S]
    constructor
    · intro h y; exact h y.1 y.2
    · intro h y hy; exact h ⟨y, hy⟩
  have hsum := Finset.card_eq_sum_card_fiberwise (f := E)
    (s := univ.filter fun c => E c ∈ B) (t := B)
    (fun c hc => by simpa using hc)
  have hfib : ∀ b ∈ B, ((univ.filter fun c => E c ∈ B).filter fun c => E c = b).card =
      (univ.filter fun c => E c = (0 : {y // y ∈ T} → K)).card := by
    intro b hb
    rw [Finset.filter_filter]
    have h1 : (univ.filter fun c => E c ∈ B ∧ E c = b) = univ.filter fun c => E c = b := by
      ext c; simp only [mem_filter, mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨h ▸ hb, h⟩
    rw [h1]
    have h2 := card_fiber_addHom E hE b
    have h3 := card_fiber_addHom E hE 0
    have hpos : 0 < Fintype.card ({y // y ∈ T} → K) := Fintype.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (h2.trans h3.symm)
  rw [hset, hsum, Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]
  have hB : B.card = S.card ^ T.card := by
    simp [B, Fintype.card_piFinset]
  have hS := card_cellTrunc_fiber bits m hm α
  have h0 := card_fiber_addHom E hE 0
  rw [hB, ← h0]
  have hK : Fintype.card ({y // y ∈ T} → K) = Fintype.card K ^ T.card := by simp
  rw [hK, ← hS, mul_pow]
  ring

end Auditable.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `cellHash_indep` via Lagrange surjectivity of evaluation and equal fibers
-/
