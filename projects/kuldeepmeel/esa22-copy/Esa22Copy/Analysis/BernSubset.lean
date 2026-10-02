import Esa22Copy.Analysis.Alg2

/-!
# Bernoulli subsets: `bs d X` keeps each element of `X` independently w.p. `2^{-d}`

The law the analysis compares everything against.  `bs d X` is given by its
mass `bsMass r X U = [U ⊆ X] · r^{|U|} · (1-r)^{|X|-|U|}` with `r = 2^{-d}`.

* `bs_bind_yStep_eq` — the one-arrival identity: picking `a` back into
  `X \ {a}` with probability `2^{-q}` and then thinning by `2^{-d}` has the same
  law as thinning `X` by `2^{-d}` and then running one arrival of Algorithm 3's
  `Y_{q+d}`.  With `q = 0` it is Claim cl:loop's induction step
  (`yLaw_eq_bs`); with `d = 1` it is the step of the domination argument.
* `throwLaw_eq_bs` — line 6's thinning pass (a uniform subset of heads) is
  `bs 1`.
-/

set_option autoImplicit false

noncomputable section

namespace Esa22Copy.Analysis.Alg2

open Esa22Copy.Interface.Pseudocode

variable {n : ℕ}

/-- The mass of the Bernoulli(`r`) subset of `X` at `U`.
INTERNAL: the product law of Claim cl:loop, written out. -/
def bsMass (r : ℝ) (X U : Finset (Fin n)) : ℝ :=
  if U ⊆ X then r ^ U.card * (1 - r) ^ (X.card - U.card) else 0

theorem bsMass_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (X U : Finset (Fin n)) :
    0 ≤ bsMass r X U := by
  unfold bsMass; split_ifs
  · exact mul_nonneg (pow_nonneg hr0 _) (pow_nonneg (by linarith) _)
  · exact le_rfl

theorem sum_bsMass (r : ℝ) (X : Finset (Fin n)) : ∑ U, bsMass r X U = 1 := by
  have hset : (Finset.univ.filter fun U : Finset (Fin n) => U ⊆ X) = X.powerset := by
    ext U; simp
  rw [show (∑ U, bsMass r X U) = ∑ U ∈ Finset.univ.filter (fun U : Finset (Fin n) => U ⊆ X),
      r ^ U.card * (1 - r) ^ (X.card - U.card) by
    rw [Finset.sum_filter]; rfl, hset, Finset.sum_pow_mul_eq_add_pow]
  simp

/-- `2^{-d}` as a real. -/
def half (d : ℕ) : ℝ := (2⁻¹ : ℝ) ^ d

theorem half_nonneg (d : ℕ) : 0 ≤ half d := by unfold half; positivity
theorem half_le_one (d : ℕ) : half d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)

/-- **The Bernoulli(`2^{-d}`) subset of `X`.**
INTERNAL: the law of `Y_k` (Claim cl:loop) and of `d` successive thinning passes. -/
def bs (d : ℕ) (X : Finset (Fin n)) : PMF (Finset (Fin n)) :=
  PMF.ofFintype (fun U => ENNReal.ofReal (bsMass (half d) X U)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun U _ => bsMass_nonneg (half_nonneg d)
      (half_le_one d) X U), sum_bsMass, ENNReal.ofReal_one])

theorem bs_apply (d : ℕ) (X U : Finset (Fin n)) :
    bs d X U = ENNReal.ofReal (bsMass (half d) X U) := rfl

/-- Splitting a fresh element off: in `bsMass r (insert a Y)` the element `a` is an
independent Bernoulli(`r`).
INTERNAL. -/
theorem bsMass_insert (r : ℝ) {a : Fin n} {Y : Finset (Fin n)} (ha : a ∉ Y)
    (U : Finset (Fin n)) :
    bsMass r (insert a Y) U =
      if a ∈ U then r * bsMass r Y (U.erase a) else (1 - r) * bsMass r Y U := by
  unfold bsMass
  rw [Finset.card_insert_of_notMem ha]
  by_cases haU : a ∈ U
  · rw [if_pos haU]
    have hsub : U ⊆ insert a Y ↔ U.erase a ⊆ Y := by
      constructor
      · intro h x hx
        have hxa := Finset.ne_of_mem_erase hx
        exact (Finset.mem_insert.1 (h (Finset.mem_of_mem_erase hx))).resolve_left hxa
      · intro h x hx
        by_cases hxa : x = a
        · exact hxa ▸ Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (h (Finset.mem_erase.2 ⟨hxa, hx⟩))
    have hc : U.card = (U.erase a).card + 1 := (Finset.card_erase_add_one haU).symm
    by_cases h : U.erase a ⊆ Y
    · rw [if_pos (hsub.2 h), if_pos h, hc, pow_succ]
      have : Y.card + 1 - ((U.erase a).card + 1) = Y.card - (U.erase a).card := by omega
      rw [this]; ring
    · rw [if_neg (fun h' => h (hsub.1 h')), if_neg h, mul_zero]
  · rw [if_neg haU]
    have hsub : U ⊆ insert a Y ↔ U ⊆ Y := by
      constructor
      · intro h x hx
        exact (Finset.mem_insert.1 (h hx)).resolve_left (fun e => haU (e ▸ hx))
      · intro h; exact h.trans (Finset.subset_insert _ _)
    by_cases h : U ⊆ Y
    · rw [if_pos (hsub.2 h), if_pos h]
      have hle := Finset.card_le_card h
      have : Y.card + 1 - U.card = (Y.card - U.card) + 1 := by omega
      rw [this, pow_succ]; ring
    · rw [if_neg (fun h' => h (hsub.1 h')), if_neg h, mul_zero]

/-- Marginalizing out `a`: summing `bsMass r X V` over the `V` with `V \ {a} = W` gives
`bsMass r (X \ {a}) W`.
INTERNAL. -/
theorem sum_bsMass_erase (r : ℝ) (X : Finset (Fin n)) (a : Fin n) {W : Finset (Fin n)}
    (haW : a ∉ W) :
    ∑ V, (if V.erase a = W then bsMass r X V else 0) = bsMass r (X.erase a) W := by
  have hset : (Finset.univ.filter fun V : Finset (Fin n) => V.erase a = W) =
      {W, insert a W} := by
    ext V
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro rfl
      by_cases haV : a ∈ V
      · exact Or.inr (Finset.insert_erase haV).symm
      · exact Or.inl (Finset.erase_eq_of_notMem haV).symm
    · rintro (rfl | rfl)
      · exact Finset.erase_eq_of_notMem haW
      · exact Finset.erase_insert haW
  have hne : W ≠ insert a W := fun h => haW (h ▸ Finset.mem_insert_self a W)
  rw [← Finset.sum_filter, hset, Finset.sum_pair hne]
  by_cases haX : a ∈ X
  · have hX : X = insert a (X.erase a) := (Finset.insert_erase haX).symm
    have hnot : a ∉ X.erase a := Finset.notMem_erase a X
    conv_lhs => rw [hX, bsMass_insert r hnot, bsMass_insert r hnot]
    rw [if_neg haW, if_pos (Finset.mem_insert_self a W), Finset.erase_insert haW]
    ring
  · rw [Finset.erase_eq_of_notMem haX]
    have : bsMass r X (insert a W) = 0 := by
      unfold bsMass
      rw [if_neg (fun h => haX (h (Finset.mem_insert_self a W)))]
    rw [this, add_zero]


theorem bern_true (k : ℕ) :
    (PMF.bernoulli (keepProb k) (keepProb_le_one k)) true = ENNReal.ofReal (half k) := by
  rw [PMF.bernoulli_apply, cond_true, ← ENNReal.ofReal_coe_nnreal]
  congr 1

theorem bern_false (k : ℕ) :
    (PMF.bernoulli (keepProb k) (keepProb_le_one k)) false = ENNReal.ofReal (1 - half k) := by
  rw [PMF.bernoulli_apply, cond_false, ← ENNReal.ofReal_coe_nnreal]
  congr 1
  rw [NNReal.coe_sub (keepProb_le_one k)]; simp [keepProb, half]

theorem half_add (q d : ℕ) : half (q + d) = half q * half d := by
  unfold half; rw [pow_add]

/-- `bs` evaluated on an `insert`: the mass of `Y_{k}` after one arrival, read off. -/
theorem yStep_apply (k : ℕ) (a : Fin n) (V U : Finset (Fin n)) :
    yStep k a V U = (if a ∈ U then (if V.erase a = U.erase a then ENNReal.ofReal (half k) else 0)
      else (if V.erase a = U then ENNReal.ofReal (1 - half k) else 0)) := by
  rw [yStep, PMF.map_apply, tsum_fintype, Fintype.sum_bool, bern_true, bern_false]
  simp only [if_true, Bool.false_eq_true, if_false]
  by_cases haU : a ∈ U
  · rw [if_pos haU]
    have h1 : (U = insert a (V.erase a)) ↔ V.erase a = U.erase a := by
      constructor
      · rintro rfl; rw [Finset.erase_insert (Finset.notMem_erase a V)]
      · intro h; rw [h, Finset.insert_erase haU]
    have h2 : ¬ U = V.erase a := fun h => Finset.notMem_erase a V (h ▸ haU)
    by_cases h : V.erase a = U.erase a
    · rw [if_pos (h1.2 h), if_neg h2, if_pos h, add_zero]
    · rw [if_neg (fun e => h (h1.1 e)), if_neg h2, if_neg h, add_zero]
  · rw [if_neg haU]
    have h1 : ¬ U = insert a (V.erase a) := fun h => haU (h ▸ Finset.mem_insert_self a _)
    rw [if_neg h1, zero_add]
    by_cases h : V.erase a = U
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (fun e => h e.symm), if_neg h]

theorem sum_bs_erase (d : ℕ) (X : Finset (Fin n)) (a : Fin n) {W : Finset (Fin n)}
    (haW : a ∉ W) :
    ∑ V, (if V.erase a = W then bs d X V else 0) = ENNReal.ofReal (bsMass (half d) (X.erase a) W) := by
  rw [← sum_bsMass_erase (half d) X a haW, ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl fun V _ => ?_
    split_ifs <;> simp [bs_apply]
  · intro V _; split_ifs
    · exact bsMass_nonneg (half_nonneg d) (half_le_one d) X V
    · exact le_rfl

/-- **One arrival commutes with thinning.**  Re-adding `a` to `X \ {a}` with probability
`2^{-q}` and then keeping each element w.p. `2^{-d}` has the law of keeping each element of
`X` w.p. `2^{-d}` and then one arrival of `a` in Algorithm 3's `Y_{q+d}`.
INTERNAL: the computation behind Claim cl:loop's inductive step.
TEXLINE: esa22-final.tex:652-668 -/
theorem bs_bind_yStep_eq (q d : ℕ) (X : Finset (Fin n)) (a : Fin n) :
    (PMF.bernoulli (keepProb q) (keepProb_le_one q)).bind
        (fun c => bs d (if c then insert a (X.erase a) else X.erase a))
      = (bs d X).bind (yStep (q + d) a) := by
  have hnot : a ∉ X.erase a := Finset.notMem_erase a X
  have hq0 := half_nonneg q
  have hq1 := half_le_one q
  have hd0 := half_nonneg d
  have hd1 := half_le_one d
  ext U
  rw [PMF.bind_apply, PMF.bind_apply, tsum_fintype, tsum_fintype, Fintype.sum_bool,
    bern_true, bern_false]
  simp only [if_true, Bool.false_eq_true, if_false]
  simp only [yStep_apply]
  rw [bs_apply, bs_apply, bsMass_insert _ hnot]
  by_cases haU : a ∈ U
  · simp only [if_pos haU]
    have hz : bsMass (half d) (X.erase a) U = 0 := by
      unfold bsMass; rw [if_neg (fun h => hnot (h haU))]
    rw [hz, ENNReal.ofReal_zero, mul_zero, add_zero]
    have hs : ∑ V, bs d X V * (if V.erase a = U.erase a then ENNReal.ofReal (half (q + d)) else 0)
        = ENNReal.ofReal (half (q + d)) * ∑ V, (if V.erase a = U.erase a then bs d X V else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun V _ => ?_
      split_ifs <;> simp [mul_comm]
    rw [hs, sum_bs_erase d X a (Finset.notMem_erase a U), ← ENNReal.ofReal_mul hq0,
      ← ENNReal.ofReal_mul (half_nonneg _), half_add]
    congr 1; ring
  · simp only [if_neg haU]
    have hs : ∑ V, bs d X V * (if V.erase a = U then ENNReal.ofReal (1 - half (q + d)) else 0)
        = ENNReal.ofReal (1 - half (q + d)) * ∑ V, (if V.erase a = U then bs d X V else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun V _ => ?_
      split_ifs <;> simp [mul_comm]
    have hm0 := bsMass_nonneg hd0 hd1 (X.erase a) U
    rw [hs, sum_bs_erase d X a haU, ← ENNReal.ofReal_mul hq0, ← ENNReal.ofReal_mul (by linarith),
      ← ENNReal.ofReal_add (mul_nonneg hq0 (mul_nonneg (by linarith) hm0))
        (mul_nonneg (by linarith) hm0),
      ← ENNReal.ofReal_mul (by rw [half_add]; nlinarith), half_add]
    congr 1; ring


/-- The law of line 6's thinning pass on a sample `X`: keep the heads of a uniform
subset of `Fin n` (one fair coin per element).
INTERNAL: `Pseudocode.throw` read on the sample. -/
def throwLaw (X : Finset (Fin n)) : PMF (Finset (Fin n)) :=
  (PMF.uniformOfFintype (Finset (Fin n))).map fun h => X.filter (· ∈ h)

/-- **Line 6 keeps each element independently w.p. ½**: `throwLaw X = bs 1 X`.
INTERNAL.
TEXLINE: esa22-final.tex:433 -/
theorem throwLaw_eq_bs (X : Finset (Fin n)) : throwLaw X = bs 1 X := by
  ext U
  rw [throwLaw, PMF.map_apply, tsum_fintype, bs_apply]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_finset, Fintype.card_fin]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  by_cases hU : U ⊆ X
  · -- the heads sets with `X ∩ h = U` are `U ∪ W`, `W ⊆ Xᶜ`
    have hset : (Finset.univ.filter fun h : Finset (Fin n) => U = X.filter (· ∈ h)) =
        (Xᶜ).powerset.image (U ∪ ·) := by
      ext h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_powerset]
      constructor
      · intro e
        refine ⟨h \ X, fun x hx => Finset.mem_compl.2 (Finset.mem_sdiff.1 hx).2, ?_⟩
        ext x
        simp only [Finset.mem_union, Finset.mem_sdiff, e, Finset.mem_filter]
        tauto
      · rintro ⟨W, hW, rfl⟩
        ext x
        simp only [Finset.mem_filter, Finset.mem_union]
        constructor
        · intro hx; exact ⟨hU hx, Or.inl hx⟩
        · rintro ⟨hxX, hx | hx⟩
          · exact hx
          · exact absurd hxX (Finset.mem_compl.1 (hW hx))
    have hinj : Set.InjOn (U ∪ ·) ((Xᶜ).powerset : Set (Finset (Fin n))) := by
      intro W₁ h₁ W₂ h₂ e
      simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
        Finset.coe_subset] at h₁ h₂
      have e' : ∀ x, x ∈ U ∪ W₁ ↔ x ∈ U ∪ W₂ := fun x => by rw [show U ∪ W₁ = U ∪ W₂ from e]
      ext x
      have hxU : x ∈ U → x ∉ W₁ ∧ x ∉ W₂ := fun hx =>
        ⟨fun h => Finset.mem_compl.1 (h₁ h) (hU hx), fun h => Finset.mem_compl.1 (h₂ h) (hU hx)⟩
      have := e' x
      simp only [Finset.mem_union] at this
      by_cases hx : x ∈ U
      · simp [(hxU hx).1, (hxU hx).2]
      · tauto
    rw [hset, Finset.card_image_of_injOn hinj, Finset.card_powerset, Finset.card_compl,
      Fintype.card_fin, bsMass, if_pos hU, half, pow_one]
    have hk : X.card ≤ n := by simpa using Finset.card_le_univ X
    have hUX : U.card ≤ X.card := Finset.card_le_card hU
    rw [show (1 - (2⁻¹ : ℝ)) = 2⁻¹ by norm_num, ← pow_add, Nat.add_sub_cancel' hUX]
    generalize X.card = k at hk ⊢
    obtain ⟨e, rfl⟩ : ∃ e, n = k + e := ⟨n - k, by omega⟩
    rw [Nat.add_sub_cancel_left, pow_add]
    push_cast
    rw [ENNReal.mul_inv (by simp) (by simp), ← mul_assoc, mul_right_comm,
      ENNReal.mul_inv_cancel (by simp) (by simp), one_mul, ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat, ENNReal.inv_pow]
  · have hset : (Finset.univ.filter fun h : Finset (Fin n) => U = X.filter (· ∈ h)) = ∅ := by
      ext h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro e; exact hU (e ▸ Finset.filter_subset _ _)
    rw [hset, bsMass, if_neg hU]
    simp

/-- The empty set thins to itself.
INTERNAL. -/
theorem bs_empty (d : ℕ) : bs d (∅ : Finset (Fin n)) = PMF.pure ∅ := by
  ext U
  rw [bs_apply, PMF.pure_apply, bsMass]
  by_cases h : U = ∅
  · subst h; simp
  · rw [if_neg (fun h' => h (Finset.subset_empty.1 h')), if_neg h, ENNReal.ofReal_zero]

/-- A Bernoulli(`2^{-0}`) coin is always heads.
INTERNAL. -/
theorem bern_zero : PMF.bernoulli (keepProb 0) (keepProb_le_one 0) = PMF.pure true := by
  ext b; cases b <;> simp [PMF.bernoulli_apply, keepProb]

/-- **Claim cl:loop.**  Every distinct item of the stream is in `Y_{k,m}` independently
with probability `2^{-k}`: `yLaw k A = bs k A.toFinset`.
PAPER: esa22-final.tex:615-672 -/
theorem yLaw_eq_bs (k : ℕ) (A : List (Fin n)) : yLaw k A = bs k A.toFinset := by
  induction A using List.reverseRecOn with
  | nil => rw [yLaw, yRun, List.toFinset_nil, bs_empty]
  | append_singleton A a ih =>
    rw [yLaw, yRun_append, ← yLaw, ih]
    have := bs_bind_yStep_eq 0 k A.toFinset a
    rw [Nat.zero_add, bern_zero, PMF.pure_bind, if_pos rfl] at this
    rw [← this, List.toFinset_append, List.toFinset_cons, List.toFinset_nil]
    congr 1
    ext x; by_cases hx : x = a <;> simp [hx, or_comm]

end Esa22Copy.Analysis.Alg2

end
