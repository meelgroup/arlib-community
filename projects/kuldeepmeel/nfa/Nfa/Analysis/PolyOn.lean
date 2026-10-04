import Nfa.Analysis.PmfExpect

/-!
# Multiaffine polynomials and their expectations

`PolyOn V F`: `F : (E → ℝ) → ℝ` is a finite sum `Σ_k c_k ∏_{e ∈ T_k} x_e` with every
`T_k ⊆ V` — a polynomial that is affine in each coordinate, in the coordinates `V`.
`ex_polyOn`: if every product of distinct coordinates in `V` has expectation the product
of the means, then `E[F(X)] = F(m)`.

This is the shape of every expectation computation in the proof of
Lemma bound_proba_AND_event (analysis.tex:221-370, 695-719): the quantities
`∏_b (N_{b,j} + V_{b,j})` are multiaffine in the atoms of layer `j`, and each product of
distinct atoms has expectation the product of the atoms one layer down.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nfa.Analysis.PolyOnAux

variable {E : Type} [DecidableEq E]

/-- `F` is a multiaffine polynomial in the coordinates `V`.

INTERNAL: the class of functions the paper's tower-rule identities are applied to.
TEXLINE: analysis.tex:695-719 -/
def PolyOn (V : Finset E) (F : (E → ℝ) → ℝ) : Prop :=
  ∃ (ι : Type) (K : Finset ι) (c : ι → ℝ) (T : ι → Finset E),
    (∀ k ∈ K, T k ⊆ V) ∧ ∀ x, F x = ∑ k ∈ K, c k * ∏ e ∈ T k, x e

/-- Constants are polynomials.

INTERNAL: closure of `PolyOn`.
TEXLINE: analysis.tex:695-719 -/
theorem PolyOn.const (V : Finset E) (a : ℝ) : PolyOn V fun _ => a :=
  ⟨Unit, {()}, fun _ => a, fun _ => ∅, fun _ _ => Finset.empty_subset _, fun _ => by simp⟩

/-- Coordinates are polynomials.

INTERNAL: closure of `PolyOn`.
TEXLINE: analysis.tex:695-719 -/
theorem PolyOn.var {V : Finset E} {e : E} (he : e ∈ V) : PolyOn V fun x => x e :=
  ⟨Unit, {()}, fun _ => 1, fun _ => {e}, fun _ _ => Finset.singleton_subset_iff.2 he,
    fun _ => by simp⟩

/-- Enlarging the coordinate set.

INTERNAL: closure of `PolyOn`.
TEXLINE: analysis.tex:695-719 -/
theorem PolyOn.mono {V W : Finset E} {F : (E → ℝ) → ℝ} (h : PolyOn V F) (hVW : V ⊆ W) :
    PolyOn W F := by
  obtain ⟨ι, K, c, T, hT, hF⟩ := h
  exact ⟨ι, K, c, T, fun k hk => (hT k hk).trans hVW, hF⟩

/-- Sums.

INTERNAL: closure of `PolyOn`.
TEXLINE: analysis.tex:695-719 -/
theorem PolyOn.add {V : Finset E} {F G : (E → ℝ) → ℝ} (hF : PolyOn V F) (hG : PolyOn V G) :
    PolyOn V fun x => F x + G x := by
  obtain ⟨ι, K, c, T, hT, hF⟩ := hF
  obtain ⟨κ, L, d, U, hU, hG⟩ := hG
  refine ⟨ι ⊕ κ, K.disjSum L, Sum.elim c d, Sum.elim T U, ?_, fun x => ?_⟩
  · intro k hk
    rcases k with k | k
    · exact hT k (Finset.inl_mem_disjSum.1 hk)
    · exact hU k (Finset.inr_mem_disjSum.1 hk)
  · show F x + G x = _
    rw [Finset.sum_disjSum, hF, hG]
    rfl

/-- Scalar multiples.

INTERNAL: closure of `PolyOn`.
TEXLINE: analysis.tex:695-719 -/
theorem PolyOn.smul {V : Finset E} {F : (E → ℝ) → ℝ} (a : ℝ) (hF : PolyOn V F) :
    PolyOn V fun x => a * F x := by
  obtain ⟨ι, K, c, T, hT, hF⟩ := hF
  refine ⟨ι, K, fun k => a * c k, T, hT, fun x => ?_⟩
  show a * F x = _
  rw [hF, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Differences.

INTERNAL: closure of `PolyOn`.
TEXLINE: analysis.tex:695-719 -/
theorem PolyOn.sub {V : Finset E} {F G : (E → ℝ) → ℝ} (hF : PolyOn V F) (hG : PolyOn V G) :
    PolyOn V fun x => F x - G x := by
  have := hF.add (hG.smul (-1))
  simpa [sub_eq_add_neg] using this

/-- Products of polynomials in disjoint coordinates.

INTERNAL: closure of `PolyOn`; independence is only ever used across disjoint atoms.
TEXLINE: analysis.tex:695-719 -/
theorem PolyOn.mul {V W : Finset E} {F G : (E → ℝ) → ℝ} (hF : PolyOn V F) (hG : PolyOn W G)
    (hd : Disjoint V W) : PolyOn (V ∪ W) fun x => F x * G x := by
  obtain ⟨ι, K, c, T, hT, hF⟩ := hF
  obtain ⟨κ, L, d, U, hU, hG⟩ := hG
  refine ⟨ι × κ, K ×ˢ L, fun k => c k.1 * d k.2, fun k => T k.1 ∪ U k.2, ?_, fun x => ?_⟩
  · intro k hk
    rw [Finset.mem_product] at hk
    exact Finset.union_subset_union (hT _ hk.1) (hU _ hk.2)
  · show F x * G x = _
    rw [hF, hG, Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_product] at hk
    rw [Finset.prod_union (hd.mono (hT _ hk.1) (hU _ hk.2))]
    ring

/-- Finite sums.

INTERNAL: closure of `PolyOn`.
TEXLINE: analysis.tex:695-719 -/
theorem PolyOn.sum {ι : Type} {V : Finset E} (K : Finset ι) {F : ι → (E → ℝ) → ℝ}
    (hF : ∀ k ∈ K, PolyOn V (F k)) : PolyOn V fun x => ∑ k ∈ K, F k x := by
  classical
  induction K using Finset.induction_on with
  | empty => simpa using PolyOn.const V 0
  | insert a K ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hF a (Finset.mem_insert_self _ _)).add
        (ih fun k hk => hF k (Finset.mem_insert_of_mem hk))

/-- Finite products of polynomials in pairwise disjoint coordinates.

INTERNAL: closure of `PolyOn`; the product over blocks `∏_{b ∈ F}`.
TEXLINE: analysis.tex:695-719 -/
theorem PolyOn.prod {ι : Type} [DecidableEq ι] (K : Finset ι) (V : ι → Finset E)
    {F : ι → (E → ℝ) → ℝ} (hF : ∀ k ∈ K, PolyOn (V k) (F k))
    (hd : ∀ k ∈ K, ∀ l ∈ K, k ≠ l → Disjoint (V k) (V l)) :
    PolyOn (K.biUnion V) fun x => ∏ k ∈ K, F k x := by
  induction K using Finset.induction_on with
  | empty => simpa using PolyOn.const (∅ : Finset E) 1
  | insert a K ha ih =>
      simp only [Finset.prod_insert ha, Finset.biUnion_insert]
      refine (hF a (Finset.mem_insert_self _ _)).mul
        (ih (fun k hk => hF k (Finset.mem_insert_of_mem hk))
          fun k hk l hl hkl => hd k (Finset.mem_insert_of_mem hk) l
            (Finset.mem_insert_of_mem hl) hkl) ?_
      rw [Finset.disjoint_biUnion_right]
      intro l hl
      exact hd a (Finset.mem_insert_self _ _) l (Finset.mem_insert_of_mem hl)
        fun h => ha (h ▸ hl)

open PmfExpect

/-- **Expectation of a multiaffine polynomial**: if every product of distinct coordinates
in `V` has expectation the product of the means `m`, then `E[F(X)] = F(m)`.

INTERNAL: the step "apply the singleton/pair expectations termwise" of the paper.
TEXLINE: analysis.tex:695-719 -/
theorem ex_polyOn {Ω : Type} (μ : PMF Ω) (hμ : μ.support.Finite) (X : Ω → E → ℝ)
    (m : E → ℝ) {V : Finset E} {F : (E → ℝ) → ℝ} (hF : PolyOn V F)
    (hmom : ∀ T ⊆ V, ex μ (fun ω => ∏ e ∈ T, X ω e) = ∏ e ∈ T, m e) :
    ex μ (fun ω => F (X ω)) = F m := by
  obtain ⟨ι, K, c, T, hT, hF⟩ := hF
  simp only [hF]
  rw [ex_sum μ hμ]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [ex_mul_left, hmom _ (hT k hk)]

end Nfa.Analysis.PolyOnAux

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `PolyOn` closure lemmas and `ex_polyOn`
-/
