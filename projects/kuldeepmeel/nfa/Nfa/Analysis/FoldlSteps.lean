import Nfa.Model.Program

/-!
# Step counting through `Charged.foldl`, and the size of a sample array

Generic tools for the running-time half of theorem:main_result
(analysis.tex:40-55, 67-68): the steps of a charged fold are the sum of the steps
of its iterations (`steps_foldl_cons`), and a fold whose iterations preserve an
invariant, cost at most `k a` and grow a measure by at most `g a` costs at most
`Σ k` and grows the measure by at most `Σ g` (`foldl_inv_le`).

`samplesSize X` is the number of words held in a sample array `X`, counting each
index; `sum_getD_length_le` says reading any range of indices visits at most that
many words.
-/

set_option autoImplicit false

namespace Nfa.Analysis

open Arlib.Computation

section Generic

variable {κ κₛ : Type} [Fintype κ] {β ι : Type}

/-- INTERNAL: the steps of a fold over a cons are the steps of the first iteration
plus the steps of the rest.
TEXLINE: analysis.tex:40-55 -/
theorem steps_foldl_cons (C : Rate κ) (f : β → ι → Charged κ κₛ β) (a : ι) (l : List ι)
    (b : β) :
    Charged.steps C (Charged.foldl f (a :: l) b) =
      Charged.steps C (f b a) + Charged.steps C (Charged.foldl f l (f b a).val) := by
  simp only [Charged.steps, Charged.cost_foldl_cons, CostVec.steps_add]

/-- INTERNAL: a fold over the empty list takes no steps.
TEXLINE: analysis.tex:40-55 -/
@[simp] theorem steps_foldl_nil (C : Rate κ) (f : β → ι → Charged κ κₛ β) (b : β) :
    Charged.steps C (Charged.foldl f [] b) = 0 := by
  simp [Charged.steps]

/-- INTERNAL: **the fold rule with an invariant and a measure.**  If every iteration
on an element of `l` preserves `I`, takes at most `k a` steps and raises `Φ` by at
most `g a`, the fold preserves `I`, takes at most `Σ k` steps and raises `Φ` by at
most `Σ g`.
TEXLINE: analysis.tex:40-55 -/
theorem foldl_inv_le (C : Rate κ) (f : β → ι → Charged κ κₛ β) (I : β → Prop)
    (Φ : β → ℕ) (k g : ι → ℕ) (l : List ι)
    (h : ∀ b a, a ∈ l → I b →
      I (f b a).val ∧ Charged.steps C (f b a) ≤ k a ∧ Φ (f b a).val ≤ Φ b + g a)
    (b : β) (hb : I b) :
    I (Charged.foldl f l b).val ∧
      Charged.steps C (Charged.foldl f l b) ≤ (l.map k).sum ∧
      Φ (Charged.foldl f l b).val ≤ Φ b + (l.map g).sum := by
  induction l generalizing b with
  | nil => simp [hb]
  | cons a l ih =>
      obtain ⟨hI, hk, hg⟩ := h b a (by simp) hb
      obtain ⟨hI', hk', hg'⟩ :=
        ih (fun b a ha hb => h b a (List.mem_cons_of_mem _ ha) hb) (f b a).val hI
      refine ⟨by simpa using hI', ?_, ?_⟩
      · rw [steps_foldl_cons]; simp only [List.map_cons, List.sum_cons]; omega
      · simp only [Charged.val_foldl_cons, List.map_cons, List.sum_cons]; omega

/-- INTERNAL: the fold rule with a constant bound per iteration and no invariant.
TEXLINE: analysis.tex:40-55 -/
theorem steps_foldl_le_sum (C : Rate κ) (f : β → ι → Charged κ κₛ β) (k : ι → ℕ)
    (l : List ι) (h : ∀ b a, a ∈ l → Charged.steps C (f b a) ≤ k a) (b : β) :
    Charged.steps C (Charged.foldl f l b) ≤ (l.map k).sum :=
  (foldl_inv_le C f (fun _ => True) (fun _ => 0) k (fun _ => 0) l
    (fun b a ha _ => ⟨trivial, h b a ha, by simp⟩) b trivial).2.1

end Generic

/-! ## The project rate -/

open Nfa.Model.Operations in
/-- INTERNAL: every operation other than the witness product costs one step.
TEXLINE: introduction.tex:146-163 -/
@[simp] theorem rate_cost_of_ne (MM : ℕ → ℕ) (m : ℕ) (o : Nfa.Model.Operations.Op) (h : o ≠ .witnessProduct) :
    (rate MM m).cost o = 1 := by
  cases o <;> simp_all [rate, price]

open Nfa.Model.Operations in
/-- INTERNAL: one witness product costs `max 1 (MM m)` steps.
TEXLINE: introduction.tex:146-163 -/
@[simp] theorem rate_cost_witnessProduct (MM : ℕ → ℕ) (m : ℕ) :
    (rate MM m).cost .witnessProduct = max 1 (MM m) := rfl

/-! ## Sample arrays -/

/-- INTERNAL: the number of words held in a sample array, summed over its indices.
TEXLINE: analysis.tex:40-55 -/
def samplesSize (X : Nfa.Program.Samples) : ℕ := (X.toList.map List.length).sum

@[simp] theorem samplesSize_empty : samplesSize #[] = 0 := rfl

@[simp] theorem samplesSize_push (X : Nfa.Program.Samples) (T : List (List Bool)) :
    samplesSize (X.push T) = samplesSize X + T.length := by
  simp [samplesSize]

/-- INTERNAL: reading the first `k` indices of a list of lists visits at most all
of its words.
TEXLINE: analysis.tex:40-55 -/
theorem sum_range_getD_length_le (L : List (List (List Bool))) (k : ℕ) :
    ∑ r ∈ Finset.range k, (L.getD r []).length ≤ (L.map List.length).sum := by
  induction L generalizing k with
  | nil => simp
  | cons x L ih =>
      cases k with
      | zero => simp
      | succ k =>
          rw [Finset.sum_range_succ']
          simp only [List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.sum_cons]
          have := ih k
          omega

/-- INTERNAL: reading the first `k` indices of a sample array visits at most
`samplesSize` words.
TEXLINE: analysis.tex:40-55 -/
theorem sum_getD_length_le (X : Nfa.Program.Samples) (k : ℕ) :
    ∑ r ∈ Finset.range k, (X.getD r []).length ≤ samplesSize X := by
  have h : ∀ r, X.getD r [] = X.toList.getD r [] := by
    intro r
    simp only [Array.getD, List.getD]
    split <;> simp_all
  simp only [h]
  exact sum_range_getD_length_le X.toList k

end Nfa.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · generic fold step lemmas (`foldl_inv_le`, `steps_foldl_cons`), `samplesSize`, `rate_cost_*`
-/
