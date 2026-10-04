import Nfa.Analysis.SpiritMoments

/-!
# Canonical runs, divergence layers, derivation paths

For `w ∈ L(q^i)`, `canon σ q w j` is the state `q^j_w` at layer `j` of the canonical run
of `w` into `q` (analysis.tex:187-194), built backwards with the selector `σ`;
`canon_pred` is the child relation the atoms follow.  `dv σ q i w₁ w₂` is the
divergence layer (`(w₁, w₂) ∈ L_{dv}`, analysis.tex:196-201), and
`sum_langCount_dv_le` is the derivation-path count
`Σ_{w₂} |L(q^{w₁,w₂})| ≤ (i+1)|L(q)|` (derivationpath.tex:197-206, analysis.tex:676-686).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nfa.Analysis.CanonPathAux
open Nfa.Pseudocode SpiritMomentsAux

variable {Q : Type} [Fintype Q] [LinearOrder Q]

/-- The canonical path, on the reversed word.

INTERNAL: the canonical runs `paths(w, q)` of analysis.tex:187-194, built backwards with `σ`.
TEXLINE: analysis.tex:187-194 -/
noncomputable def canonRev {A : PaperNFA Q} (σ : Selector A) (j : ℕ) : Q → List Bool → Q
  | q, [] => q
  | q, b :: rev => if rev.length < j then q else canonRev σ j ((σ.pick q rev.reverse b).getD q) rev

/-- `q^j_w`: the state at layer `j` on the canonical (σ-chosen) run of `w` into `q`.

INTERNAL: the canonical runs `paths(w, q)` of analysis.tex:187-194.
TEXLINE: analysis.tex:187-194 -/
noncomputable def canon {A : PaperNFA Q} (σ : Selector A) (q : Q) (w : List Bool) (j : ℕ) : Q :=
  canonRev σ j q w.reverse

/-- The empty word stays at `q`.

INTERNAL: canonical-path bookkeeping.
TEXLINE: analysis.tex:187-194 -/
theorem canon_nil {A : PaperNFA Q} (σ : Selector A) (q : Q) (j : ℕ) : canon σ q [] j = q := rfl

/-- One step back along the canonical run.

INTERNAL: canonical-path bookkeeping.
TEXLINE: analysis.tex:187-194 -/
theorem canon_snoc {A : PaperNFA Q} (σ : Selector A) (q : Q) (v : List Bool) (b : Bool) (j : ℕ) :
    canon σ q (v ++ [b]) j =
      if v.length < j then q else canon σ ((σ.pick q v b).getD q) v j := by
  simp [canon, canonRev, List.reverse_append]

/-- At or above the word's own layer the canonical node is `q`.

INTERNAL: canonical-path bookkeeping.
TEXLINE: analysis.tex:187-194 -/
theorem canon_of_le {A : PaperNFA Q} (σ : Selector A) (q : Q) (w : List Bool) (j : ℕ)
    (h : w.length ≤ j) : canon σ q w j = q := by
  induction w using List.reverseRecOn generalizing q with
  | nil => rfl
  | append_singleton v b ih =>
      rw [canon_snoc, if_pos (by simp at h; omega)]

/-- Along a word of `L(q)`, the canonical state at layer `j` reads the prefix of length `j`.

INTERNAL: canonical-path bookkeeping.
TEXLINE: analysis.tex:187-194 -/
theorem canon_mem_eval (A : PaperNFA Q) (σ : Selector A) (w : List Bool) :
    ∀ (q : Q), q ∈ A.toNFA.eval w → ∀ j ≤ w.length, canon σ q w j ∈ A.toNFA.eval (w.take j) := by
  induction w using List.reverseRecOn with
  | nil => intro q hq j hj; simp at hj; subst hj; simpa [canon_nil] using hq
  | append_singleton v b ih =>
      intro q hq j hj
      rw [canon_snoc]
      split_ifs with hlt
      · have : j = v.length + 1 := by simp at hj; omega
        subst this
        rw [List.take_of_length_le (by simp)]
        exact hq
      · rw [NFA.eval_append_singleton, NFA.mem_stepSet] at hq
        obtain ⟨c, hc, hcq⟩ := hq
        obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.1 (σ.pick_complete q v b c hcq hc)
        rw [hc', Option.getD_some, List.take_append_of_le_length (by omega)]
        exact ih c' (σ.pick_sound q v b c' hc').2 j (by omega)

/-- The canonical path is determined by any later node.

INTERNAL: canonical-path bookkeeping.
TEXLINE: analysis.tex:187-194 -/
theorem canon_take (A : PaperNFA Q) (σ : Selector A) (w : List Bool) :
    ∀ (q : Q) (j j' : ℕ), j ≤ j' → j' ≤ w.length →
      canon σ q w j = canon σ (canon σ q w j') (w.take j') j := by
  induction w using List.reverseRecOn with
  | nil => intro q j j' _ hj'; simp at hj'; subst hj'; simp [canon_nil]
  | append_singleton v b ih =>
      intro q j j' hjj' hj'
      by_cases hj'eq : j' = v.length + 1
      · subst hj'eq
        rw [List.take_of_length_le (by simp), canon_of_le σ q _ (v.length + 1) (by simp)]
      · have hj'v : j' ≤ v.length := by simp at hj'; omega
        rw [canon_snoc, canon_snoc, if_neg (by omega), if_neg (by omega),
          List.take_append_of_le_length hj'v]
        exact ih _ j j' hjj' hj'v

/-- **The child relation along the canonical run**: the node at layer `j − 1` is the
canonical predecessor of the node at layer `j`.

INTERNAL: the canonical child `(v, c)` of `(w, q)` (lemma expectation_of_singleton).
TEXLINE: analysis.tex:221-224 -/
theorem canon_pred (A : PaperNFA Q) (σ : Selector A) (w : List Bool) (q : Q) (j : ℕ)
    (hj : 1 ≤ j) (hjw : j ≤ w.length) :
    canon σ q w (j - 1) = childOf σ (canon σ q w j) (w.take j) := by
  rw [canon_take A σ w q (j - 1) j (by omega) hjw]
  have hlen : (w.take j).length = j := by simp; omega
  obtain ⟨v, b, hvb⟩ : ∃ v b, w.take j = v ++ [b] := by
    rcases List.eq_nil_or_concat (w.take j) with h | ⟨v, b, h⟩
    · rw [h] at hlen; simp at hlen; omega
    · exact ⟨v, b, by rw [h, List.concat_eq_append]⟩
  have hv : v.length = j - 1 := by rw [hvb] at hlen; simp at hlen; omega
  rw [hvb, canon_snoc, if_neg (by omega), canon_of_le σ _ v _ (by omega)]
  simp [childOf, List.dropLast_concat, List.getLastD_concat]

/-- The suffix after layer `j` leads from the canonical node to `q`.

INTERNAL: canonical-path bookkeeping for the derivation-path count.
TEXLINE: derivationpath.tex:197-206 -/
theorem mem_eval_append_drop (A : PaperNFA Q) (σ : Selector A) (w : List Bool) :
    ∀ (q : Q), q ∈ A.toNFA.eval w → ∀ j ≤ w.length, ∀ v : List Bool,
      canon σ q w j ∈ A.toNFA.eval v → q ∈ A.toNFA.eval (v ++ w.drop j) := by
  induction w using List.reverseRecOn with
  | nil => intro q _ j _ v hv; simpa [canon_nil] using hv
  | append_singleton w' b ih =>
      intro q hq j hj v hv
      rw [canon_snoc] at hv
      split_ifs at hv with hlt
      · have : j = w'.length + 1 := by simp at hj; omega
        subst this
        rw [List.drop_of_length_le (by simp), List.append_nil]
        exact hv
      · rw [NFA.eval_append_singleton, NFA.mem_stepSet] at hq
        obtain ⟨c, hc, hcq⟩ := hq
        obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.1 (σ.pick_complete q w' b c hcq hc)
        rw [hc', Option.getD_some] at hv
        have hsound := σ.pick_sound q w' b c' hc'
        have := ih c' hsound.2 j (by omega) v hv
        rw [List.drop_append_of_le_length (by omega), ← List.append_assoc,
          NFA.eval_append_singleton, NFA.mem_stepSet]
        exact ⟨c', this, hsound.1⟩


/-- `L(q^ℓ)` as a `Finset`.

INTERNAL: the finite language of an unrolled state.
TEXLINE: background.tex:18 -/
noncomputable def lang (A : PaperNFA Q) (ℓ : ℕ) (q : Q) : Finset (List Bool) :=
  haveI := Classical.decPred fun w : List Bool => q ∈ A.toNFA.eval w
  Finset.filter (fun w => q ∈ A.toNFA.eval w)
    ((Finset.univ : Finset (Fin ℓ → Bool)).image List.ofFn)

/-- Membership in `L(q^ℓ)`.

INTERNAL: bookkeeping.
TEXLINE: background.tex:18 -/
theorem mem_lang (A : PaperNFA Q) (ℓ : ℕ) (q : Q) (w : List Bool) :
    w ∈ lang A ℓ q ↔ w.length = ℓ ∧ q ∈ A.toNFA.eval w := by
  classical
  unfold lang
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨f, rfl⟩, h⟩
    exact ⟨List.length_ofFn, h⟩
  · rintro ⟨hl, h⟩
    subst hl
    exact ⟨⟨fun k => w.get k, List.ofFn_get w⟩, h⟩

/-- `|L(q^ℓ)|` as the card of `lang`.

INTERNAL: bookkeeping.
TEXLINE: background.tex:18 -/
theorem card_lang (A : PaperNFA Q) (ℓ : ℕ) (q : Q) :
    (lang A ℓ q).card = langCount A ℓ q := by
  unfold langCount
  rw [← Set.ncard_coe_finset]
  congr 1
  ext w
  rw [Finset.mem_coe, mem_lang]
  rfl

/-- Agreement of the canonical nodes of `w₁`, `w₂ ∈ L(q)` at layer `j`.

INTERNAL: the partition `L(q)² = L_0 ∪ … ∪ L_i` of analysis.tex:196-201.
TEXLINE: analysis.tex:196-201 -/
def agree {A : PaperNFA Q} (σ : Selector A) (q : Q) (w1 w2 : List Bool) (j : ℕ) : Prop :=
  w1.take j = w2.take j ∧ canon σ q w1 j = canon σ q w2 j

/-- Agreement is decidable.

INTERNAL: bookkeeping.
TEXLINE: analysis.tex:196-201 -/
noncomputable instance agree_decidable {A : PaperNFA Q} (σ : Selector A) (q : Q) (w1 w2 : List Bool) (j : ℕ) :
    Decidable (agree σ q w1 w2 j) := by
  unfold agree; infer_instance

/-- Agreement at layer `j` persists below `j`.

INTERNAL: the divergence node is well defined.
TEXLINE: analysis.tex:196-201 -/
theorem agree_mono (A : PaperNFA Q) (σ : Selector A) (q : Q) (w1 w2 : List Bool) (j j' : ℕ)
    (hjj : j' ≤ j) (h1 : j ≤ w1.length) (h2 : j ≤ w2.length) (h : agree σ q w1 w2 j) :
    agree σ q w1 w2 j' := by
  obtain ⟨ht, hc⟩ := h
  refine ⟨?_, ?_⟩
  · have htt : ∀ w : List Bool, w.take j' = (w.take j).take j' := fun w => by
      rw [List.take_take, min_eq_left hjj]
    rw [htt w1, htt w2, ht]
  · rw [canon_take A σ w1 q j' j hjj h1, canon_take A σ w2 q j' j hjj h2, hc, ht]


/-- The divergence layer of `w₁, w₂ ∈ L(q^i)`: the last layer where their canonical nodes
agree (`q^{w₁,w₂}` is the node there).

INTERNAL: the index `k` with `(w₁, w₂) ∈ L_k` of analysis.tex:196-201.
TEXLINE: analysis.tex:196-201 -/
noncomputable def dv {A : PaperNFA Q} (σ : Selector A) (q : Q) (i : ℕ) (w1 w2 : List Bool) : ℕ :=
  Nat.findGreatest (fun j => agree σ q w1 w2 j) i

/-- `dv ≤ i`.

INTERNAL: bookkeeping.
TEXLINE: analysis.tex:196-201 -/
theorem dv_le {A : PaperNFA Q} (σ : Selector A) (q : Q) (i : ℕ) (w1 w2 : List Bool) :
    dv σ q i w1 w2 ≤ i := Nat.findGreatest_le i

/-- Every two words agree at layer `0` (at `q_I`).

INTERNAL: bookkeeping.
TEXLINE: analysis.tex:196-201 -/
theorem agree_zero (A : PaperNFA Q) (σ : Selector A) (q : Q) (i : ℕ) (w1 w2 : List Bool)
    (h1 : w1 ∈ lang A i q) (h2 : w2 ∈ lang A i q) : agree σ q w1 w2 0 := by
  rw [mem_lang] at h1 h2
  refine ⟨by simp, ?_⟩
  have e1 := canon_mem_eval A σ w1 q h1.2 0 (Nat.zero_le _)
  have e2 := canon_mem_eval A σ w2 q h2.2 0 (Nat.zero_le _)
  simp only [List.take_zero, NFA.eval_nil, PaperNFA.toNFA, Set.mem_singleton_iff] at e1 e2
  rw [e1, e2]

/-- Agreement at `j` is `j ≤ dv`.

INTERNAL: bookkeeping.
TEXLINE: analysis.tex:196-201 -/
theorem agree_iff_le_dv (A : PaperNFA Q) (σ : Selector A) (q : Q) (i : ℕ) (w1 w2 : List Bool)
    (h1 : w1 ∈ lang A i q) (h2 : w2 ∈ lang A i q) (j : ℕ) (hj : j ≤ i) :
    agree σ q w1 w2 j ↔ j ≤ dv σ q i w1 w2 := by
  classical
  have hl1 := ((mem_lang A i q w1).1 h1).1
  have hl2 := ((mem_lang A i q w2).1 h2).1
  constructor
  · intro h
    unfold dv
    exact Nat.le_findGreatest hj h
  · intro h
    have hspec : agree σ q w1 w2 (dv σ q i w1 w2) := by
      unfold dv
      exact Nat.findGreatest_spec (P := fun j => agree σ q w1 w2 j) (Nat.zero_le i)
        (agree_zero A σ q i w1 w2 h1 h2)
    exact agree_mono A σ q w1 w2 _ j h (by rw [hl1]; exact dv_le σ q i w1 w2)
      (by rw [hl2]; exact dv_le σ q i w1 w2) hspec

/-- `dv = i` exactly on the diagonal (`L_i = {(w, w)}`).

INTERNAL: bookkeeping.
TEXLINE: analysis.tex:196-201 -/
theorem dv_eq_iff (A : PaperNFA Q) (σ : Selector A) (q : Q) (i : ℕ) (w1 w2 : List Bool)
    (h1 : w1 ∈ lang A i q) (h2 : w2 ∈ lang A i q) : dv σ q i w1 w2 = i ↔ w1 = w2 := by
  have hl1 := ((mem_lang A i q w1).1 h1).1
  have hl2 := ((mem_lang A i q w2).1 h2).1
  rw [le_antisymm_iff, and_iff_right (dv_le σ q i w1 w2),
    ← agree_iff_le_dv A σ q i w1 w2 h1 h2 i le_rfl]
  unfold agree
  rw [List.take_of_length_le hl1.le, List.take_of_length_le hl2.le,
    canon_of_le σ q w1 i hl1.le, canon_of_le σ q w2 i hl2.le]
  simp

/-- **Derivation paths** (derivationpath.tex:197-206): the words of `L(q)` whose canonical
node at layer `j` is that of `w₁`, times `|L(q^{w₁}_j)|`, number at most `|L(q)|`.

INTERNAL: the bound `|D(w₁,j)|·|L(q^{w₁}_j)| ≤ |L(q)|` used at analysis.tex:680-684.
TEXLINE: derivationpath.tex:197-206 -/
theorem card_agree_mul_le (A : PaperNFA Q) (σ : Selector A) (q : Q) (i : ℕ) (w1 : List Bool)
    (j : ℕ) (hj : j ≤ i) :
    ((lang A i q).filter fun w2 => agree σ q w1 w2 j).card *
        (lang A j (canon σ q w1 j)).card ≤ (lang A i q).card := by
  classical
  rw [mul_comm, ← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun x => x.1 ++ x.2.drop j) ?_ ?_
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_filter] at hx
    obtain ⟨hv, hw2, hag⟩ := hx
    rw [mem_lang] at hv hw2
    show x.1 ++ x.2.drop j ∈ lang A i q
    rw [mem_lang]
    refine ⟨by simp [hv.1, hw2.1]; omega, ?_⟩
    apply mem_eval_append_drop A σ x.2 q hw2.2 j (by omega) x.1
    rw [← hag.2]
    exact hv.2
  · intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_filter] at hx hy
    have hxl := ((mem_lang A _ _ _).1 hx.1).1
    have hyl := ((mem_lang A _ _ _).1 hy.1).1
    obtain ⟨h1', h2'⟩ := List.append_inj hxy (by rw [hxl, hyl])
    refine Prod.ext h1' ?_
    rw [← List.take_append_drop j x.2, ← List.take_append_drop j y.2, h2', ← hx.2.2.1,
      ← hy.2.2.1]

/-- The derivation-path count: `Σ_{w₂ ∈ L(q)} |L(q^{w₁,w₂})| ≤ (i+1)|L(q)|`.

INTERNAL: the bound on `N_{b,0}` of analysis.tex:676-686.
TEXLINE: analysis.tex:676-686 -/
theorem sum_langCount_dv_le (A : PaperNFA Q) (σ : Selector A) (q : Q) (i : ℕ) (w1 : List Bool)
    (h1 : w1 ∈ lang A i q) :
    ∑ w2 ∈ lang A i q, (langCount A (dv σ q i w1 w2) (canon σ q w1 (dv σ q i w1 w2)) : ℝ) ≤
      (i + 1) * (lang A i q).card := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun w2 => dv σ q i w1 w2) (t := Finset.range (i + 1))
    fun w2 _ => Finset.mem_range.2 (Nat.lt_succ_of_le (dv_le σ q i w1 w2))]
  calc ∑ j ∈ Finset.range (i + 1), ∑ w2 ∈ (lang A i q).filter (fun w2 => dv σ q i w1 w2 = j),
        (langCount A (dv σ q i w1 w2) (canon σ q w1 (dv σ q i w1 w2)) : ℝ)
      ≤ ∑ j ∈ Finset.range (i + 1), ∑ w2 ∈ (lang A i q).filter (fun w2 => agree σ q w1 w2 j),
          (langCount A j (canon σ q w1 j) : ℝ) := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [Finset.mem_range] at hj
        calc _ = ∑ w2 ∈ (lang A i q).filter (fun w2 => dv σ q i w1 w2 = j),
              (langCount A j (canon σ q w1 j) : ℝ) :=
              Finset.sum_congr rfl fun w2 hw2 => by rw [(Finset.mem_filter.1 hw2).2]
          _ ≤ _ := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
              intro w2 hw2
              rw [Finset.mem_filter] at hw2 ⊢
              exact ⟨hw2.1, (agree_iff_le_dv A σ q i w1 w2 h1 hw2.1 j (by omega)).2 hw2.2.ge⟩
    _ ≤ ∑ j ∈ Finset.range (i + 1), ((lang A i q).card : ℝ) := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [Finset.mem_range] at hj
        rw [Finset.sum_const, nsmul_eq_mul, ← card_lang]
        exact_mod_cast card_agree_mul_le A σ q i w1 j (by omega)
    _ = (i + 1) * (lang A i q).card := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

end Nfa.Analysis.CanonPathAux

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · canonical runs, divergence layer, derivation-path count
-/
