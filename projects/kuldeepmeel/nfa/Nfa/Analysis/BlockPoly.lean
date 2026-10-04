import Nfa.Analysis.CanonPath
import Nfa.Analysis.PolyOn

/-!
# The block polynomials `N_{b,j} + V_{b,j}`

For a top state `q ∈ Q^i`, a layer `j ≤ i` and a block `R_b` of repetitions,
`blockP … j s R_b x` is the paper's `N_{b,j} + V_{b,j}` (analysis.tex:638-660) as a
polynomial in the atoms `x` of layer `j`, with the coefficients `p(q^{w₁,w₂})` read in `s`;
`phiP` is `∏_{b ∈ F}` of these.  Proved here, all algebra:

* `phiP_polyOn` — it is multiaffine, distinct blocks reading disjoint atoms;
* `phiP_subst` — substituting the child atoms of layer `j − 1` gives `phiP` at `j − 1`
  (the algebraic content of lemma induction_lemma, including the `L_{j−1}` case);
* `phiP_zero_le` — at layer `0`, `0 ≤ N_{b,0} ≤ β(i+1)|L(q)|²/(1−ε)` (analysis.tex:672-690);
* `blockP_dom` — `β²(Y_{q,b} − |L(q)|)² ≤ N̂_{b,i} + V̂_{b,i}` under the spirit's floors
  (analysis.tex:619-636).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nfa.Analysis.BlockPolyAux
open Nfa.Pseudocode SpiritMomentsAux CanonPathAux PolyOnAux

variable {Q : Type} [Fintype Q] [LinearOrder Q]

/-- The atom index of `(r, w)` at layer `j`: `(r, w^j, q^j_w)`.

INTERNAL: the atoms `A_r(w,q,j) = A_r(w^j, q^j_w)` of analysis.tex:203-205.
TEXLINE: analysis.tex:203-205 -/
noncomputable def atomIdx {A : PaperNFA Q} (σ : Selector A) (q : Q) (j r : ℕ) (w : List Bool) :
    ℕ × List Bool × Q :=
  (r, w.take j, canon σ q w j)

/-- `|L(q^{w₁,w₂})|/(1−ε)`.

INTERNAL: the coefficient of `C_r` (analysis.tex:205-215).
TEXLINE: analysis.tex:205-215 -/
noncomputable def kap (A : PaperNFA Q) (σ : Selector A) (q : Q) (i : ℕ) (ε : ℝ)
    (w1 w2 : List Bool) : ℝ :=
  (langCount A (dv σ q i w1 w2) (canon σ q w1 (dv σ q i w1 w2)) : ℝ) / (1 - ε)

/-- `p(q^{w₁,w₂})`, read in `s`.

INTERNAL: the coefficient of `C_r` (analysis.tex:205-215).
TEXLINE: analysis.tex:205-215 -/
noncomputable def pdv {A : PaperNFA Q} (σ : Selector A) (q : Q) (i : ℕ) (s : CoreState Q)
    (w1 w2 : List Bool) : ℝ :=
  s.p (dv σ q i w1 w2) (canon σ q w1 (dv σ q i w1 w2))

/-- `C_r(w₁,w₂,q,j)·A_r(w₂,q,j)` as a polynomial in the atoms `x` of layer `j` (with the case
labels of analysis.tex:205-215 in the order lemma expectation_of_C_A_terms uses them).

INTERNAL: the terms of `N_{b,j}`.
TEXLINE: analysis.tex:205-215 -/
noncomputable def termP (A : PaperNFA Q) (σ : Selector A) (q : Q) (i : ℕ) (ε : ℝ) (j : ℕ)
    (s : CoreState Q) (r : ℕ) (w1 w2 : List Bool) (x : ℕ × List Bool × Q → ℝ) : ℝ :=
  if dv σ q i w1 w2 < j then
    (kap A σ q i ε w1 w2 * pdv σ q i s w1 w2 * x (atomIdx σ q j r w1) - 1) *
      x (atomIdx σ q j r w2)
  else (kap A σ q i ε w1 w2 - 1) * x (atomIdx σ q j r w2)

/-- `N_{b,j} + V_{b,j}` for the block of repetitions `B`, as a polynomial in the atoms.

INTERNAL: the per-block quantity of analysis.tex:638-660.
TEXLINE: analysis.tex:638-660 -/
noncomputable def blockP (A : PaperNFA Q) (σ : Selector A) (q : Q) (i : ℕ) (ε : ℝ) (j : ℕ)
    (s : CoreState Q) (B : Finset ℕ) (x : ℕ × List Bool × Q → ℝ) : ℝ :=
  (∑ r ∈ B, ∑ w1 ∈ lang A i q, ∑ w2 ∈ lang A i q, termP A σ q i ε j s r w1 w2 x)
  - (∑ r ∈ B, ∑ w1 ∈ lang A i q, ∑ w2 ∈ lang A i q, (x (atomIdx σ q j r w1) - 1))
  + ∑ r1 ∈ B, ∑ r2 ∈ B.erase r1, ∑ w1 ∈ lang A i q, ∑ w2 ∈ lang A i q,
      (x (atomIdx σ q j r1 w1) - 1) * (x (atomIdx σ q j r2 w2) - 1)

/-- The atoms of `B` at layer `j`.

INTERNAL: bookkeeping.
TEXLINE: analysis.tex:551-692 -/
noncomputable def blockAtoms {A : PaperNFA Q} (σ : Selector A) (q : Q) (i j : ℕ) (B : Finset ℕ) :
    Finset (ℕ × List Bool × Q) :=
  (B ×ˢ lang A i q).image fun p => atomIdx σ q j p.1 p.2

/-- Block atoms are block atoms.

INTERNAL: bookkeeping.
TEXLINE: analysis.tex:551-692 -/
theorem atomIdx_mem {A : PaperNFA Q} (σ : Selector A) (q : Q) (i j : ℕ) (B : Finset ℕ) (r : ℕ)
    (hr : r ∈ B) (w : List Bool) (hw : w ∈ lang A i q) : atomIdx σ q j r w ∈ blockAtoms σ q i j B :=
  Finset.mem_image.2 ⟨(r, w), Finset.mem_product.2 ⟨hr, hw⟩, rfl⟩

/-- Distinct divergence below `j` gives distinct atoms at `j`.

INTERNAL: bookkeeping.
TEXLINE: analysis.tex:551-692 -/
theorem atomIdx_ne (A : PaperNFA Q) (σ : Selector A) (q : Q) (i j r : ℕ) (w1 w2 : List Bool)
    (h1 : w1 ∈ lang A i q) (h2 : w2 ∈ lang A i q) (hj : j ≤ i) (hdv : dv σ q i w1 w2 < j) :
    atomIdx σ q j r w1 ≠ atomIdx σ q j r w2 := by
  intro h
  simp only [atomIdx, Prod.mk.injEq, true_and] at h
  have := (agree_iff_le_dv A σ q i w1 w2 h1 h2 j hj).1 h
  omega

/-- `N_{b,j} + V_{b,j}` is multiaffine in the atoms of its block.

INTERNAL: the conditional factorisation of analysis.tex:701-711.
TEXLINE: analysis.tex:701-711 -/
theorem blockP_polyOn (A : PaperNFA Q) (σ : Selector A) (q : Q) (i : ℕ) (ε : ℝ) (j : ℕ)
    (hj : j ≤ i) (s : CoreState Q) (B : Finset ℕ) :
    PolyOn (blockAtoms σ q i j B) (blockP A σ q i ε j s B) := by
  classical
  have hvar : ∀ r ∈ B, ∀ w ∈ lang A i q,
      PolyOn (blockAtoms σ q i j B) fun x => x (atomIdx σ q j r w) :=
    fun r hr w hw => PolyOn.var (atomIdx_mem σ q i j B r hr w hw)
  have hvar1 : ∀ r ∈ B, ∀ w ∈ lang A i q,
      PolyOn {atomIdx σ q j r w} fun x => x (atomIdx σ q j r w) - 1 :=
    fun r _ w _ => (PolyOn.var (Finset.mem_singleton_self _)).sub (PolyOn.const _ 1)
  have hsub : ∀ r ∈ B, ∀ w ∈ lang A i q, {atomIdx σ q j r w} ⊆ blockAtoms σ q i j B :=
    fun r hr w hw => Finset.singleton_subset_iff.2 (atomIdx_mem σ q i j B r hr w hw)
  unfold blockP
  refine (PolyOn.sub ?_ ?_).add ?_
  · refine PolyOn.sum _ fun r hr => PolyOn.sum _ fun w1 hw1 => PolyOn.sum _ fun w2 hw2 => ?_
    unfold termP
    split_ifs with hdv
    · have hm := ((PolyOn.var (Finset.mem_singleton_self (atomIdx σ q j r w1))).smul
        (kap A σ q i ε w1 w2 * pdv σ q i s w1 w2)).sub (PolyOn.const _ 1) |>.mul
        (PolyOn.var (Finset.mem_singleton_self (atomIdx σ q j r w2)))
        (Finset.disjoint_singleton.2 (atomIdx_ne A σ q i j r w1 w2 hw1 hw2 hj hdv))
      exact (hm.mono (Finset.union_subset (hsub r hr w1 hw1) (hsub r hr w2 hw2)))
    · exact (hvar r hr w2 hw2).smul _
  · exact PolyOn.sum _ fun r hr => PolyOn.sum _ fun w1 hw1 => PolyOn.sum _ fun w2 _ =>
      (hvar1 r hr w1 hw1).mono (hsub r hr w1 hw1)
  · refine PolyOn.sum _ fun r1 hr1 => PolyOn.sum _ fun r2 hr2 => PolyOn.sum _ fun w1 hw1 =>
      PolyOn.sum _ fun w2 hw2 => ?_
    have hr2' := Finset.mem_of_mem_erase hr2
    have hne : atomIdx σ q j r1 w1 ≠ atomIdx σ q j r2 w2 := by
      intro h
      simp only [atomIdx, Prod.mk.injEq] at h
      exact (Finset.ne_of_mem_erase hr2) h.1.symm
    exact ((hvar1 r1 hr1 w1 hw1).mul (hvar1 r2 hr2' w2 hw2)
      (Finset.disjoint_singleton.2 hne)).mono
      (Finset.union_subset (hsub r1 hr1 w1 hw1) (hsub r2 hr2' w2 hw2))


/-- The `b`-th block of repetitions, `{βb, …, βb+β−1}` (`R_b`, analysis.tex:390-392).

INTERNAL: bookkeeping.
TEXLINE: analysis.tex:390-392 -/
def blk (P : Params) (b : ℕ) : Finset ℕ := (Finset.range P.β).image fun r => P.β * b + r

/-- Membership in a block.

INTERNAL: bookkeeping.
TEXLINE: analysis.tex:390-392 -/
theorem mem_blk (P : Params) (b r : ℕ) : r ∈ blk P b ↔ P.β * b ≤ r ∧ r < P.β * b + P.β := by
  unfold blk
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨r', hr', rfl⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨r - P.β * b, by omega, by omega⟩

/-- Blocks are disjoint.

INTERNAL: bookkeeping.
TEXLINE: analysis.tex:390-392 -/
theorem blk_disjoint (P : Params) (b b' : ℕ) (h : b ≠ b') : Disjoint (blk P b) (blk P b') := by
  rw [Finset.disjoint_left]
  intro r hr hr'
  rw [mem_blk] at hr hr'
  rcases Nat.lt_or_gt_of_ne h with h | h
  · have : P.β * (b + 1) ≤ P.β * b' := Nat.mul_le_mul_left _ h
    rw [Nat.mul_succ] at this; omega
  · have : P.β * (b' + 1) ≤ P.β * b := Nat.mul_le_mul_left _ h
    rw [Nat.mul_succ] at this; omega

/-- `∏_{b ∈ F} (N_{b,j} + V_{b,j})`, as a polynomial in the atoms of layer `j`.

INTERNAL: the quantity of lemma induction_lemma.
TEXLINE: analysis.tex:663-669 -/
noncomputable def phiP (A : PaperNFA Q) (σ : Selector A) (q : Q) (i : ℕ) (ε : ℝ) (P : Params)
    (F : Finset (Fin P.γ)) (j : ℕ) (s : CoreState Q) (x : ℕ × List Bool × Q → ℝ) : ℝ :=
  ∏ b ∈ F, blockP A σ q i ε j s (blk P b) x

/-- The atoms the blocks of `F` read at layer `j`.

INTERNAL: bookkeeping.
TEXLINE: analysis.tex:551-692 -/
noncomputable def phiAtoms {A : PaperNFA Q} (σ : Selector A) (q : Q) (i : ℕ) (P : Params)
    (F : Finset (Fin P.γ)) (j : ℕ) : Finset (ℕ × List Bool × Q) :=
  F.biUnion fun b => blockAtoms σ q i j (blk P b)

/-- `∏_b (N_{b,j} + V_{b,j})` is multiaffine (blocks read disjoint atoms).

INTERNAL: the conditional independence across blocks of analysis.tex:701-711.
TEXLINE: analysis.tex:701-711 -/
theorem phiP_polyOn (A : PaperNFA Q) (σ : Selector A) (q : Q) (i : ℕ) (ε : ℝ) (P : Params)
    (F : Finset (Fin P.γ)) (j : ℕ) (hj : j ≤ i) (s : CoreState Q) :
    PolyOn (phiAtoms σ q i P F j) (phiP A σ q i ε P F j s) := by
  unfold phiP phiAtoms
  refine PolyOn.prod F (fun b => blockAtoms σ q i j (blk P b))
    (fun b _ => blockP_polyOn A σ q i ε j hj s _) ?_
  intro b _ b' _ hbb'
  rw [Finset.disjoint_left]
  intro e he he'
  unfold blockAtoms at he he'
  rw [Finset.mem_image] at he he'
  obtain ⟨p, hp, rfl⟩ := he
  obtain ⟨p', hp', hpp'⟩ := he'
  rw [Finset.mem_product] at hp hp'
  simp only [atomIdx, Prod.mk.injEq] at hpp'
  exact Finset.disjoint_left.1 (blk_disjoint P b b' (fun h => hbb' (Fin.ext h))) hp.1
    (hpp'.1 ▸ hp'.1)

/-- Only the estimates of layers `< j` enter the coefficients.

INTERNAL: `p(q^{w₁,w₂})` is fixed by `𝓕_j`.
TEXLINE: analysis.tex:701-704 -/
theorem phiP_congr (A : PaperNFA Q) (σ : Selector A) (q : Q) (i : ℕ) (ε : ℝ) (P : Params)
    (F : Finset (Fin P.γ)) (j : ℕ) (s s' : CoreState Q) (h : ∀ d < j, s'.p d = s.p d)
    (x : ℕ × List Bool × Q → ℝ) : phiP A σ q i ε P F j s' x = phiP A σ q i ε P F j s x := by
  unfold phiP blockP termP
  refine Finset.prod_congr rfl fun b _ => ?_
  congr 1; congr 1
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun w1 _ =>
    Finset.sum_congr rfl fun w2 _ => ?_
  split_ifs with hdv
  · unfold pdv; rw [h _ hdv]
  · rfl

/-- **The step of lemma induction_lemma, algebraically**: substituting the child atoms
into `C·A` at layer `j` gives `C·A` at layer `j − 1` (the case `(w₁,w₂) ∈ L_{j−1}` uses
`p·A² = A`).

INTERNAL: lemma expectation_of_C_A_terms, after the expectations are taken.
TEXLINE: analysis.tex:320-370 -/
theorem termP_subst (A : PaperNFA Q) (σ : Selector A) (q : Q) (i : ℕ) (ε : ℝ) (j : ℕ)
    (hj : 1 ≤ j) (hji : j ≤ i) (s : CoreState Q)
    (hp : ∀ c ∈ layerSet A (j - 1), s.p (j - 1) c ≠ 0) (r : ℕ) (w1 w2 : List Bool)
    (h1 : w1 ∈ lang A i q) (h2 : w2 ∈ lang A i q) (x : ℕ × List Bool × Q → ℝ)
    (hx : ∀ w ∈ lang A i q, x (atomIdx σ q j r w) = atomVal s (j - 1) (atomIdx σ q (j - 1) r w)) :
    termP A σ q i ε j s r w1 w2 x = termP A σ q i ε (j - 1) s r w1 w2 (atomVal s (j - 1)) := by
  unfold termP
  rw [hx w1 h1, hx w2 h2]
  by_cases hlt : dv σ q i w1 w2 < j - 1
  · rw [if_pos (by omega), if_pos hlt]
  by_cases heq : dv σ q i w1 w2 = j - 1
  · rw [if_pos (by omega), if_neg hlt]
    have hag : atomIdx σ q (j - 1) r w1 = atomIdx σ q (j - 1) r w2 := by
      have := (agree_iff_le_dv A σ q i w1 w2 h1 h2 (j - 1) (by omega)).2 heq.ge
      simp only [atomIdx, Prod.mk.injEq, true_and]
      exact this
    rw [hag]
    have hpdv : pdv σ q i s w1 w2 = s.p (j - 1) (canon σ q w2 (j - 1)) := by
      unfold pdv
      rw [heq]
      have := (agree_iff_le_dv A σ q i w1 w2 h1 h2 (j - 1) (by omega)).2 heq.ge
      rw [this.2]
    have hmem : canon σ q w2 (j - 1) ∈ layerSet A (j - 1) := by
      have h2' := (mem_lang A i q w2).1 h2
      have := canon_mem_eval A σ w2 q h2'.2 (j - 1) (by omega)
      unfold layerSet
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨_, by simp; omega, this⟩
    have hp0 := hp _ hmem
    rw [hpdv]
    unfold atomVal atomIdx
    simp only
    split_ifs
    · field_simp
    · ring
  · rw [if_neg (by omega), if_neg hlt]


/-- Substitution, block by block.

INTERNAL: lemma induction_lemma.
TEXLINE: analysis.tex:695-719 -/
theorem blockP_subst (A : PaperNFA Q) (σ : Selector A) (q : Q) (i : ℕ) (ε : ℝ) (j : ℕ)
    (hj : 1 ≤ j) (hji : j ≤ i) (s : CoreState Q)
    (hp : ∀ c ∈ layerSet A (j - 1), s.p (j - 1) c ≠ 0) (B : Finset ℕ) (x : ℕ × List Bool × Q → ℝ)
    (hx : ∀ r ∈ B, ∀ w ∈ lang A i q,
      x (atomIdx σ q j r w) = atomVal s (j - 1) (atomIdx σ q (j - 1) r w)) :
    blockP A σ q i ε j s B x = blockP A σ q i ε (j - 1) s B (atomVal s (j - 1)) := by
  unfold blockP
  congr 1; congr 1
  · refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun w1 h1 =>
      Finset.sum_congr rfl fun w2 h2 => ?_
    exact termP_subst A σ q i ε j hj hji s hp r w1 w2 h1 h2 x (hx r hr)
  · refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun w1 h1 =>
      Finset.sum_congr rfl fun w2 _ => ?_
    rw [hx r hr w1 h1]
  · refine Finset.sum_congr rfl fun r1 hr1 => Finset.sum_congr rfl fun r2 hr2 =>
      Finset.sum_congr rfl fun w1 h1 => Finset.sum_congr rfl fun w2 h2 => ?_
    rw [hx r1 hr1 w1 h1, hx r2 (Finset.mem_of_mem_erase hr2) w2 h2]

/-- Substitution in `∏_b (N_{b,j} + V_{b,j})`.

INTERNAL: lemma induction_lemma.
TEXLINE: analysis.tex:695-719 -/
theorem phiP_subst (A : PaperNFA Q) (σ : Selector A) (q : Q) (i : ℕ) (ε : ℝ) (P : Params)
    (F : Finset (Fin P.γ)) (j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) (s : CoreState Q)
    (hp : ∀ c ∈ layerSet A (j - 1), s.p (j - 1) c ≠ 0) (x : ℕ × List Bool × Q → ℝ)
    (hx : ∀ r w, w ∈ lang A i q →
      x (atomIdx σ q j r w) = atomVal s (j - 1) (atomIdx σ q (j - 1) r w)) :
    phiP A σ q i ε P F j s x = phiP A σ q i ε P F (j - 1) s (atomVal s (j - 1)) := by
  unfold phiP
  exact Finset.prod_congr rfl fun b _ =>
    blockP_subst A σ q i ε j hj hji s hp _ x fun r _ w hw => hx r w hw

/-- The child atoms of layer `j` are the atoms of layer `j − 1` along the canonical runs.

INTERNAL: the canonical child of lemma expectation_of_singleton.
TEXLINE: analysis.tex:221-224 -/
theorem childAtom_atomIdx (A : PaperNFA Q) (σ : Selector A) (q : Q) (i : ℕ) (j : ℕ)
    (hj : 1 ≤ j) (hji : j ≤ i) (s : CoreState Q) (r : ℕ) (w : List Bool) (hw : w ∈ lang A i q) :
    childAtom σ s j r (canon σ q w j) (w.take j) = atomVal s (j - 1) (atomIdx σ q (j - 1) r w) := by
  have hl := ((mem_lang A i q w).1 hw).1
  have hc := canon_pred A σ w q j hj (by omega)
  have hd : (w.take j).dropLast = w.take (j - 1) := by
    rw [List.dropLast_eq_take, List.take_take, List.length_take]
    congr 1
    omega
  unfold childAtom atomVal atomIdx
  simp only
  rw [hd, ← hc]


/-- `|R_b| = β`.

INTERNAL: bookkeeping.
TEXLINE: analysis.tex:390-392 -/
theorem card_blk (P : Params) (b : ℕ) : (blk P b).card = P.β := by
  unfold blk
  rw [Finset.card_image_of_injective _ fun x y h => by simpa using h, Finset.card_range]

/-- Canonical runs start at `q_I`.

INTERNAL: bookkeeping.
TEXLINE: analysis.tex:187-194 -/
theorem canon_zero (A : PaperNFA Q) (σ : Selector A) (q : Q) (i : ℕ) (w : List Bool)
    (hw : w ∈ lang A i q) : canon σ q w 0 = A.qI := by
  have := canon_mem_eval A σ w q ((mem_lang A i q w).1 hw).2 0 (Nat.zero_le _)
  simpa [NFA.eval_nil, PaperNFA.toNFA] using this

/-- At the top layer the atoms are `(r, w, q)`.

INTERNAL: bookkeeping.
TEXLINE: analysis.tex:551-692 -/
theorem atomIdx_top (A : PaperNFA Q) (σ : Selector A) (q : Q) (i r : ℕ) (w : List Bool)
    (hw : w ∈ lang A i q) : atomIdx σ q i r w = (r, w, q) := by
  have hl := ((mem_lang A i q w).1 hw).1
  simp [atomIdx, List.take_of_length_le hl.le, canon_of_le σ q w i hl.le]

/-- `Σ_{w₂} κ(w₁,w₂)` lies between `|L(q)|` and `(i+1)|L(q)|/(1−ε)`.

INTERNAL: the bound on `N_{b,0}`.
TEXLINE: analysis.tex:676-686 -/
theorem sum_kap_bounds (A : PaperNFA Q) (σ : Selector A) (q : Q) (i : ℕ) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (w1 : List Bool) (h1 : w1 ∈ lang A i q) :
    ((lang A i q).card : ℝ) ≤ ∑ w2 ∈ lang A i q, kap A σ q i ε w1 w2 ∧
      ∑ w2 ∈ lang A i q, kap A σ q i ε w1 w2 ≤ (i + 1) * (lang A i q).card / (1 - ε) := by
  have h1ε : 0 < 1 - ε := by linarith
  unfold kap
  rw [← Finset.sum_div]
  constructor
  · rw [le_div_iff₀ h1ε]
    have hl := ((mem_lang A i q w1).1 h1).1
    have hself : (langCount A (dv σ q i w1 w1) (canon σ q w1 (dv σ q i w1 w1)) : ℝ) =
        (lang A i q).card := by
      rw [(dv_eq_iff A σ q i w1 w1 h1 h1).2 rfl, canon_of_le σ q w1 i hl.le, card_lang]
    calc ((lang A i q).card : ℝ) * (1 - ε) ≤ (lang A i q).card := by
          have : (0 : ℝ) ≤ (lang A i q).card := by positivity
          nlinarith
      _ = _ := hself.symm
      _ ≤ _ := Finset.single_le_sum (f := fun w2 =>
          (langCount A (dv σ q i w1 w2) (canon σ q w1 (dv σ q i w1 w2)) : ℝ))
          (fun _ _ => by positivity) h1
  · exact div_le_div_of_nonneg_right (sum_langCount_dv_le A σ q i w1 h1) h1ε.le

/-- **The base of the induction** (analysis.tex:672-690): at layer `0` every atom is `1`,
`V_{b,0} = 0`, and `0 ≤ N_{b,0} ≤ β(i+1)|L(q)|²/(1−ε)`.

INTERNAL: the end of the induction.
TEXLINE: analysis.tex:672-690 -/
theorem phiP_zero_le (A : PaperNFA Q) (σ : Selector A) (q : Q) (i : ℕ) (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1) (P : Params) (hα : P.α = P.β * P.γ) (F : Finset (Fin P.γ)) :
    phiP A σ q i ε P F 0 (initState A P) (atomVal (initState A P) 0) ≤
      ((P.β : ℝ) * ((i + 1) * (lang A i q).card ^ 2 / (1 - ε))) ^ F.card := by
  have h1ε : 0 < 1 - ε := by linarith
  have hone : ∀ (b : Fin P.γ), ∀ r ∈ blk P b, ∀ w ∈ lang A i q,
      atomVal (initState A P) 0 (atomIdx σ q 0 r w) = 1 := by
    intro b r hr w hw
    have hrα : r < P.α := by
      rw [mem_blk] at hr
      have : P.β * (b + 1) ≤ P.β * P.γ := Nat.mul_le_mul_left _ b.2
      rw [Nat.mul_succ] at this
      omega
    simp [atomVal, atomIdx, canon_zero A σ q i w hw, initState, hrα]
  have hblock : ∀ b : Fin P.γ,
      blockP A σ q i ε 0 (initState A P) (blk P b) (atomVal (initState A P) 0) =
        ∑ r ∈ blk P b, ∑ w1 ∈ lang A i q, ∑ w2 ∈ lang A i q, (kap A σ q i ε w1 w2 - 1) := by
    intro b
    unfold blockP termP
    have h1 : ∑ r ∈ blk P b, ∑ w1 ∈ lang A i q, ∑ w2 ∈ lang A i q,
        (atomVal (initState A P) 0 (atomIdx σ q 0 r w1) - 1) = 0 :=
      Finset.sum_eq_zero fun r hr => Finset.sum_eq_zero fun w1 h1 =>
        Finset.sum_eq_zero fun w2 _ => by rw [hone b r hr w1 h1]; ring
    have h2 : ∑ r1 ∈ blk P b, ∑ r2 ∈ (blk P b).erase r1, ∑ w1 ∈ lang A i q, ∑ w2 ∈ lang A i q,
        (atomVal (initState A P) 0 (atomIdx σ q 0 r1 w1) - 1) *
          (atomVal (initState A P) 0 (atomIdx σ q 0 r2 w2) - 1) = 0 :=
      Finset.sum_eq_zero fun r1 hr1 => Finset.sum_eq_zero fun r2 _ =>
        Finset.sum_eq_zero fun w1 h1 => Finset.sum_eq_zero fun w2 _ => by
          rw [hone b r1 hr1 w1 h1]; ring
    rw [h1, h2, sub_zero, add_zero]
    refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun w1 _ =>
      Finset.sum_congr rfl fun w2 h2 => ?_
    rw [if_neg (Nat.not_lt_zero _), hone b r hr w2 h2, mul_one]
  have hL : (0 : ℝ) ≤ (lang A i q).card := by positivity
  have hbounds : ∀ b : Fin P.γ,
      0 ≤ blockP A σ q i ε 0 (initState A P) (blk P b) (atomVal (initState A P) 0) ∧
      blockP A σ q i ε 0 (initState A P) (blk P b) (atomVal (initState A P) 0) ≤
        (P.β : ℝ) * ((i + 1) * (lang A i q).card ^ 2 / (1 - ε)) := by
    intro b
    rw [hblock b, Finset.sum_const, card_blk, nsmul_eq_mul]
    have hin : ∀ w1 ∈ lang A i q, 0 ≤ ∑ w2 ∈ lang A i q, (kap A σ q i ε w1 w2 - 1) ∧
        ∑ w2 ∈ lang A i q, (kap A σ q i ε w1 w2 - 1) ≤
          (i + 1) * (lang A i q).card / (1 - ε) := by
      intro w1 h1
      obtain ⟨hlo, hhi⟩ := sum_kap_bounds A σ q i ε hε0 hε1 w1 h1
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
      constructor
      · linarith
      · linarith
    have hβ : (0 : ℝ) ≤ P.β := by positivity
    constructor
    · exact mul_nonneg hβ (Finset.sum_nonneg fun w1 h1 => (hin w1 h1).1)
    · refine mul_le_mul_of_nonneg_left ?_ hβ
      calc ∑ w1 ∈ lang A i q, ∑ w2 ∈ lang A i q, (kap A σ q i ε w1 w2 - 1)
          ≤ ∑ w1 ∈ lang A i q, ((i + 1) * (lang A i q).card / (1 - ε)) :=
            Finset.sum_le_sum fun w1 h1 => (hin w1 h1).2
        _ = (i + 1) * (lang A i q).card ^ 2 / (1 - ε) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
  unfold phiP
  calc ∏ b ∈ F, blockP A σ q i ε 0 (initState A P) (blk P b) (atomVal (initState A P) 0)
      ≤ ∏ b ∈ F, ((P.β : ℝ) * ((i + 1) * (lang A i q).card ^ 2 / (1 - ε))) :=
        Finset.prod_le_prod (fun b _ => (hbounds b).1) fun b _ => (hbounds b).2
    _ = _ := Finset.prod_const _


/-- The hatted atom `Â_r(w, q) = 1_{w ∈ hat S^r(q)}/ρ(q)`.

INTERNAL: the atoms of analysis.tex:180-183.
TEXLINE: analysis.tex:180-183 -/
noncomputable def hatVal (H : ℕ → Finset (List Bool)) (ρ : ℝ) (e : ℕ × List Bool × Q) : ℝ :=
  if e.2.1 ∈ H e.1 then 1 / ρ else 0

/-- `β(Y_{q,b} − |L(q)|) = Σ_{r ∈ R_b, w ∈ L(q)} (Â_r(w,q) − 1)`.

INTERNAL: the block mean in atoms (analysis.tex:394-398).
TEXLINE: analysis.tex:394-398 -/
theorem blockMean_sub (A : PaperNFA Q) (σ : Selector A) (q : Q) (i : ℕ) (P : Params)
    (hβ : 0 < P.β) (H : ℕ → Finset (List Bool)) (hH : ∀ r, H r ⊆ lang A i q) (ρ : ℝ)
    (hρ : 0 < ρ) (b : ℕ) :
    (P.β : ℝ) * (blockMean P ρ H b - (lang A i q).card) =
      ∑ r ∈ blk P b, ∑ w ∈ lang A i q, (hatVal H ρ (atomIdx σ q i r w) - 1) := by
  classical
  have hrow : ∀ r, ∑ w ∈ lang A i q, (hatVal H ρ (atomIdx σ q i r w) - 1) =
      ((H r).card : ℝ) / ρ - (lang A i q).card := by
    intro r
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1
    have : ∀ w ∈ lang A i q, hatVal H ρ (atomIdx σ q i r w) = if w ∈ H r then 1 / ρ else 0 :=
      fun w hw => by rw [atomIdx_top A σ q i r w hw]; rfl
    rw [Finset.sum_congr rfl this, Finset.sum_ite_mem, Finset.inter_eq_right.2 (hH r),
      Finset.sum_const, nsmul_eq_mul]
    ring
  simp_rw [hrow]
  unfold blk blockMean
  rw [Finset.sum_image fun x _ y _ h => by simpa using h]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

/-- **Domination** (analysis.tex:619-636): with the spirit's floors,
`β²(Y_{q,b} − |L(q)|)² ≤ N̂_{b,i} + V̂_{b,i}`.

INTERNAL: the domination step; the paper's "`β(Y − |L(q)|)²`" at eq. many_sums is `β²(…)²`.
TEXLINE: analysis.tex:619-636 -/
theorem blockP_dom (A : PaperNFA Q) (σ : Selector A) (q : Q) (i : ℕ) (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1) (P : Params) (hβ : 0 < P.β) (s : CoreState Q)
    (hfl : ∀ d < i, ∀ c ∈ layerSet A d, (1 - ε) / (langCount A d c : ℝ) ≤ s.p d c)
    (H : ℕ → Finset (List Bool)) (hH : ∀ r, H r ⊆ lang A i q) (ρ : ℝ)
    (hρ : (1 - ε) / ((lang A i q).card : ℝ) ≤ ρ) (hq : q ∈ layerSet A i) (b : ℕ) :
    (P.β : ℝ) ^ 2 * (blockMean P ρ H b - (lang A i q).card) ^ 2 ≤
      blockP A σ q i ε i s (blk P b) (hatVal H ρ) := by
  classical
  have h1ε : 0 < 1 - ε := by linarith
  have hLpos : (0 : ℝ) < (lang A i q).card := by
    rw [card_lang]; exact_mod_cast StarBadLeSpiritAux.langCount_pos' A i q hq
  have hρ0 : 0 < ρ := (div_pos h1ε hLpos).trans_le hρ
  set a : ℕ → List Bool → ℝ := fun r w => hatVal H ρ (atomIdx σ q i r w)
  have ha0 : ∀ r w, 0 ≤ a r w := fun r w => by
    simp only [a, hatVal]; split_ifs <;> positivity
  -- termwise domination of `Â₁Â₂ − Â₂`
  have hterm : ∀ r, ∀ w1 ∈ lang A i q, ∀ w2 ∈ lang A i q,
      a r w1 * a r w2 - a r w2 ≤ termP A σ q i ε i s r w1 w2 (hatVal H ρ) := by
    intro r w1 h1 w2 h2
    unfold termP
    split_ifs with hdv
    · set d := dv σ q i w1 w2
      set c := canon σ q w1 d
      have hcl : c ∈ layerSet A d := by
        have h1' := (mem_lang A i q w1).1 h1
        have := canon_mem_eval A σ w1 q h1'.2 d (by rw [h1'.1]; exact hdv.le)
        unfold layerSet
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨_, by simp; omega, this⟩
      have hLd : (0 : ℝ) < langCount A d c := by
        exact_mod_cast StarBadLeSpiritAux.langCount_pos' A d c hcl
      have hk : 1 ≤ kap A σ q i ε w1 w2 * pdv σ q i s w1 w2 := by
        have := hfl d hdv c hcl
        unfold kap pdv
        rw [div_mul_eq_mul_div, le_div_iff₀ h1ε]
        rw [div_le_iff₀ hLd] at this
        linarith
      have := mul_nonneg (ha0 r w1) (ha0 r w2)
      show a r w1 * a r w2 - a r w2 ≤ _
      nlinarith
    · have heq : w1 = w2 := (dv_eq_iff A σ q i w1 w2 h1 h2).1
        (le_antisymm (dv_le σ q i w1 w2) (not_lt.1 hdv))
      subst heq
      have hkap : kap A σ q i ε w1 w1 = (lang A i q).card / (1 - ε) := by
        have hl := ((mem_lang A i q w1).1 h1).1
        unfold kap
        rw [(dv_eq_iff A σ q i w1 w1 h1 h1).2 rfl, canon_of_le σ q w1 i hl.le, card_lang]
      show a r w1 * a r w1 - a r w1 ≤ _
      rw [hkap]
      have hval : a r w1 = 0 ∨ a r w1 = 1 / ρ := by
        simp only [a, hatVal]; split_ifs <;> simp
      have hle : 1 / ρ ≤ (lang A i q).card / (1 - ε) := by
        rw [div_le_div_iff₀ hρ0 h1ε, one_mul]
        rw [div_le_iff₀ hLpos] at hρ
        linarith
      rw [show hatVal H ρ (atomIdx σ q i r w1) = a r w1 from rfl]
      rcases hval with h | h
      · rw [h]; simp
      · rw [h]; nlinarith [hle, one_div_pos.2 hρ0]
  -- expand the square
  rw [← mul_pow, blockMean_sub A σ q i P hβ H hH ρ hρ0 b, sq, Finset.sum_mul_sum]
  unfold blockP
  have hsplit : ∀ r1 ∈ blk P b,
      ∑ r2 ∈ blk P b, (∑ w ∈ lang A i q, (a r1 w - 1)) * ∑ w ∈ lang A i q, (a r2 w - 1) =
        (∑ w1 ∈ lang A i q, ∑ w2 ∈ lang A i q, (a r1 w1 * a r1 w2 - a r1 w2)) -
          (∑ w1 ∈ lang A i q, ∑ w2 ∈ lang A i q, (a r1 w1 - 1)) +
          ∑ r2 ∈ (blk P b).erase r1, ∑ w1 ∈ lang A i q, ∑ w2 ∈ lang A i q,
            (a r1 w1 - 1) * (a r2 w2 - 1) := by
    intro r1 hr1
    rw [← Finset.add_sum_erase _ _ hr1, Finset.sum_mul_sum]
    simp_rw [Finset.sum_mul_sum]
    rw [← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun w1 _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun w2 _ => by ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  gcongr with r hr w1 h1 w2 h2
  exact hterm r w1 h1 w2 h2

end Nfa.Analysis.BlockPolyAux

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · block polynomials: multiaffinity, substitution, base, domination
-/
