import Nfa.Analysis.SpiritLaw
import Nfa.Model.Prior
import Nfa.Analysis.BlockPoly
import Nfa.Analysis.SpiritInv

/-!
# The joint second moment of the block means in `N^s`

`spirit_block_moment_le` is the moment bound inside the proof of
Lemma bound_proba_AND_event (analysis.tex:551-692): in the spirited algorithm `N^s`, at a
listed state `q ∈ Q^i` and for any set `F` of blocks,

  `E[∏_{b ∈ F} (Y_{q,b} − |L(q)|)²] ≤ ((n+1)|L(q)|² / ((1−ε)β))^{|F|}`.

The expectation is over `spiritMeans` (the run of `N^s` up to `q`, then the
`hat S^r(q)` draws), written as a `tsum` in `ℝ≥0∞`.

Proof — the paper's (analysis.tex:551-719):
* `β²(Y_{q,b} − |L(q)|)² = Σ_{r ∈ R_b, w₁, w₂} (Â_r(w₁)Â_r(w₂) − Â_r(w₂)) − Σ B̂_r(w₁) +
  Σ_{r₁ ≠ r₂} B̂_{r₁}(w₁)B̂_{r₂}(w₂)` with atoms `Â_r(w,q) = 1_{w ∈ hat S^r(q)}/ρ(q)`,
  `B̂ = Â − 1` (`BlockPolyAux.blockMean_sub`); the paper's "`β(Y − |L(q)|)²`" at
  eq. many_sums is a typo for `β²`.
* domination by `N̂_{b,i} + V̂_{b,i}` using the spirit's floor at the divergence node
  `q^{w₁,w₂}` (and `ρ(q) ≥ (1−ε)/|L(q)|`, eq. spirit_rho_floor, when `w₁ = w₂`).  The
  two cases in the definition of `Ĉ`/`C` (analysis.tex:205-215) are labelled the wrong
  way round relative to their use in lemma expectation_of_C_A_terms; the use is right
  (`BlockPolyAux.blockP_dom`).
* lemma induction_lemma (analysis.tex:695-719): conditional independence across blocks
  given `𝓕_j`, `hat 𝓕_j`, and lemmas expectation_of_singleton / _of_pair /
  _of_C_A_terms (analysis.tex:221-370), down to layer `0`, where `V_{b,0} = 0`.  Here:
  `∏_b (N_{b,j} + V_{b,j})` is a multiaffine polynomial in the atoms of layer `j`
  (`BlockPolyAux.phiP_polyOn`), every product of distinct atoms averages over one layer
  to the product of the child atoms (`SpiritMomentsAux.ex_layer_prod`, `ex_hatSamples_prod`),
  so the expectation is the polynomial at the child atoms (`PolyOnAux.ex_polyOn`), which
  is `∏_b (N_{b,j−1} + V_{b,j−1})` (`BlockPolyAux.phiP_subst`).
* `N_{b,0} ≤ β(n+1)|L(q)|²/(1−ε)` by `|D(w₁,j)|·|L(q^{w₁}_j)| ≤ |L(q)|`
  (derivationpath.tex:197-206; `CanonPathAux.sum_langCount_dv_le`, `BlockPolyAux.phiP_zero_le`).

In the Lean model the run is a fold over single states (`corePairs`), not over layers;
every state of layer `j` reads only layer `j−1`, so the layer filtrations `𝓕_j ⊂ hat 𝓕_j`
of the paper are the states of `spiritPrefix` at layer boundaries.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal

namespace Nfa.Analysis.SpiritBlockMomentAux
open Nfa.Pseudocode PmfExpect SpiritMomentsAux CanonPathAux PolyOnAux BlockPolyAux SpiritInvAux

variable {Q : Type} [Fintype Q] [LinearOrder Q]

/-- Running `as ++ bs` is running `as`, then `bs`.

INTERNAL: fold bookkeeping.
TEXLINE: analysis.tex:166-170 -/
theorem runSpirit_append (A : PaperNFA Q) (σ : Selector A) (P : Params) (ε : ℝ) :
    ∀ (as bs : List (ℕ × Q)) (st : CoreState Q),
      runSpirit A σ P ε st (as ++ bs) =
        (runSpirit A σ P ε st as).bind fun s => runSpirit A σ P ε s bs
  | [], bs, st => by simp [runSpirit]
  | x :: as, bs, st => by
      simp only [List.cons_append, runSpirit, PMF.bind_bind]
      congr 1
      funext s
      exact runSpirit_append A σ P ε as bs s

/-- Layers `1..j+1` are layers `1..j`, then layer `j+1`.

INTERNAL: the filtration `𝓕_j ⊂ hat 𝓕_j ⊂ 𝓕_{j+1}` as list structure.
TEXLINE: analysis.tex:166-170 -/
theorem corePairs_succ (A : PaperNFA Q) (j : ℕ) :
    corePairs A (j + 1) = corePairs A j ++ (layerList A (j + 1)).map fun q' => (j + 1, q') := by
  unfold corePairs
  rw [List.range'_1_concat, List.flatMap_append, List.flatMap_singleton, Nat.add_comm 1 j]

/-- Listed states lie in layers `≥ 1`.

INTERNAL: bookkeeping.
TEXLINE: algorithm.tex:97-100 -/
theorem one_le_of_mem_corePairs (A : PaperNFA Q) (n : ℕ) (y : ℕ × Q) (hy : y ∈ corePairs A n) :
    1 ≤ y.1 :=
  ((StarBadLeSpiritAux.mem_corePairs A n y.1 y.2).1 hy).1

/-- The floor gives positive estimates.

INTERNAL: bookkeeping.
TEXLINE: analysis.tex:76-86 -/
theorem p_pos_of_inv (A : PaperNFA Q) (ε : ℝ) (hε1 : ε < 1) (t : CoreState Q)
    (ht : SpiritInv A ε t) (ℓ : ℕ) (c : Q) (hc : c ∈ layerSet A ℓ) : 0 < t.p ℓ c := by
  have hL : (0 : ℝ) < langCount A ℓ c := by
    exact_mod_cast StarBadLeSpiritAux.langCount_pos' A ℓ c hc
  exact (div_pos (by linarith) hL).trans_le (ht.1 ℓ c hc)

/-- Atoms of `phiAtoms` at layer `j` are valid atoms of layer `j`.

INTERNAL: bookkeeping.
TEXLINE: analysis.tex:663-692 -/
theorem phiAtoms_valid (A : PaperNFA Q) (σ : Selector A) (q : Q) (i : ℕ) (P : Params)
    (hα : P.α = P.β * P.γ) (F : Finset (Fin P.γ)) (j : ℕ) (hji : j ≤ i) (e : ℕ × List Bool × Q)
    (he : e ∈ phiAtoms σ q i P F j) :
    e.1 < P.α ∧ e.2.1.length = j ∧ e.2.2 ∈ A.toNFA.eval e.2.1 ∧ e.2.2 ∈ layerSet A j := by
  unfold phiAtoms blockAtoms at he
  rw [Finset.mem_biUnion] at he
  obtain ⟨b, _, he⟩ := he
  rw [Finset.mem_image] at he
  obtain ⟨⟨r, w⟩, hrw, rfl⟩ := he
  rw [Finset.mem_product] at hrw
  have hw := (mem_lang A i q w).1 hrw.2
  have hev := canon_mem_eval A σ w q hw.2 j (by omega)
  refine ⟨?_, by simp [atomIdx]; omega, hev, ?_⟩
  · have hr := (mem_blk P b r).1 hrw.1
    have : P.β * (b + 1) ≤ P.β * P.γ := Nat.mul_le_mul_left _ b.2
    rw [Nat.mul_succ] at this
    simp only [atomIdx]; omega
  · unfold layerSet
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨_, by simp; omega, hev⟩

/-- **One layer of the induction** (lemma induction_lemma): the expectation of
`∏_b (N_{b,j} + V_{b,j})` over layer `j` of `N^s` is `∏_b (N_{b,j−1} + V_{b,j−1})`.

INTERNAL: lemma induction_lemma, both identities at once.
TEXLINE: analysis.tex:695-719 -/
theorem ex_layer_phi (A : PaperNFA Q) (σ : Selector A) (P : Params) (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1) (hα : P.α = P.β * P.γ) (q : Q) (i : ℕ) (F : Finset (Fin P.γ)) (j : ℕ)
    (hj : 1 ≤ j) (hji : j ≤ i) (t : CoreState Q) (ht : SpiritInv A ε t) :
    ex (runSpirit A σ P ε t ((layerList A j).map fun q' => (j, q')))
        (fun t' => phiP A σ q i ε P F j t' (atomVal t' j)) =
      phiP A σ q i ε P F (j - 1) t (atomVal t (j - 1)) := by
  set μ := runSpirit A σ P ε t ((layerList A j).map fun q' => (j, q'))
  have hμ : μ.support.Finite := runSpirit_support_finite _ _ _ _ _ _
  have hnot : ∀ d, d ≠ j → ∀ c, ((d, c) : ℕ × Q) ∉ (layerList A j).map fun q' => (j, q') := by
    intro d hd c h
    simp only [List.mem_map, Prod.mk.injEq] at h
    obtain ⟨_, _, h, _⟩ := h
    exact hd h.symm
  have hcongr : ∀ t' ∈ μ.support,
      phiP A σ q i ε P F j t' (atomVal t' j) = phiP A σ q i ε P F j t (atomVal t' j) := by
    intro t' ht'
    refine phiP_congr A σ q i ε P F j t t' (fun d hd => funext fun c => ?_) _
    exact StarBadLeSpiritAux.runSpirit_frame A σ P ε _ t t' ht' d c (hnot d (by omega) c)
  rw [ex_congr μ hcongr]
  rw [ex_polyOn μ hμ (fun t' => atomVal t' j) (fun e => childAtom σ t j e.1 e.2.2 e.2.1)
    (phiP_polyOn A σ q i ε P F j hji t) fun T hT => ?_]
  · refine phiP_subst A σ q i ε P F j hj hji t
      (fun c hc => (p_pos_of_inv A ε hε1 t ht _ c hc).ne') _ fun r w hw => ?_
    exact childAtom_atomIdx A σ q i j hj hji t r w hw
  · refine ex_layer_prod A σ P ε hε0 hε1 j hj (layerList A j) (Finset.sort_nodup _ _)
      (fun q' hq' => by simpa [layerList] using hq') t (fun c hc => ht.1 _ c hc) T ?_
    intro x hx
    obtain ⟨h1, h2, h3, h4⟩ := phiAtoms_valid A σ q i P hα F j hji x (hT hx)
    exact ⟨h1, h2, h3, by simpa [layerList] using h4⟩


/-- The law of `N^s` after layers `1, …, j`.

INTERNAL: the law of `𝓕_{j+1}`.
TEXLINE: analysis.tex:166-170 -/
noncomputable def lawUpTo (A : PaperNFA Q) (σ : Selector A) (P : Params) (ε : ℝ) (j : ℕ) :
    PMF (CoreState Q) :=
  runSpirit A σ P ε (initState A P) (corePairs A j)

/-- Reachable states after layers `1..j` satisfy the invariants.

INTERNAL: bookkeeping.
TEXLINE: analysis.tex:76-86 -/
theorem lawUpTo_inv (A : PaperNFA Q) (σ : Selector A) (P : Params) (ε : ℝ) (hε0 : 0 < ε)
    (j : ℕ) (t : CoreState Q) (ht : t ∈ (lawUpTo A σ P ε j).support) : SpiritInv A ε t :=
  runSpirit_inv A σ P ε _ (fun y hy => one_le_of_mem_corePairs A j y hy) _ t
    (initState_inv A P ε hε0) ht

/-- **The induction of analysis.tex:663-671**: `E[∏_b (N_{b,j} + V_{b,j})]` is the same at every
layer `j ≤ i`, down to its (deterministic) value at layer `0`.

INTERNAL: eq. down_to_zero.
TEXLINE: analysis.tex:663-671 -/
theorem ex_lawUpTo_phi (A : PaperNFA Q) (σ : Selector A) (P : Params) (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1) (hα : P.α = P.β * P.γ) (q : Q) (i : ℕ) (F : Finset (Fin P.γ)) :
    ∀ j ≤ i, ex (lawUpTo A σ P ε j) (fun t => phiP A σ q i ε P F j t (atomVal t j)) =
      phiP A σ q i ε P F 0 (initState A P) (atomVal (initState A P) 0)
  | 0, _ => by simp [lawUpTo, corePairs, runSpirit, ex_pure]
  | j + 1, hj => by
      have ih := ex_lawUpTo_phi A σ P ε hε0 hε1 hα q i F j (by omega)
      unfold lawUpTo
      rw [corePairs_succ, runSpirit_append, ex_bind _ _ (runSpirit_support_finite _ _ _ _ _ _)
        fun _ _ => runSpirit_support_finite _ _ _ _ _ _]
      rw [← ih]
      refine ex_congr _ fun t ht => ?_
      exact ex_layer_phi A σ P ε hε0 hε1 hα q i F (j + 1) (by omega) hj t
        (lawUpTo_inv A σ P ε hε0 j t ht)

/-- **The top step** (lemma induction_lemma at `j = i`, `hat 𝓕` side): averaging the hatted
`∏_b (N̂_{b,i} + V̂_{b,i})` over the `hat S^r(q)` gives `∏_b (N_{b,i−1} + V_{b,i−1})`.

INTERNAL: lemma induction_lemma at the top layer.
TEXLINE: analysis.tex:695-719 -/
theorem ex_top_phi (A : PaperNFA Q) (σ : Selector A) (P : Params) (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1) (hα : P.α = P.β * P.γ) (q : Q) (i : ℕ) (hi : 1 ≤ i) (hq : q ∈ layerSet A i)
    (F : Finset (Fin P.γ)) (t : CoreState Q) (ht : SpiritInv A ε t) :
    ex (hatSamples A σ P t i q (rho A t i q))
        (fun H => phiP A σ q i ε P F i t (hatVal H (rho A t i q))) =
      phiP A σ q i ε P F (i - 1) t (atomVal t (i - 1)) := by
  classical
  set ρ := rho A t i q
  have hfl : ∀ c ∈ pred A i q, (1 - ε) / (langCount A (i - 1) c : ℝ) ≤ t.p (i - 1) c :=
    fun c hc => ht.1 _ c (Finset.mem_filter.1 hc).1
  have hL : (0 : ℝ) < langCount A i q := by
    exact_mod_cast StarBadLeSpiritAux.langCount_pos' A i q hq
  have hρ0 : 0 < ρ := (div_pos (by linarith) hL).trans_le
    (rho_ge_floor A ε hε0 hε1 t i hi q hq hfl)
  have hp0 : ∀ c ∈ pred A i q, 0 < t.p (i - 1) c := fun c hc =>
    hρ0.trans_le (rho_le_pred A t i q c hc)
  rw [ex_polyOn _ (hatSamples_support_finite _ _ _ _ _ _ _) (fun H => hatVal H ρ)
    (fun e => childAtom σ t i e.1 e.2.2 e.2.1) (phiP_polyOn A σ q i ε P F i le_rfl t)
    fun T hT => ?_]
  · exact phiP_subst A σ q i ε P F i hi le_rfl t
      (fun c hc => (p_pos_of_inv A ε hε1 t ht _ c hc).ne') _ fun r w hw =>
      childAtom_atomIdx A σ q i i hi le_rfl t r w hw
  · have hq' : ∀ e ∈ T, e.2.2 = q := by
      intro e he
      have h := hT he
      unfold phiAtoms blockAtoms at h
      rw [Finset.mem_biUnion] at h
      obtain ⟨b, _, h⟩ := h
      rw [Finset.mem_image] at h
      obtain ⟨⟨r, w⟩, hrw, rfl⟩ := h
      rw [atomIdx_top A σ q i r w (Finset.mem_product.1 hrw).2]
    have hinj : Set.InjOn (fun e : ℕ × List Bool × Q => (e.1, e.2.1)) ↑T := by
      intro x hx y hy h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 (Prod.ext h.2 ((hq' x hx).trans (hq' y hy).symm))
    have hl : ∀ H : ℕ → Finset (List Bool), ∏ e ∈ T, hatVal H ρ e =
        ∏ x ∈ T.image (fun e => (e.1, e.2.1)), if x.2 ∈ H x.1 then 1 / ρ else 0 := by
      intro H
      rw [Finset.prod_image fun x hx y hy h => hinj hx hy h]
      rfl
    simp_rw [hl]
    rw [ex_hatSamples_prod A σ P t i hi q ρ _ ?_ hρ0 (fun c hc => rho_le_pred A t i q c hc) hp0,
      Finset.prod_image fun x hx y hy h => hinj hx hy h]
    · refine Finset.prod_congr rfl fun e he => ?_
      rw [hq' e he]
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨e, he, rfl⟩ := hx
      obtain ⟨h1, h2, h3, _⟩ := phiAtoms_valid A σ q i P hα F i le_rfl e (hT he)
      exact ⟨h1, h2, (hq' e he) ▸ h3⟩


/-- **Domination in expectation**: `E[∏_b (Y_{q,b} − |L(q)|)² | 𝓕_i] ≤ β^{−2|F|} ∏_b (N_{b,i−1} + V_{b,i−1})`.

INTERNAL: analysis.tex:619-662 with the top step.
TEXLINE: analysis.tex:619-662 -/
theorem ex_top_le (A : PaperNFA Q) (σ : Selector A) (P : Params) (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1) (hα : P.α = P.β * P.γ) (hβ : 0 < P.β) (q : Q) (i : ℕ) (hi : 1 ≤ i)
    (hq : q ∈ layerSet A i) (F : Finset (Fin P.γ)) (t : CoreState Q) (ht : SpiritInv A ε t) :
    ex (hatSamples A σ P t i q (rho A t i q))
        (fun H => ∏ b ∈ F, (blockMean P (rho A t i q) H b - (lang A i q).card) ^ 2) ≤
      (1 / (P.β : ℝ) ^ 2) ^ F.card * phiP A σ q i ε P F (i - 1) t (atomVal t (i - 1)) := by
  set ρ := rho A t i q
  have hfl : ∀ c ∈ pred A i q, (1 - ε) / (langCount A (i - 1) c : ℝ) ≤ t.p (i - 1) c :=
    fun c hc => ht.1 _ c (Finset.mem_filter.1 hc).1
  have hρ : (1 - ε) / ((lang A i q).card : ℝ) ≤ ρ := by
    rw [card_lang]; exact rho_ge_floor A ε hε0 hε1 t i hi q hq hfl
  rw [← ex_top_phi A σ P ε hε0 hε1 hα q i hi hq F t ht, ← ex_mul_left]
  refine ex_mono _ (hatSamples_support_finite _ _ _ _ _ _ _) fun H hH => ?_
  have hHv : ∀ r, H r ⊆ lang A i q := fun r w hw => (mem_lang A i q w).2
    (hatSamples_support_valid A σ P t i hi q ρ (fun c r u hu => (ht.2 _ c r u hu).1) H hH r w hw)
  have hβ2 : (0 : ℝ) < (P.β : ℝ) ^ 2 := by positivity
  unfold phiP
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun b _ => by positivity) fun b _ => ?_
  have hdom := blockP_dom A σ q i ε hε0 hε1 P hβ t (fun d _ c hc => ht.1 d c hc) H hHv ρ hρ hq b
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hβ2]
  linarith

/-- The run up to the `k`-th listed state `q^i` is layers `1, …, i−1` and then states of
layer `i`.

INTERNAL: list bookkeeping.
TEXLINE: algorithm.tex:97-100 -/
theorem take_corePairs (A : PaperNFA Q) (n k i : ℕ) (q : Q)
    (hx : (corePairs A n)[k]? = some (i, q)) :
    ∃ ys, (corePairs A n).take k = corePairs A (i - 1) ++ ys ∧ ∀ y ∈ ys, y.1 = i := by
  have hmem : (i, q) ∈ corePairs A n := List.mem_of_getElem? hx
  obtain ⟨hi1, hin, _⟩ := (StarBadLeSpiritAux.mem_corePairs A n i q).1 hmem
  have hsplit : ∀ m d, ∃ R, corePairs A (m + d) = corePairs A m ++ R ∧ ∀ y ∈ R, m < y.1 := by
    intro m d
    induction d with
    | zero => exact ⟨[], by simp, by simp⟩
    | succ d ih =>
        obtain ⟨R, hR, hRy⟩ := ih
        refine ⟨R ++ (layerList A (m + d + 1)).map fun q' => (m + d + 1, q'), ?_, ?_⟩
        · rw [← Nat.add_assoc, corePairs_succ, hR, List.append_assoc]
        · intro y hy
          rw [List.mem_append] at hy
          rcases hy with hy | hy
          · exact hRy y hy
          · simp only [List.mem_map] at hy
            obtain ⟨_, _, rfl⟩ := hy
            show m < m + d + 1
            omega
  obtain ⟨R, hR, hRy⟩ := hsplit (i - 1) (n - (i - 1))
  rw [show i - 1 + (n - (i - 1)) = n by omega] at hR
  set C := corePairs A (i - 1)
  have hC : ∀ y ∈ C, y.1 ≤ i - 1 := fun y hy =>
    ((StarBadLeSpiritAux.mem_corePairs A (i - 1) y.1 y.2).1 hy).2.1
  obtain ⟨hk, hxk⟩ := List.getElem?_eq_some_iff.1 hx
  have hkC : C.length ≤ k := by
    by_contra h
    push Not at h
    have h1 : (corePairs A n)[k]? = C[k]? := by rw [hR, List.getElem?_append_left h]
    rw [hx] at h1
    have := hC _ (List.mem_of_getElem? h1.symm)
    simp at this
    omega
  refine ⟨R.take (k - C.length), ?_, ?_⟩
  · rw [hR, List.take_append, List.take_of_length_le hkC]
  · intro y hy
    have hyR : y ∈ R := List.mem_of_mem_take hy
    have hlo := hRy y hyR
    have hyk : y ∈ (corePairs A n).take k := by
      rw [hR, List.take_append, List.take_of_length_le hkC]
      exact List.mem_append_right _ hy
    rw [List.mem_take_iff_getElem] at hyk
    obtain ⟨m, hm, rfl⟩ := hyk
    have hsort := List.pairwise_iff_getElem.1 (StarBadLeSpiritAux.corePairs_sorted A n)
    have := hsort m k (by omega) hk (by omega)
    rw [hxk] at this
    simp at this hlo
    omega


/-- The states of layer `i` before `q` do not touch what `∏_b (N_{b,i−1} + V_{b,i−1})` reads.

INTERNAL: `𝓕_i` is fixed before layer `i` starts.
TEXLINE: analysis.tex:166-170 -/
theorem phi_frame (A : PaperNFA Q) (σ : Selector A) (P : Params) (ε : ℝ) (q : Q) (i : ℕ)
    (hi : 1 ≤ i) (F : Finset (Fin P.γ)) (ys : List (ℕ × Q)) (hys : ∀ y ∈ ys, y.1 = i)
    (t t' : CoreState Q) (ht' : t' ∈ (runSpirit A σ P ε t ys).support) :
    phiP A σ q i ε P F (i - 1) t' (atomVal t' (i - 1)) =
      phiP A σ q i ε P F (i - 1) t (atomVal t (i - 1)) := by
  have hnot : ∀ d, d ≠ i → ∀ c, ((d, c) : ℕ × Q) ∉ ys := fun d hd c h => hd (hys _ h)
  have hp : ∀ d, d ≠ i → t'.p d = t.p d := fun d hd => funext fun c =>
    StarBadLeSpiritAux.runSpirit_frame A σ P ε ys t t' ht' d c (hnot d hd c)
  have hS : t'.S (i - 1) = t.S (i - 1) := funext fun c =>
    runSpirit_frame_S A σ P ε ys t t' ht' (i - 1) c (hnot (i - 1) (by omega) c)
  have hatom : atomVal t' (i - 1) = atomVal t (i - 1) := by
    funext e
    unfold atomVal
    rw [hS, hp (i - 1) (by omega)]
  rw [hatom]
  exact phiP_congr A σ q i ε P F (i - 1) t t' (fun d hd => hp d (by omega)) _

/-- `spiritPrefix` has finite support.

INTERNAL: bookkeeping.
TEXLINE: analysis.tex:156-162 -/
theorem spiritPrefix_support_finite (A : PaperNFA Q) (σ : Selector A) (P : Params) (ε : ℝ)
    (n k : ℕ) : (spiritPrefix A σ P ε n k).support.Finite :=
  runSpirit_support_finite _ _ _ _ _ _

/-- `spiritMeans` has finite support.

INTERNAL: bookkeeping.
TEXLINE: analysis.tex:156-162 -/
theorem spiritMeans_support_finite (A : PaperNFA Q) (σ : Selector A) (P : Params) (ε : ℝ)
    (n k i : ℕ) (q : Q) : (spiritMeans A σ P ε n k i q).support.Finite :=
  support_bind_finite _ _ (spiritPrefix_support_finite _ _ _ _ _ _) fun _ _ =>
    support_map_finite _ _ (hatSamples_support_finite _ _ _ _ _ _ _)

/-- **The block moment bound, as a real expectation**, for any parameter block with
`α = βγ` and `β > 0`.

INTERNAL: analysis.tex:551-692 assembled.
TEXLINE: analysis.tex:551-692 -/
theorem spirit_moment_ex (A : PaperNFA Q) (σ : Selector A) (P : Params) (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1) (hα : P.α = P.β * P.γ) (hβ : 0 < P.β) (n k i : ℕ) (q : Q)
    (hx : (corePairs A n)[k]? = some (i, q)) (F : Finset (Fin P.γ)) :
    ex (spiritMeans A σ P ε n k i q) (fun Y => ∏ b ∈ F, (Y b - (langCount A i q : ℝ)) ^ 2) ≤
      (1 / (P.β : ℝ) ^ 2) ^ F.card *
        ((P.β : ℝ) * ((i + 1) * (lang A i q).card ^ 2 / (1 - ε))) ^ F.card := by
  have hmem : (i, q) ∈ corePairs A n := List.mem_of_getElem? hx
  obtain ⟨hi, _, hq⟩ := (StarBadLeSpiritAux.mem_corePairs A n i q).1 hmem
  have hc0 : (0 : ℝ) ≤ (1 / (P.β : ℝ) ^ 2) ^ F.card := by positivity
  unfold spiritMeans
  rw [ex_bind _ _ (spiritPrefix_support_finite _ _ _ _ _ _) fun _ _ =>
    support_map_finite _ _ (hatSamples_support_finite _ _ _ _ _ _ _)]
  have hinv : ∀ t ∈ (spiritPrefix A σ P ε n k).support, SpiritInv A ε t := by
    intro t ht
    exact runSpirit_inv A σ P ε _ (fun y hy => one_le_of_mem_corePairs A n y
      (List.mem_of_mem_take hy)) _ t (initState_inv A P ε hε0) ht
  calc ex (spiritPrefix A σ P ε n k) (fun t => ex ((hatSamples A σ P t i q (rho A t i q)).map
          fun hatS (b : Fin P.γ) => blockMean P (rho A t i q) hatS b)
          (fun Y => ∏ b ∈ F, (Y b - (langCount A i q : ℝ)) ^ 2))
      ≤ ex (spiritPrefix A σ P ε n k) (fun t => (1 / (P.β : ℝ) ^ 2) ^ F.card *
          phiP A σ q i ε P F (i - 1) t (atomVal t (i - 1))) := by
        refine ex_mono _ (spiritPrefix_support_finite _ _ _ _ _ _) fun t ht => ?_
        rw [ex_map _ _ (hatSamples_support_finite _ _ _ _ _ _ _), ← card_lang]
        exact ex_top_le A σ P ε hε0 hε1 hα hβ q i hi hq F t (hinv t ht)
    _ = (1 / (P.β : ℝ) ^ 2) ^ F.card *
          phiP A σ q i ε P F 0 (initState A P) (atomVal (initState A P) 0) := by
        rw [ex_mul_left]
        congr 1
        obtain ⟨ys, hys, hysi⟩ := take_corePairs A n k i q hx
        unfold spiritPrefix
        rw [hys, runSpirit_append, ex_bind _ _ (runSpirit_support_finite _ _ _ _ _ _)
          fun _ _ => runSpirit_support_finite _ _ _ _ _ _]
        rw [← ex_lawUpTo_phi A σ P ε hε0 hε1 hα q i F (i - 1) (by omega)]
        refine ex_congr _ fun t _ => ?_
        rw [ex_congr _ fun t' ht' => phi_frame A σ P ε q i hi F ys hysi t t' ht',
          ex_const _ (runSpirit_support_finite _ _ _ _ _ _)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (phiP_zero_le A σ q i ε hε0 hε1 P hα F) hc0

end Nfa.Analysis.SpiritBlockMomentAux

namespace Nfa.Analysis

open Nfa.Pseudocode SpiritBlockMomentAux

/-- **The block moment bound** (analysis.tex:551-692): in `N^s` with the paper's
parameters, at the `k`-th listed state `q^i`,
`E[∏_{b ∈ F} (Y_{q,b} − |L(q)|)²] ≤ ((n+1)|L(q)|²/((1−ε)β))^{|F|}`.

PAPER: analysis.tex:551-692 (the bound on `E[∏_b (Y_{q,b} − |L(q)|)²]` in the proof of
lemma bound_proba_AND_event), analysis.tex:695-719 (lemma induction_lemma). -/
theorem spirit_block_moment_le (hprior : Nfa.Prior) {Q : Type} [Fintype Q] [LinearOrder Q]
    (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (n : ℕ) (ε δ : ℝ)
    (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε < 1) (k i : ℕ) (q : Q)
    (hx : (corePairs A n)[k]? = some (i, q)) (F : Finset (Fin (Nfa.params A n ε δ).γ)) :
    ∑' Y, spiritMeans A σ (Nfa.params A n ε δ) ε n k i q Y *
        ENNReal.ofReal (∏ b ∈ F, (Y b - (langCount A i q : ℝ)) ^ 2)
      ≤ ENNReal.ofReal
          (((n + 1) * (langCount A i q : ℝ) ^ 2 /
            ((1 - ε) * ((Nfa.params A n ε δ).β : ℝ))) ^ F.card) := by
  have hα : (Nfa.params A n ε δ).α = (Nfa.params A n ε δ).β * (Nfa.params A n ε δ).γ := rfl
  have h1ε : 0 < 1 - ε := by linarith
  have hβ : 0 < (Nfa.params A n ε δ).β := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    exact Nat.ceil_pos.2 (by positivity)
  have hβ' : (0 : ℝ) < (Nfa.params A n ε δ).β := by exact_mod_cast hβ
  have hmem : (i, q) ∈ corePairs A n := List.mem_of_getElem? hx
  obtain ⟨_, hin, _⟩ := (StarBadLeSpiritAux.mem_corePairs A n i q).1 hmem
  have hex := spirit_moment_ex A σ (Nfa.params A n ε δ) ε hε0 hε1 hα hβ n k i q hx F
  rw [PmfExpect.tsum_ofReal_eq _ (spiritMeans_support_finite _ _ _ _ _ _ _ _) _
    fun Y _ => Finset.prod_nonneg fun b _ => sq_nonneg _]
  refine ENNReal.ofReal_le_ofReal (hex.trans ?_)
  rw [← mul_pow, CanonPathAux.card_lang]
  refine pow_le_pow_left₀ (by positivity) ?_ _
  rw [show 1 / ((Nfa.params A n ε δ).β : ℝ) ^ 2 * ((Nfa.params A n ε δ).β *
      ((i + 1) * (langCount A i q : ℝ) ^ 2 / (1 - ε))) =
      (i + 1) * (langCount A i q : ℝ) ^ 2 / ((1 - ε) * ((Nfa.params A n ε δ).β : ℝ)) by
    field_simp]
  gcongr

end Nfa.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · paper's route: atoms' moments (`SpiritMoments`), multiaffine expectations
  (`PolyOn`), the block polynomials (`BlockPoly`), induction down the layers
* r1 · open · stated for `bound_proba_AND_event` (its Markov step is proved there)
-/
