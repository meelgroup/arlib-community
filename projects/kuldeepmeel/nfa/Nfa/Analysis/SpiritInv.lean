import Nfa.Analysis.SpiritMoments

/-!
# Invariants of the spirited algorithm `N^s`

`SpiritInv A ε t`: at every unrolled state `q^ℓ`, `p(q^ℓ) ≥ (1−ε)/|L(q^ℓ)|` (the spirit's
floor, analysis.tex:76-86), and every stored sample of `q^ℓ` is a word of `L(q^ℓ)`.
Both hold at `initState` and along every run of `N^s` over states of layers `≥ 1`
(`runSpirit_inv`).  The first is what "the spirit ensures `p(q^{w₁,w₂}) ≥ (1−ε)/|L|`
with probability 1" (analysis.tex:627) means in the transcription.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nfa.Analysis.SpiritInvAux
open Nfa.Pseudocode PmfExpect SpiritMomentsAux

variable {Q : Type} [Fintype Q] [LinearOrder Q]

/-- The invariants of every reachable state of `N^s`: the spirit's floor holds at every
unrolled state, and every stored sample of `q^ℓ` is a word of `L(q^ℓ)`.

INTERNAL: what the spirit guarantees "with probability 1" (analysis.tex:76-86, 627).
TEXLINE: analysis.tex:76-86 -/
def SpiritInv (A : PaperNFA Q) (ε : ℝ) (t : CoreState Q) : Prop :=
  (∀ ℓ, ∀ c ∈ layerSet A ℓ, (1 - ε) / (langCount A ℓ c : ℝ) ≤ t.p ℓ c) ∧
  (∀ ℓ c r, ∀ u ∈ t.S ℓ c r, u.length = ℓ ∧ c ∈ A.toNFA.eval u)

/-- `initState` satisfies the invariants.

INTERNAL: bookkeeping.
TEXLINE: analysis.tex:76-86 -/
theorem initState_inv (A : PaperNFA Q) (P : Params) (ε : ℝ) (hε0 : 0 < ε) :
    SpiritInv A ε (initState A P) := by
  refine ⟨fun ℓ c hc => ?_, fun ℓ c r u hu => ?_⟩
  · have hL : (1 : ℝ) ≤ langCount A ℓ c := by
      exact_mod_cast StarBadLeSpiritAux.langCount_pos' A ℓ c hc
    show (1 - ε) / (langCount A ℓ c : ℝ) ≤ 1
    rw [div_le_one (by linarith)]
    linarith
  · simp only [initState] at hu
    split_ifs at hu with h
    · obtain ⟨rfl, rfl, _⟩ := h
      rw [Finset.mem_singleton] at hu
      subst hu
      simp [NFA.eval_nil, PaperNFA.toNFA]
    · simp at hu

/-- On the list, `drawAll` reads a value its draw can take.

INTERNAL: support bookkeeping.
TEXLINE: algorithm.tex:49-56 -/
theorem drawAll_support_mem {ι β : Type} [DecidableEq ι] (f : ι → PMF β) (d : β) :
    ∀ (L : List ι) (g : ι → β), g ∈ (drawAll f d L).support → ∀ i ∈ L, g i ∈ (f i).support
  | [], _, _, i, hi => by simp at hi
  | j :: js, g, hg, i, hi => by
      simp only [drawAll, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hg
      obtain ⟨b, hb, g', hg', rfl⟩ := hg
      by_cases hij : i = j
      · subst hij; rw [Function.update_self]; exact hb
      · rw [Function.update_of_ne hij]
        exact drawAll_support_mem f d js g' hg' i ((List.mem_cons.1 hi).resolve_left hij)

/-- `reduce(S, π) ⊆ S`.

INTERNAL: support bookkeeping.
TEXLINE: algorithm.tex:49-56 -/
theorem reduce_support_subset (S : Finset (List Bool)) (π : ℝ) (R : Finset (List Bool))
    (hR : R ∈ (reduce S π).support) : R ⊆ S := by
  unfold reduce at hR
  rw [PMF.mem_support_map_iff] at hR
  obtain ⟨_, _, rfl⟩ := hR
  exact Finset.filter_subset _ _

/-- `S^r(q) ⊆ hat S^r(q)`.

INTERNAL: support bookkeeping.
TEXLINE: algorithm.tex:80-84 -/
theorem finalReduce_support_subset (P : Params) (H : ℕ → Finset (List Bool)) (ρ p : ℝ)
    (S' : ℕ → Finset (List Bool)) (hS : S' ∈ (finalReduce P H ρ p).support) (r : ℕ) :
    S' r ⊆ H r := by
  unfold finalReduce at hS
  by_cases hr : r ∈ List.range P.α
  · exact reduce_support_subset _ _ _ (drawAll_support_mem _ _ _ S' hS r hr)
  · rw [drawAll_support_off _ _ _ S' hS r hr]; exact Finset.empty_subset _

/-- Every word of `hat S^r(q')` is a word of `L(q'^i)`, when the samples of layer `i − 1` are.

INTERNAL: support bookkeeping.
TEXLINE: algorithm.tex:64-78 -/
theorem hatSamples_support_valid (A : PaperNFA Q) (σ : Selector A) (P : Params)
    (t : CoreState Q) (i : ℕ) (hi : 1 ≤ i) (q' : Q) (ρ : ℝ)
    (hS : ∀ c r, ∀ u ∈ t.S (i - 1) c r, u.length = i - 1)
    (H : ℕ → Finset (List Bool)) (hH : H ∈ (hatSamples A σ P t i q' ρ).support) (r : ℕ) :
    ∀ u ∈ H r, u.length = i ∧ q' ∈ A.toNFA.eval u := by
  classical
  intro u hu
  unfold hatSamples at hH
  by_cases hr : r ∈ List.range P.α
  · have h := drawAll_support_mem _ _ _ H hH r hr
    unfold hatSample at h
    rw [PMF.mem_support_map_iff] at h
    obtain ⟨bar, hbar, hHr⟩ := h
    rw [← hHr] at hu
    unfold unionSel at hu
    simp only [Finset.mem_biUnion, Finset.mem_filter] at hu
    obtain ⟨c, hc, hub, w, b, rfl, hpick⟩ := hu
    obtain ⟨hdel, hev⟩ := σ.pick_sound q' w b c hpick
    have hcl : c ∈ predList A i q' := by simpa [predList] using hc
    have hbc := drawAll_support_mem _ _ _ bar hbar c hcl
    have hsub := reduce_support_subset _ _ _ hbc hub
    unfold extendSet at hsub
    rw [Finset.mem_image] at hsub
    obtain ⟨⟨v, b'⟩, hvb, hvb'⟩ := hsub
    rw [Finset.mem_product] at hvb
    have hlen := hS c r v hvb.1
    refine ⟨?_, ?_⟩
    · have := congrArg List.length hvb'
      simp only [List.length_append, List.length_singleton] at this
      rw [List.length_append, List.length_singleton]; omega
    · rw [NFA.eval_append_singleton, NFA.mem_stepSet]
      exact ⟨c, hev, hdel⟩
  · rw [drawAll_support_off _ _ _ H hH r hr] at hu; simp at hu

/-- The invariants are preserved by one spirited step at a state of layer `i ≥ 1`.

INTERNAL: bookkeeping.
TEXLINE: analysis.tex:76-86 -/
theorem spiritStep_inv (A : PaperNFA Q) (σ : Selector A) (P : Params) (ε : ℝ)
    (i : ℕ) (hi : 1 ≤ i) (t : CoreState Q) (q' : Q) (ht : SpiritInv A ε t)
    (u : CoreState Q) (hu : u ∈ (spiritStep A σ P ε i t q').support) : SpiritInv A ε u := by
  rw [StarBadLeSpiritAux.spiritStep_eq, PMF.mem_support_bind_iff] at hu
  obtain ⟨H, hH, hu⟩ := hu
  rw [PMF.mem_support_map_iff] at hu
  obtain ⟨S', hS', rfl⟩ := hu
  refine ⟨fun ℓ c hc => ?_, fun ℓ c r w hw => ?_⟩
  · by_cases h : (ℓ, c) = (i, q')
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rw [StarBadLeSpiritAux.writeState_p_self]
      exact le_max_right _ _
    · rw [StarBadLeSpiritAux.writeState_p_ne _ _ _ _ _ _ _ h]
      exact ht.1 ℓ c hc
  · by_cases h : (ℓ, c) = (i, q')
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rw [writeState_S_self] at hw
      exact hatSamples_support_valid A σ P t ℓ hi c _ (fun c r u hu => (ht.2 _ c r u hu).1) H hH r
        w (finalReduce_support_subset P H _ _ S' hS' r hw)
    · rw [writeState_S_ne _ _ _ _ _ _ _ h] at hw
      exact ht.2 ℓ c r w hw

/-- The invariants hold along every run of `N^s` over states of layers `≥ 1`.

INTERNAL: bookkeeping.
TEXLINE: analysis.tex:76-86 -/
theorem runSpirit_inv (A : PaperNFA Q) (σ : Selector A) (P : Params) (ε : ℝ) :
    ∀ (ys : List (ℕ × Q)), (∀ y ∈ ys, 1 ≤ y.1) → ∀ (st t : CoreState Q), SpiritInv A ε st →
      t ∈ (runSpirit A σ P ε st ys).support → SpiritInv A ε t
  | [], _, st, t, hst, ht => by
      simp only [runSpirit, PMF.support_pure, Set.mem_singleton_iff] at ht
      rw [ht]; exact hst
  | x :: ys, hys, st, t, hst, ht => by
      rw [runSpirit, PMF.mem_support_bind_iff] at ht
      obtain ⟨u, hu, ht⟩ := ht
      exact runSpirit_inv A σ P ε ys (fun y hy => hys y (by simp [hy])) u t
        (spiritStep_inv A σ P ε x.1 (hys x (by simp)) st x.2 hst u hu) ht

end Nfa.Analysis.SpiritInvAux

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · floor and sample-validity invariants of `N^s`
-/
