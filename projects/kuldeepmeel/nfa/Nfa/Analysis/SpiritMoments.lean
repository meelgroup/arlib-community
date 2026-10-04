import Nfa.Analysis.PmfExpect
import Nfa.Analysis.DigitCoinApplyTrue
import Nfa.Analysis.StarBadLeSpirit

/-!
# Moments of the atoms in the spirited algorithm `N^s`

The expectation identities of analysis.tex:221-370 (lemmas expectation_of_singleton and
expectation_of_pair, for any number of distinct atoms at once), proved for the
transcription: one `reduce` (`ex_reduce_prod`), the final reduce of a state
(`ex_finalReduce_prod`, the `hat 𝓕` half), the `hat S` draws of a state
(`ex_hatSamples_prod`, the `𝓕` half), one spirited step (`ex_spiritStep_prod`) and one
whole layer (`ex_layer_prod`): for distinct valid atoms
`A_r(u, q') = 1_{u ∈ S^r(q')}/p(q')` of layer `j`,

  `E[∏ A_r(u, q') | 𝓕_j] = ∏ A_r(u⁻, σ(u, q'))`.

Distinct atoms are independent coins, which is why products factor.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped ENNReal

namespace Nfa.Analysis.SpiritMomentsAux
open Nfa.Pseudocode PmfExpect

/-- `digitCoin` has finite support.

INTERNAL: expectation bookkeeping for the moment bound of lemma bound_proba_AND_event.
TEXLINE: analysis.tex:221-370 -/
theorem digitCoin_support_finite (π : ℝ) : (digitCoin π).support.Finite := Set.toFinite _

/-- `reduce` has finite support.

INTERNAL: expectation bookkeeping for the moment bound of lemma bound_proba_AND_event.
TEXLINE: analysis.tex:221-370 -/
theorem reduce_support_finite (S : Finset (List Bool)) (π : ℝ) : (reduce S π).support.Finite :=
  support_map_finite _ _ (drawAll_support_finite _ _ (fun _ => digitCoin_support_finite π) _)

/-- `E[a·1_{coin}] = π a` for the Bernoulli(`π`) coin of `reduce`.

INTERNAL: expectation bookkeeping for the moment bound of lemma bound_proba_AND_event.
TEXLINE: analysis.tex:221-370 -/
theorem ex_digitCoin (π : ℝ) (h0 : 0 ≤ π) (h1 : π ≤ 1) (a : ℝ) :
    ex (digitCoin π) (fun k => if k = true then a else 0) = π * a := by
  rw [ex_eq_sum _ _ Finset.univ fun k hk => absurd (Finset.mem_univ k) hk]
  simp [digitCoin_apply_true π h0 h1, ENNReal.toReal_ofReal h0]

/-- `E[∏_{u ∈ U} a_u 1_{u ∈ reduce(S,π)}] = ∏_{u ∈ U} 1_{u ∈ S} π a_u`.

INTERNAL: expectation bookkeeping for the moment bound of lemma bound_proba_AND_event.
TEXLINE: analysis.tex:221-370 -/
theorem ex_reduce_prod (S : Finset (List Bool)) (π : ℝ) (h0 : 0 ≤ π) (h1 : π ≤ 1)
    (U : Finset (List Bool)) (a : List Bool → ℝ) :
    ex (reduce S π) (fun R => ∏ u ∈ U, if u ∈ R then a u else 0) =
      ∏ u ∈ U, if u ∈ S then π * a u else 0 := by
  classical
  unfold reduce
  rw [ex_map _ _ (drawAll_support_finite _ _ (fun _ => digitCoin_support_finite π) _)]
  by_cases hU : U ⊆ S
  · have hstep : ∀ keep : List Bool → Bool,
        (∏ u ∈ U, if u ∈ S.filter (fun x => keep x = true) then a u else 0) =
          ∏ u ∈ S.toList.toFinset, (fun u k => if u ∈ U then (if k = true then a u else 0)
            else 1) u (keep u) := by
      intro keep
      rw [Finset.toList_toFinset, ← Finset.prod_subset hU (fun u _ hu => by simp [hu])]
      refine Finset.prod_congr rfl fun u hu => ?_
      simp [Finset.mem_filter, hU hu, hu]
    simp_rw [hstep]
    refine (ex_drawAll_prod _ false (fun _ => digitCoin_support_finite π)
      (fun u k => if u ∈ U then (if k = true then a u else 0) else 1) S.toList
      (Finset.nodup_toList S)).trans ?_
    rw [Finset.toList_toFinset, ← Finset.prod_subset hU (fun u _ hu => by
        simp only [hu, if_false]; exact ex_const _ (digitCoin_support_finite π) 1)]
    refine Finset.prod_congr rfl fun u hu => ?_
    simp only [hu, if_true, hU hu]
    exact ex_digitCoin π h0 h1 (a u)
  · obtain ⟨u, huU, huS⟩ := Finset.not_subset.1 hU
    rw [Finset.prod_eq_zero huU (by simp [huS])]
    have : ∀ keep : List Bool → Bool,
        (∏ u ∈ U, if u ∈ S.filter (fun x => keep x = true) then a u else 0) = 0 :=
      fun keep => Finset.prod_eq_zero huU (by simp [Finset.mem_filter, huS])
    simp_rw [this]
    exact ex_const _ (drawAll_support_finite _ _ (fun _ => digitCoin_support_finite π) _) 0


/-- `reduce` moment with a constant weight, for an injectively indexed monomial.

INTERNAL: expectation bookkeeping for the moment bound of lemma bound_proba_AND_event.
TEXLINE: analysis.tex:221-370 -/
theorem ex_reduce_prod_inj {ι : Type} (S : Finset (List Bool)) (π : ℝ) (h0 : 0 ≤ π)
    (h1 : π ≤ 1) (X : Finset ι) (u : ι → List Bool) (hu : Set.InjOn u X) (c : ℝ) :
    ex (reduce S π) (fun R => ∏ x ∈ X, if u x ∈ R then c else 0) =
      ∏ x ∈ X, if u x ∈ S then π * c else 0 := by
  classical
  have h1' : ∀ R : Finset (List Bool), (∏ x ∈ X, if u x ∈ R then c else 0) =
      ∏ v ∈ X.image u, if v ∈ R then c else 0 := fun R =>
    (Finset.prod_image (f := fun v => if v ∈ R then c else 0)
      fun x hx y hy h => hu hx hy h).symm
  simp_rw [h1']
  rw [ex_reduce_prod S π h0 h1 _ (fun _ => c)]
  exact Finset.prod_image (f := fun v => if v ∈ S then π * c else 0)
    fun x hx y hy h => hu hx hy h

/-- Grouping a product by a key.

INTERNAL: expectation bookkeeping for the moment bound of lemma bound_proba_AND_event.
TEXLINE: analysis.tex:221-370 -/
theorem prod_group {ι κ : Type} [DecidableEq κ] (T : Finset ι) (key : ι → κ) (K : Finset κ)
    (hK : ∀ x ∈ T, key x ∈ K) (g : ι → ℝ) :
    ∏ x ∈ T, g x = ∏ k ∈ K, ∏ x ∈ T.filter (fun x => key x = k), g x :=
  (Finset.prod_fiberwise_of_maps_to hK g).symm

/-- **`finalReduce` moment** (the `hat 𝓕` half of lemmas expectation_of_singleton/_of_pair):
`E[∏_{(r,u) ∈ T} 1_{u ∈ S^r}/p | hat S] = ∏_{(r,u) ∈ T} 1_{u ∈ hat S^r}/ρ`.

INTERNAL: expectation bookkeeping for the moment bound of lemma bound_proba_AND_event.
TEXLINE: analysis.tex:221-260 -/
theorem ex_finalReduce_prod (P : Params) (H : ℕ → Finset (List Bool)) (ρ p : ℝ)
    (hp0 : 0 < p) (hpρ : p ≤ ρ) (T : Finset (ℕ × List Bool)) (hT : ∀ x ∈ T, x.1 < P.α) :
    ex (finalReduce P H ρ p) (fun S => ∏ x ∈ T, if x.2 ∈ S x.1 then 1 / p else 0) =
      ∏ x ∈ T, if x.2 ∈ H x.1 then 1 / ρ else 0 := by
  classical
  have hρ0 : 0 < ρ := hp0.trans_le hpρ
  have hK : ∀ x ∈ T, x.1 ∈ (List.range P.α).toFinset := fun x hx => by
    simp [hT x hx]
  have hinj : ∀ r : ℕ,
      Set.InjOn Prod.snd (↑(T.filter fun x => x.1 = r) : Set (ℕ × List Bool)) := by
    intro r x hx y hy h
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
    exact Prod.ext (hx.2.trans hy.2.symm) h
  have hL : ∀ S : ℕ → Finset (List Bool), (∏ x ∈ T, if x.2 ∈ S x.1 then 1 / p else 0) =
      ∏ r ∈ (List.range P.α).toFinset,
        (fun r R => ∏ x ∈ T.filter (fun x => x.1 = r), if x.2 ∈ R then 1 / p else 0) r (S r) := by
    intro S
    rw [prod_group T Prod.fst _ hK]
    refine Finset.prod_congr rfl fun r _ => Finset.prod_congr rfl fun x hx => ?_
    rw [(Finset.mem_filter.1 hx).2]
  simp_rw [hL]
  unfold finalReduce
  refine (ex_drawAll_prod (fun r => reduce (H r) (p / ρ)) ∅ (fun r => reduce_support_finite _ _)
    (fun r R => ∏ x ∈ T.filter (fun x => x.1 = r), if x.2 ∈ R then 1 / p else 0)
    (List.range P.α) List.nodup_range).trans ?_
  rw [prod_group T Prod.fst _ hK]
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [ex_reduce_prod_inj _ _ (div_nonneg hp0.le hρ0.le) ((div_le_one hρ0).2 hpρ) _ _ (hinj r)]
  refine Finset.prod_congr rfl fun x hx => ?_
  rw [(Finset.mem_filter.1 hx).2]
  congr 1
  field_simp


variable {Q : Type} [Fintype Q] [LinearOrder Q]

/-- The canonical predecessor `σ(u, q')` of a sample `u` at `q'`.

INTERNAL: the atoms of analysis.tex:176-183.
TEXLINE: analysis.tex:176-183 -/
noncomputable def childOf {A : PaperNFA Q} (σ : Selector A) (q' : Q) (u : List Bool) : Q :=
  (σ.pick q' u.dropLast (u.getLastD false)).getD q'

/-- A word of `L(q'^j)`, `j ≥ 1`, splits as `v·b` with `σ` picking a predecessor in `pred`.

INTERNAL: expectation bookkeeping for the moment bound of lemma bound_proba_AND_event.
TEXLINE: analysis.tex:221-370 -/
theorem valid_decomp (A : PaperNFA Q) (σ : Selector A) (j : ℕ) (hj : 1 ≤ j) (q' : Q)
    (u : List Bool) (hlen : u.length = j) (hq : q' ∈ A.toNFA.eval u) :
    ∃ v b, u = v ++ [b] ∧ σ.pick q' v b = some (childOf σ q' u) ∧ u.dropLast = v ∧
      childOf σ q' u ∈ pred A j q' ∧ b ∈ labels A (childOf σ q' u) q' ∧
      childOf σ q' u ∈ A.toNFA.eval v := by
  rcases List.eq_nil_or_concat u with rfl | ⟨v, b, rfl⟩
  · simp at hlen; omega
  rw [List.concat_eq_append] at hlen hq ⊢
  rw [NFA.eval_append_singleton, NFA.mem_stepSet] at hq
  obtain ⟨c, hc, hcq⟩ := hq
  have hsome := σ.pick_complete q' v b c hcq hc
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.1 hsome
  have hchild : childOf σ q' (v ++ [b]) = c' := by
    simp [childOf, List.dropLast_concat, List.getLastD_concat, hc']
  obtain ⟨hdel, hev⟩ := σ.pick_sound q' v b c' hc'
  refine ⟨v, b, rfl, by rw [hchild, hc'], List.dropLast_concat, ?_, ?_, by rw [hchild]; exact hev⟩
  · rw [hchild]
    unfold pred
    rw [Finset.mem_filter]
    refine ⟨?_, ⟨b, by simp [labels, hdel]⟩⟩
    unfold layerSet
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨v, by simp at hlen; omega, hev⟩
  · rw [hchild]; simp [labels, hdel]

/-- The selector union keeps a word exactly when its canonical predecessor's draw does.

INTERNAL: expectation bookkeeping for the moment bound of lemma bound_proba_AND_event.
TEXLINE: analysis.tex:221-370 -/
theorem mem_unionSel_iff (A : PaperNFA Q) (σ : Selector A) (j : ℕ) (hj : 1 ≤ j) (q' : Q)
    (u : List Bool) (hlen : u.length = j) (hq : q' ∈ A.toNFA.eval u)
    (bar : Q → Finset (List Bool)) :
    u ∈ unionSel σ q' (pred A j q') bar ↔ u ∈ bar (childOf σ q' u) := by
  classical
  obtain ⟨v, b, rfl, hpick, _, hpred, _, _⟩ := valid_decomp A σ j hj q' u hlen hq
  unfold unionSel
  simp only [Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨c, _, hu, ⟨w, b', hwb, hpk⟩⟩
    obtain ⟨rfl, hb⟩ := List.append_inj hwb.symm (by simpa using congrArg List.length hwb.symm)
    · simp only [List.cons.injEq, and_true] at hb
      subst hb
      rw [hpick] at hpk
      cases hpk
      exact hu
  · intro hu
    exact ⟨_, hpred, hu, v, b, rfl, hpick⟩

/-- Membership in `T·Σ(c, q')` of `v·b` with `b ∈ Σ(c, q')`.

INTERNAL: expectation bookkeeping for the moment bound of lemma bound_proba_AND_event.
TEXLINE: analysis.tex:221-370 -/
theorem mem_extendSet_iff (T : Finset (List Bool)) (L : Finset Bool) (v : List Bool) (b : Bool)
    (hb : b ∈ L) : v ++ [b] ∈ extendSet T L ↔ v ∈ T := by
  unfold extendSet
  simp only [Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨w, b', ⟨hw, _⟩, h⟩
    obtain ⟨rfl, _⟩ := List.append_inj h (by simpa using congrArg List.length h)
    exact hw
  · intro hv
    exact ⟨v, b, ⟨hv, hb⟩, rfl⟩


/-- The child atom `A_r(u⁻, σ(u, q'))` one layer down, read in `t`.

INTERNAL: the atoms of analysis.tex:176-183.
TEXLINE: analysis.tex:176-183 -/
noncomputable def childAtom {A : PaperNFA Q} (σ : Selector A) (t : CoreState Q) (j r : ℕ)
    (q' : Q) (u : List Bool) : ℝ :=
  if u.dropLast ∈ t.S (j - 1) (childOf σ q' u) r then 1 / t.p (j - 1) (childOf σ q' u) else 0

/-- `normalize` has finite support.

INTERNAL: expectation bookkeeping for the moment bound of lemma bound_proba_AND_event.
TEXLINE: analysis.tex:221-370 -/
theorem normalize_support_finite (A : PaperNFA Q) (t : CoreState Q) (i : ℕ) (q : Q) (ρ : ℝ)
    (r : ℕ) (q' : Q) : (normalize A t i q ρ r q').support.Finite :=
  reduce_support_finite _ _

/-- `hatSample` has finite support.

INTERNAL: expectation bookkeeping for the moment bound of lemma bound_proba_AND_event.
TEXLINE: analysis.tex:221-370 -/
theorem hatSample_support_finite (A : PaperNFA Q) (σ : Selector A) (t : CoreState Q) (i : ℕ)
    (q : Q) (ρ : ℝ) (r : ℕ) : (hatSample A σ t i q ρ r).support.Finite :=
  support_map_finite _ _ (drawAll_support_finite _ _ (normalize_support_finite A t i q ρ r) _)

/-- `hatSamples` has finite support.

INTERNAL: expectation bookkeeping for the moment bound of lemma bound_proba_AND_event.
TEXLINE: analysis.tex:221-370 -/
theorem hatSamples_support_finite (A : PaperNFA Q) (σ : Selector A) (P : Params)
    (t : CoreState Q) (i : ℕ) (q : Q) (ρ : ℝ) : (hatSamples A σ P t i q ρ).support.Finite :=
  drawAll_support_finite _ _ (hatSample_support_finite A σ t i q ρ) _

/-- **`hatSample` moment** (the `𝓕` half of lemmas expectation_of_singleton/_of_pair): for
distinct valid words, `E[∏ 1_{u ∈ hat S^r(q')}/ρ | 𝓕] = ∏ A_r(u⁻, σ(u, q'))`.

INTERNAL: expectation bookkeeping for the moment bound of lemma bound_proba_AND_event.
TEXLINE: analysis.tex:221-260 -/
theorem ex_hatSample_prod {ι : Type} (A : PaperNFA Q) (σ : Selector A) (t : CoreState Q)
    (i : ℕ) (hi : 1 ≤ i) (q' : Q) (ρ : ℝ) (r : ℕ) (X : Finset ι) (u : ι → List Bool)
    (hu : Set.InjOn u X) (hval : ∀ x ∈ X, (u x).length = i ∧ q' ∈ A.toNFA.eval (u x))
    (hρ0 : 0 < ρ) (hρp : ∀ c ∈ pred A i q', ρ ≤ t.p (i - 1) c)
    (hp0 : ∀ c ∈ pred A i q', 0 < t.p (i - 1) c) :
    ex (hatSample A σ t i q' ρ r) (fun Hr => ∏ x ∈ X, if u x ∈ Hr then 1 / ρ else 0) =
      ∏ x ∈ X, childAtom σ t i r q' (u x) := by
  classical
  unfold hatSample
  rw [ex_map _ _ (drawAll_support_finite _ _ (normalize_support_finite A t i q' ρ r) _)]
  have hK : ∀ x ∈ X, childOf σ q' (u x) ∈ (predList A i q').toFinset := by
    intro x hx
    obtain ⟨_, _, _, _, _, hpred, _, _⟩ :=
      valid_decomp A σ i hi q' (u x) (hval x hx).1 (hval x hx).2
    simpa [predList] using hpred
  have hL : ∀ bar : Q → Finset (List Bool),
      (∏ x ∈ X, if u x ∈ unionSel σ q' (pred A i q') bar then 1 / ρ else 0) =
        ∏ c ∈ (predList A i q').toFinset,
          (fun c R => ∏ x ∈ X.filter (fun x => childOf σ q' (u x) = c),
            if u x ∈ R then 1 / ρ else 0) c (bar c) := by
    intro bar
    rw [prod_group X (fun x => childOf σ q' (u x)) _ hK]
    refine Finset.prod_congr rfl fun c _ => Finset.prod_congr rfl fun x hx => ?_
    rw [Finset.mem_filter] at hx
    exact if_congr (by rw [mem_unionSel_iff A σ i hi q' (u x) (hval x hx.1).1 (hval x hx.1).2,
      hx.2]) rfl rfl
  simp_rw [hL]
  refine (ex_drawAll_prod (normalize A t i q' ρ r) ∅ (normalize_support_finite A t i q' ρ r)
    (fun c R => ∏ x ∈ X.filter (fun x => childOf σ q' (u x) = c),
      if u x ∈ R then 1 / ρ else 0)
    (predList A i q') (Finset.sort_nodup _ _)).trans ?_
  rw [prod_group X (fun x => childOf σ q' (u x)) _ hK]
  refine Finset.prod_congr rfl fun c hc => ?_
  have hcp : c ∈ pred A i q' := by simpa [predList] using hc
  have hpc := hp0 c hcp
  unfold Pseudocode.normalize
  rw [ex_reduce_prod_inj _ _ (div_nonneg hρ0.le hpc.le) ((div_le_one hpc).2 (hρp c hcp)) _ _
    (hu.mono (by intro x hx; simp only [Finset.coe_filter] at hx; exact hx.1))]
  refine Finset.prod_congr rfl fun x hx => ?_
  rw [Finset.mem_filter] at hx
  obtain ⟨v, b, hvb, _, hdrop, _, hb, _⟩ :=
    valid_decomp A σ i hi q' (u x) (hval x hx.1).1 (hval x hx.1).2
  unfold childAtom
  rw [hx.2]
  have hmem : u x ∈ extendSet (t.S (i - 1) c r) (labels A c q') ↔
      (u x).dropLast ∈ t.S (i - 1) c r := by
    rw [hdrop, hvb]; exact mem_extendSet_iff _ _ v b (hx.2 ▸ hb)
  exact if_congr hmem (by field_simp) rfl


/-- **`hatSamples` moment**: over all repetitions, for distinct valid `(r, u)`,
`E[∏ 1_{u ∈ hat S^r(q')}/ρ | 𝓕] = ∏ A_r(u⁻, σ(u, q'))`.

INTERNAL: expectation bookkeeping for the moment bound of lemma bound_proba_AND_event.
TEXLINE: analysis.tex:221-260 -/
theorem ex_hatSamples_prod (A : PaperNFA Q) (σ : Selector A) (P : Params) (t : CoreState Q)
    (i : ℕ) (hi : 1 ≤ i) (q' : Q) (ρ : ℝ) (T : Finset (ℕ × List Bool))
    (hT : ∀ x ∈ T, x.1 < P.α ∧ x.2.length = i ∧ q' ∈ A.toNFA.eval x.2)
    (hρ0 : 0 < ρ) (hρp : ∀ c ∈ pred A i q', ρ ≤ t.p (i - 1) c)
    (hp0 : ∀ c ∈ pred A i q', 0 < t.p (i - 1) c) :
    ex (hatSamples A σ P t i q' ρ) (fun H => ∏ x ∈ T, if x.2 ∈ H x.1 then 1 / ρ else 0) =
      ∏ x ∈ T, childAtom σ t i x.1 q' x.2 := by
  classical
  have hK : ∀ x ∈ T, x.1 ∈ (List.range P.α).toFinset := fun x hx => by simp [(hT x hx).1]
  have hinj : ∀ r : ℕ,
      Set.InjOn Prod.snd (↑(T.filter fun x => x.1 = r) : Set (ℕ × List Bool)) := by
    intro r x hx y hy h
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
    exact Prod.ext (hx.2.trans hy.2.symm) h
  have hL : ∀ H : ℕ → Finset (List Bool), (∏ x ∈ T, if x.2 ∈ H x.1 then 1 / ρ else 0) =
      ∏ r ∈ (List.range P.α).toFinset,
        (fun r R => ∏ x ∈ T.filter (fun x => x.1 = r), if x.2 ∈ R then 1 / ρ else 0) r (H r) := by
    intro H
    rw [prod_group T Prod.fst _ hK]
    refine Finset.prod_congr rfl fun r _ => Finset.prod_congr rfl fun x hx => ?_
    rw [(Finset.mem_filter.1 hx).2]
  simp_rw [hL]
  unfold hatSamples
  refine (ex_drawAll_prod (hatSample A σ t i q' ρ) ∅ (hatSample_support_finite A σ t i q' ρ)
    (fun r R => ∏ x ∈ T.filter (fun x => x.1 = r), if x.2 ∈ R then 1 / ρ else 0)
    (List.range P.α) List.nodup_range).trans ?_
  rw [prod_group T Prod.fst _ hK]
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [ex_hatSample_prod A σ t i hi q' ρ r _ Prod.snd (hinj r)
    (fun x hx => (hT x (Finset.mem_filter.1 hx).1).2) hρ0 hρp hp0]
  refine Finset.prod_congr rfl fun x hx => ?_
  rw [(Finset.mem_filter.1 hx).2]

/-- The spirit's floor propagates to `ρ` (eq. spirit_rho_floor).

INTERNAL: expectation bookkeeping for the moment bound of lemma bound_proba_AND_event.
TEXLINE: analysis.tex:82-86 -/
theorem rho_ge_floor (A : PaperNFA Q) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (t : CoreState Q) (i : ℕ)
    (hi : 1 ≤ i) (q' : Q) (hq' : q' ∈ layerSet A i)
    (hfl : ∀ c ∈ pred A i q', (1 - ε) / (langCount A (i - 1) c : ℝ) ≤ t.p (i - 1) c) :
    (1 - ε) / (langCount A i q' : ℝ) ≤ rho A t i q' := by
  have hL : (1 : ℝ) ≤ langCount A i q' := by
    exact_mod_cast StarBadLeSpiritAux.langCount_pos' A i q' hq'
  unfold rho
  split_ifs with h
  · rw [Finset.le_inf'_iff]
    intro c hc
    refine le_trans ?_ (hfl c hc)
    have hcL : (1 : ℝ) ≤ langCount A (i - 1) c := by
      have : c ∈ layerSet A (i - 1) := (Finset.mem_filter.1 hc).1
      exact_mod_cast StarBadLeSpiritAux.langCount_pos' A (i - 1) c this
    have := StarBadLeSpiritAux.langCount_pred_le A i hi q' c hc
    apply div_le_div_of_nonneg_left (by linarith) (by linarith)
    exact_mod_cast this
  · rw [div_le_one (by linarith)]
    linarith

/-- `ρ(q) ≤ p(q')` for every predecessor `q'`.

INTERNAL: expectation bookkeeping for the moment bound of lemma bound_proba_AND_event.
TEXLINE: analysis.tex:221-370 -/
theorem rho_le_pred (A : PaperNFA Q) (t : CoreState Q) (i : ℕ) (q' c : Q)
    (hc : c ∈ pred A i q') : rho A t i q' ≤ t.p (i - 1) c := by
  unfold rho
  rw [dif_pos ⟨c, hc⟩]
  exact Finset.inf'_le _ hc

/-- A step at `q^i` writes `S^·(q^i)`.

INTERNAL: expectation bookkeeping for the moment bound of lemma bound_proba_AND_event.
TEXLINE: analysis.tex:221-370 -/
theorem writeState_S_self (st : CoreState Q) (i : ℕ) (q : Q) (p : ℝ)
    (S' : ℕ → Finset (List Bool)) : (StarBadLeSpiritAux.writeState st i q p S').S i q = S' := by
  simp [StarBadLeSpiritAux.writeState]

/-- `finalReduce` has finite support.

INTERNAL: expectation bookkeeping for the moment bound of lemma bound_proba_AND_event.
TEXLINE: analysis.tex:221-370 -/
theorem finalReduce_support_finite (P : Params) (H : ℕ → Finset (List Bool)) (ρ p : ℝ) :
    (finalReduce P H ρ p).support.Finite :=
  drawAll_support_finite _ _ (fun _ => reduce_support_finite _ _) _

/-- `spiritStep` has finite support.

INTERNAL: expectation bookkeeping for the moment bound of lemma bound_proba_AND_event.
TEXLINE: analysis.tex:221-370 -/
theorem spiritStep_support_finite (A : PaperNFA Q) (σ : Selector A) (P : Params) (ε : ℝ)
    (i : ℕ) (t : CoreState Q) (q' : Q) : (spiritStep A σ P ε i t q').support.Finite := by
  rw [StarBadLeSpiritAux.spiritStep_eq]
  exact support_bind_finite _ _ (hatSamples_support_finite _ _ _ _ _ _ _) fun H _ =>
    support_map_finite _ _ (finalReduce_support_finite _ _ _ _)

/-- **One estimate step of `N^s`** (both halves of lemmas expectation_of_singleton/_of_pair):
for distinct valid `(r, u)`, `E[∏ A_r(u, q') | 𝓕] = ∏ A_r(u⁻, σ(u, q'))`.

INTERNAL: expectation bookkeeping for the moment bound of lemma bound_proba_AND_event.
TEXLINE: analysis.tex:221-300 -/
theorem ex_spiritStep_prod (A : PaperNFA Q) (σ : Selector A) (P : Params) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (t : CoreState Q) (i : ℕ) (hi : 1 ≤ i) (q' : Q)
    (hq' : q' ∈ layerSet A i)
    (hfl : ∀ c ∈ pred A i q', (1 - ε) / (langCount A (i - 1) c : ℝ) ≤ t.p (i - 1) c)
    (T : Finset (ℕ × List Bool))
    (hT : ∀ x ∈ T, x.1 < P.α ∧ x.2.length = i ∧ q' ∈ A.toNFA.eval x.2) :
    ex (spiritStep A σ P ε i t q')
        (fun t' => ∏ x ∈ T, if x.2 ∈ t'.S i q' x.1 then 1 / t'.p i q' else 0) =
      ∏ x ∈ T, childAtom σ t i x.1 q' x.2 := by
  have hL : (0 : ℝ) < langCount A i q' := by
    exact_mod_cast StarBadLeSpiritAux.langCount_pos' A i q' hq'
  have hfl0 : 0 < (1 - ε) / (langCount A i q' : ℝ) := div_pos (by linarith) hL
  have hρfl := rho_ge_floor A ε hε0 hε1 t i hi q' hq' hfl
  have hρ0 : 0 < rho A t i q' := hfl0.trans_le hρfl
  have hp0 : ∀ c ∈ pred A i q', 0 < t.p (i - 1) c := fun c hc =>
    hρ0.trans_le (rho_le_pred A t i q' c hc)
  rw [StarBadLeSpiritAux.spiritStep_eq, ex_bind _ _ (hatSamples_support_finite _ _ _ _ _ _ _)
    fun H _ => support_map_finite _ _ (finalReduce_support_finite _ _ _ _)]
  rw [← ex_hatSamples_prod A σ P t i hi q' (rho A t i q') T hT hρ0
    (fun c hc => rho_le_pred A t i q' c hc) hp0]
  refine ex_congr _ fun H _ => ?_
  rw [ex_map _ _ (finalReduce_support_finite _ _ _ _)]
  simp only [StarBadLeSpiritAux.writeState_p_self, writeState_S_self]
  refine ex_finalReduce_prod P H _ _ ?_ ?_ T fun x hx => (hT x hx).1
  · exact hfl0.trans_le (le_max_right _ _)
  · refine max_le ?_ hρfl
    unfold takeMin
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _


/-- A step at `q^i` leaves every other sample set alone.

INTERNAL: expectation bookkeeping for the moment bound of lemma bound_proba_AND_event.
TEXLINE: analysis.tex:221-370 -/
theorem writeState_S_ne (st : CoreState Q) (i : ℕ) (q : Q) (p : ℝ) (S' : ℕ → Finset (List Bool))
    (ℓ : ℕ) (q' : Q) (h : (ℓ, q') ≠ (i, q)) :
    (StarBadLeSpiritAux.writeState st i q p S').S ℓ q' = st.S ℓ q' := by
  unfold StarBadLeSpiritAux.writeState
  by_cases hℓ : ℓ = i
  · subst hℓ
    have hq : q' ≠ q := fun hq => h (by rw [hq])
    simp [Function.update_of_ne hq]
  · simp [Function.update_of_ne hℓ]

/-- Every outcome of a spirited step agrees with its input's samples off `q^i`.

INTERNAL: expectation bookkeeping for the moment bound of lemma bound_proba_AND_event.
TEXLINE: analysis.tex:221-370 -/
theorem spiritStep_frame_S (A : PaperNFA Q) (σ : Selector A) (P : Params) (ε : ℝ) (i : ℕ)
    (st : CoreState Q) (q : Q) (u : CoreState Q)
    (hu : u ∈ (spiritStep A σ P ε i st q).support) (ℓ : ℕ) (q' : Q) (h : (ℓ, q') ≠ (i, q)) :
    u.S ℓ q' = st.S ℓ q' := by
  rw [StarBadLeSpiritAux.spiritStep_eq, PMF.mem_support_bind_iff] at hu
  obtain ⟨_, _, hu⟩ := hu
  rw [PMF.mem_support_map_iff] at hu
  obtain ⟨_, _, rfl⟩ := hu
  exact writeState_S_ne _ _ _ _ _ _ _ h

/-- `N^s` never touches the samples of an unlisted state.

INTERNAL: expectation bookkeeping for the moment bound of lemma bound_proba_AND_event.
TEXLINE: analysis.tex:221-370 -/
theorem runSpirit_frame_S (A : PaperNFA Q) (σ : Selector A) (P : Params) (ε : ℝ) :
    ∀ (ys : List (ℕ × Q)) (st t : CoreState Q), t ∈ (runSpirit A σ P ε st ys).support →
      ∀ ℓ q', (ℓ, q') ∉ ys → t.S ℓ q' = st.S ℓ q'
  | [], st, t, ht, ℓ, q', _ => by
      simp only [runSpirit, PMF.support_pure, Set.mem_singleton_iff] at ht
      rw [ht]
  | x :: ys, st, t, ht, ℓ, q', hy => by
      rw [runSpirit, PMF.mem_support_bind_iff] at ht
      obtain ⟨u, hu, ht⟩ := ht
      rw [List.mem_cons, not_or] at hy
      rw [runSpirit_frame_S A σ P ε ys u t ht ℓ q' hy.2]
      exact spiritStep_frame_S A σ P ε x.1 st x.2 u hu ℓ q' hy.1

/-- `runSpirit` has finite support.

INTERNAL: expectation bookkeeping for the moment bound of lemma bound_proba_AND_event.
TEXLINE: analysis.tex:221-370 -/
theorem runSpirit_support_finite (A : PaperNFA Q) (σ : Selector A) (P : Params) (ε : ℝ) :
    ∀ (ys : List (ℕ × Q)) (st : CoreState Q), (runSpirit A σ P ε st ys).support.Finite
  | [], st => by simp [runSpirit, PMF.support_pure]
  | x :: ys, st => by
      rw [runSpirit]
      exact support_bind_finite _ _ (spiritStep_support_finite _ _ _ _ _ _ _) fun u _ =>
        runSpirit_support_finite A σ P ε ys u

/-- The atom `A_r(u, q'^j) = 1_{u ∈ S^r(q'^j)}/p(q'^j)`, read in `t`.

INTERNAL: the atoms of analysis.tex:176-183.
TEXLINE: analysis.tex:176-183 -/
noncomputable def atomVal (t : CoreState Q) (j : ℕ) (x : ℕ × List Bool × Q) : ℝ :=
  if x.2.1 ∈ t.S j x.2.2 x.1 then 1 / t.p j x.2.2 else 0

/-- `childAtom` reads only layer `j − 1`.

INTERNAL: expectation bookkeeping for the moment bound of lemma bound_proba_AND_event.
TEXLINE: analysis.tex:221-370 -/
theorem childAtom_congr {A : PaperNFA Q} (σ : Selector A) (t t' : CoreState Q) (j r : ℕ)
    (q' : Q) (u : List Bool) (hp : t'.p (j - 1) = t.p (j - 1))
    (hS : t'.S (j - 1) = t.S (j - 1)) :
    childAtom σ t' j r q' u = childAtom σ t j r q' u := by
  unfold childAtom; rw [hp, hS]

/-- **One layer of `N^s`** (the step of lemma induction_lemma, both halves): for distinct
valid atoms of layer `j`, `E[∏ A | 𝓕_j] = ∏ A(child)`.

INTERNAL: expectation bookkeeping for the moment bound of lemma bound_proba_AND_event.
TEXLINE: analysis.tex:695-719 -/
theorem ex_layer_prod (A : PaperNFA Q) (σ : Selector A) (P : Params) (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1) (j : ℕ) (hj : 1 ≤ j) :
    ∀ (qs : List Q), qs.Nodup → (∀ q' ∈ qs, q' ∈ layerSet A j) →
      ∀ (t : CoreState Q),
        (∀ c ∈ layerSet A (j - 1), (1 - ε) / (langCount A (j - 1) c : ℝ) ≤ t.p (j - 1) c) →
        ∀ (T : Finset (ℕ × List Bool × Q)),
          (∀ x ∈ T, x.1 < P.α ∧ x.2.1.length = j ∧ x.2.2 ∈ A.toNFA.eval x.2.1 ∧ x.2.2 ∈ qs) →
          ex (runSpirit A σ P ε t (qs.map fun q' => (j, q'))) (fun t' => ∏ x ∈ T, atomVal t' j x) =
            ∏ x ∈ T, childAtom σ t j x.1 x.2.2 x.2.1
  | [], _, _, t, _, T, hT => by
      have : T = ∅ := Finset.eq_empty_of_forall_notMem fun x hx => by simpa using (hT x hx).2.2.2
      subst this
      simp [runSpirit, ex_pure]
  | q1 :: qs, hnd, hqs, t, hfl, T, hT => by
      classical
      rw [List.nodup_cons] at hnd
      have hq1 : q1 ∈ layerSet A j := hqs q1 (by simp)
      set T1 := T.filter fun x => x.2.2 = q1
      set T2 := T.filter fun x => ¬ x.2.2 = q1
      have hnot : ((j, q1) : ℕ × Q) ∉ qs.map fun q' => (j, q') := by
        simp only [List.mem_map, Prod.mk.injEq, true_and, not_exists, not_and]
        exact fun q' hq' h => hnd.1 (h ▸ hq')
      have hne : ∀ c, ((j - 1, c) : ℕ × Q) ≠ (j, q1) := fun c h => by
        have := congrArg Prod.fst h; simp at this; omega
      simp only [List.map_cons, runSpirit]
      rw [ex_bind _ _ (spiritStep_support_finite _ _ _ _ _ _ _)
        fun u _ => runSpirit_support_finite _ _ _ _ _ _]
      -- inner expectation, for an outcome `t1` of the first step
      have hinner : ∀ t1 ∈ (spiritStep A σ P ε j t q1).support,
          ex (runSpirit A σ P ε t1 (qs.map fun q' => (j, q'))) (fun t' => ∏ x ∈ T, atomVal t' j x) =
            (∏ x ∈ T1, atomVal t1 j x) * ∏ x ∈ T2, childAtom σ t j x.1 x.2.2 x.2.1 := by
        intro t1 ht1
        have hp1 : t1.p (j - 1) = t.p (j - 1) := funext fun c =>
          StarBadLeSpiritAux.spiritStep_frame A σ P ε j t q1 t1 ht1 _ c (hne c)
        have hS1 : t1.S (j - 1) = t.S (j - 1) := funext fun c =>
          spiritStep_frame_S A σ P ε j t q1 t1 ht1 _ c (hne c)
        have ih := ex_layer_prod A σ P ε hε0 hε1 j hj qs hnd.2
          (fun q' hq' => hqs q' (by simp [hq'])) t1 (by rw [hp1]; exact hfl) T2 (by
            intro x hx
            rw [Finset.mem_filter] at hx
            obtain ⟨h1, h2, h3, h4⟩ := hT x hx.1
            refine ⟨h1, h2, h3, ?_⟩
            simp only [List.mem_cons] at h4
            exact h4.resolve_left hx.2)
        have hfr : ∀ t' ∈ (runSpirit A σ P ε t1 (qs.map fun q' => (j, q'))).support,
            ∏ x ∈ T1, atomVal t' j x = ∏ x ∈ T1, atomVal t1 j x := by
          intro t' ht'
          refine Finset.prod_congr rfl fun x hx => ?_
          rw [Finset.mem_filter] at hx
          unfold atomVal
          rw [hx.2, StarBadLeSpiritAux.runSpirit_frame A σ P ε _ t1 t' ht' j q1 hnot,
            runSpirit_frame_S A σ P ε _ t1 t' ht' j q1 hnot]
        have hcongr : ex (runSpirit A σ P ε t1 (qs.map fun q' => (j, q')))
              (fun t' => ∏ x ∈ T, atomVal t' j x) =
            ex (runSpirit A σ P ε t1 (qs.map fun q' => (j, q')))
              (fun t' => (∏ x ∈ T1, atomVal t1 j x) * ∏ x ∈ T2, atomVal t' j x) := by
          refine ex_congr _ fun t' ht' => ?_
          rw [← Finset.prod_filter_mul_prod_filter_not T (fun x => x.2.2 = q1)]
          exact congrArg (· * _) (hfr t' ht')
        rw [hcongr, ex_mul_left, ih]
        congr 1
        exact Finset.prod_congr rfl fun x _ => childAtom_congr σ t t1 j _ _ _ hp1 hS1
      rw [ex_congr _ hinner, ex_mul_right]
      rw [← Finset.prod_filter_mul_prod_filter_not T (fun x => x.2.2 = q1)]
      congr 1
      -- the first step, by `ex_spiritStep_prod`
      have hinj : Set.InjOn (fun x : ℕ × List Bool × Q => (x.1, x.2.1)) ↑T1 := by
        intro x hx y hy h
        simp only [Finset.coe_filter, Set.mem_ofPred_eq, T1] at hx hy
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 (Prod.ext h.2 (hx.2.trans hy.2.symm))
      have hl : ∀ t1 : CoreState Q, ∏ x ∈ T1, atomVal t1 j x =
          ∏ y ∈ T1.image (fun x => (x.1, x.2.1)),
            if y.2 ∈ t1.S j q1 y.1 then 1 / t1.p j q1 else 0 := by
        intro t1
        rw [Finset.prod_image fun x hx y hy h => hinj hx hy h]
        refine Finset.prod_congr rfl fun x hx => ?_
        rw [Finset.mem_filter] at hx
        unfold atomVal
        rw [hx.2]
      have hr : ∏ x ∈ T1, childAtom σ t j x.1 x.2.2 x.2.1 =
          ∏ y ∈ T1.image (fun x => (x.1, x.2.1)), childAtom σ t j y.1 q1 y.2 := by
        rw [Finset.prod_image fun x hx y hy h => hinj hx hy h]
        refine Finset.prod_congr rfl fun x hx => ?_
        rw [(Finset.mem_filter.1 hx).2]
      simp_rw [hl]
      rw [hr]
      refine ex_spiritStep_prod A σ P ε hε0 hε1 t j hj q1 hq1
        (fun c hc => hfl c (Finset.mem_filter.1 hc).1) _ ?_
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [Finset.mem_filter] at hx
      obtain ⟨h1, h2, h3, _⟩ := hT x hx.1
      exact ⟨h1, h2, hx.2 ▸ h3⟩

end Nfa.Analysis.SpiritMomentsAux

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · moments of `reduce`, `finalReduce`, `hatSamples`, `spiritStep`, one layer
-/
