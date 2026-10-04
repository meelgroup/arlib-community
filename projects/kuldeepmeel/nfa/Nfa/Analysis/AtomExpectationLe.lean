import Nfa.Analysis.CoreLawStar
import Nfa.Analysis.DigitCoinApplyTrue

/-!
# Atoms have expectation at most one in `countNFAcore*`

The atom `A_r(w, q^ℓ) = 1_{w ∈ S^r(q^ℓ)} / p(q^ℓ)` (analysis.tex:475-486) is
`atomVal r ℓ q w`, read in `ℝ≥0∞`.  `atom_expectation_le` is the upper-bound half of
Proposition atoms_have_expected_value_one for `countNFAcore*`: its expectation under
`coreLawStar` is at most `1` when `w ∈ L(q^ℓ)` (`|w| = ℓ`, `q ∈ eval w`) and `0`
otherwise.  The second half is what `S^r(q) ⊆ L(q)` buys, without carrying it as a
state invariant.

Route (paper's, analysis.tex:480-486, tower rule along the run):
* invariant on a law `D` of states: every `p` is positive on the support, and
  `E_D[atomVal r ℓ q w] ≤ 1_{w ∈ L(q^ℓ)}` for all `ℓ q w`;
* one `estimateAndSample` step at `(i, q)`, `i ≥ 1`, from a fixed state `st`:
  for `w = u·b` with `σ.pick q u b = some q'`, the final-reduce coin is kept with
  probability at most `p/ρ`, the normalise coin with probability at most `ρ/p(q')`
  (`digitCoin x true ≤ x`), so `E[atomVal r i q w] ≤ atomVal r (i-1) q' u st`;
  every other atom is unchanged;
* both coin marginals come from `drawAll` over a duplicate-free list.
-/

set_option autoImplicit false

open scoped ENNReal

namespace Nfa.Analysis

open Nfa.Pseudocode

variable {Q : Type} [Fintype Q] [LinearOrder Q]

/-- The atom `A_r(w, q^ℓ) = 1_{w ∈ S^r(q^ℓ)} / p(q^ℓ)` of a core state, in `ℝ≥0∞`.

PAPER: analysis.tex:475-478 (the atoms `A_r(w, q)`, background of
Proposition atoms_have_expected_value_one). -/
noncomputable def atomVal (r ℓ : ℕ) (q : Q) (w : List Bool) (st : CoreState Q) : ℝ≥0∞ :=
  if w ∈ st.S ℓ q r then ENNReal.ofReal (1 / st.p ℓ q) else 0

end Nfa.Analysis

namespace Nfa.Analysis.AtomAux

open Nfa.Pseudocode

/-- Expectation of an `ℝ≥0∞`-valued function under a PMF.

INTERNAL: notation for the proof.
TEXLINE: analysis.tex:475-486 -/
noncomputable def ex {α : Type} (D : PMF α) (f : α → ℝ≥0∞) : ℝ≥0∞ := ∑' x, D x * f x

/-- `E_{pure a}[f] = f a`.

INTERNAL: step of the proof of atoms_have_expected_value_one.
TEXLINE: analysis.tex:475-486 -/
theorem ex_pure {α : Type} (a : α) (f : α → ℝ≥0∞) : ex (PMF.pure a) f = f a := by
  unfold ex
  rw [tsum_eq_single a (fun b hb => by simp [PMF.pure_apply, hb])]
  simp

/-- Tower rule: `E_{D >>= k}[f] = E_D[E_{k ·}[f]]`.

INTERNAL: step of the proof of atoms_have_expected_value_one.
TEXLINE: analysis.tex:475-486 -/
theorem ex_bind {α β : Type} (D : PMF α) (k : α → PMF β) (f : β → ℝ≥0∞) :
    ex (D.bind k) f = ex D fun a => ex (k a) f := by
  unfold ex
  simp_rw [PMF.bind_apply, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => tsum_congr fun b => by ring

/-- `E_{map g D}[f] = E_D[f ∘ g]`.

INTERNAL: step of the proof of atoms_have_expected_value_one.
TEXLINE: analysis.tex:475-486 -/
theorem ex_map {α β : Type} (D : PMF α) (g : α → β) (f : β → ℝ≥0∞) :
    ex (D.map g) f = ex D (f ∘ g) := by
  rw [← PMF.bind_pure_comp, ex_bind]
  simp [ex_pure]; rfl

/-- `E_D[c] = c`.

INTERNAL: step of the proof of atoms_have_expected_value_one.
TEXLINE: analysis.tex:475-486 -/
theorem ex_const {α : Type} (D : PMF α) (c : ℝ≥0∞) : ex D (fun _ => c) = c := by
  unfold ex
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Monotonicity of `ex` on the support.

INTERNAL: step of the proof of atoms_have_expected_value_one.
TEXLINE: analysis.tex:475-486 -/
theorem ex_mono {α : Type} (D : PMF α) {f g : α → ℝ≥0∞} (h : ∀ a ∈ D.support, f a ≤ g a) :
    ex D f ≤ ex D g := by
  unfold ex
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ D.support
  · exact mul_le_mul_right (h a ha) _
  · rw [PMF.apply_eq_zero_iff _ _ |>.2 ha]; simp

/-- `ex` depends only on the values on the support.

INTERNAL: step of the proof of atoms_have_expected_value_one.
TEXLINE: analysis.tex:475-486 -/
theorem ex_congr {α : Type} (D : PMF α) {f g : α → ℝ≥0∞} (h : ∀ a ∈ D.support, f a = g a) :
    ex D f = ex D g :=
  le_antisymm (ex_mono D fun a ha => (h a ha).le) (ex_mono D fun a ha => (h a ha).ge)

/-- One coordinate of `drawAll` over a duplicate-free list has the law of its own draw.

INTERNAL: independence of the draws, read one coordinate at a time.
TEXLINE: algorithm.tex:49-56 -/
theorem drawAll_map_eval {ι β : Type} [DecidableEq ι] (f : ι → PMF β) (d : β) :
    ∀ (l : List ι), l.Nodup → ∀ i ∈ l, (drawAll f d l).map (fun g => g i) = f i
  | [], _, i, hi => by simp at hi
  | j :: js, hnd, i, hi => by
      rw [List.nodup_cons] at hnd
      simp only [drawAll, PMF.map_bind, PMF.map_comp]
      by_cases hij : i = j
      · subst hij
        have : ∀ b, (drawAll f d js).map ((fun g => g i) ∘ fun g => Function.update g i b)
            = PMF.pure b := by
          intro b
          simp only [Function.comp_def, Function.update_self]
          exact PMF.map_const _ _
        simp_rw [this]
        exact PMF.bind_pure _
      · have hi' : i ∈ js := by simpa [hij] using hi
        have : ∀ b, (drawAll f d js).map ((fun g => g i) ∘ fun g => Function.update g j b)
            = f i := by
          intro b
          simp only [Function.comp_def, Function.update_of_ne hij]
          exact drawAll_map_eval f d js hnd.2 i hi'
        simp_rw [this]
        exact PMF.bind_const _ _

/-- A coordinate off the list of `drawAll` is the default.

INTERNAL: step of the proof of atoms_have_expected_value_one.
TEXLINE: analysis.tex:475-486 -/
theorem drawAll_map_eval_not_mem {ι β : Type} [DecidableEq ι] (f : ι → PMF β) (d : β) :
    ∀ (l : List ι) (i : ι), i ∉ l → (drawAll f d l).map (fun g => g i) = PMF.pure d
  | [], i, _ => by simp [drawAll, PMF.pure_map]
  | j :: js, i, hi => by
      have hij : i ≠ j := fun h => hi (h ▸ List.mem_cons_self)
      have hi' : i ∉ js := fun h => hi (List.mem_cons_of_mem _ h)
      simp only [drawAll, PMF.map_bind, PMF.map_comp, Function.comp_def,
        Function.update_of_ne hij]
      simp_rw [drawAll_map_eval_not_mem f d js i hi']
      exact PMF.bind_const _ _

/-- `ex` form of `drawAll_map_eval`.

INTERNAL: step of the proof of atoms_have_expected_value_one.
TEXLINE: analysis.tex:475-486 -/
theorem ex_drawAll_eval {ι β : Type} [DecidableEq ι] (f : ι → PMF β) (d : β) (l : List ι)
    (hl : l.Nodup) (i : ι) (hi : i ∈ l) (h : β → ℝ≥0∞) :
    ex (drawAll f d l) (fun g => h (g i)) = ex (f i) h := by
  rw [← drawAll_map_eval f d l hl i hi, ex_map]
  rfl

/-- `ex` form of `drawAll_map_eval_not_mem`.

INTERNAL: step of the proof of atoms_have_expected_value_one.
TEXLINE: analysis.tex:475-486 -/
theorem ex_drawAll_eval_not_mem {ι β : Type} [DecidableEq ι] (f : ι → PMF β) (d : β)
    (l : List ι) (i : ι) (hi : i ∉ l) (h : β → ℝ≥0∞) :
    ex (drawAll f d l) (fun g => h (g i)) = h d := by
  rw [← ex_pure d h, ← drawAll_map_eval_not_mem f d l i hi, ex_map]
  rfl

/-- `Pr[digitCoin x] ≤ x` for `x ≥ 0` (exact on `[0,1]`, `1` above).

INTERNAL: step of the proof of atoms_have_expected_value_one.
TEXLINE: analysis.tex:475-486 -/
theorem digitCoin_true_le (x : ℝ) (hx : 0 ≤ x) : digitCoin x true ≤ ENNReal.ofReal x := by
  rcases le_or_gt x 1 with h1 | h1
  · exact (Nfa.Analysis.digitCoin_apply_true x hx h1).le
  · exact (PMF.coe_le_one _ _).trans (ENNReal.one_le_ofReal.2 h1.le)

/-- Expectation of a heads-indicator.

INTERNAL: step of the proof of atoms_have_expected_value_one.
TEXLINE: analysis.tex:475-486 -/
theorem ex_bool {D : PMF Bool} (c : ℝ≥0∞) :
    ex D (fun b => if b = true then c else 0) = D true * c := by
  unfold ex
  rw [tsum_fintype, Fintype.sum_bool]
  simp

/-- `Pr[w ∈ reduce(T, x)] ≤ 1_{w ∈ T} · x`.

INTERNAL: step of the proof of atoms_have_expected_value_one.
TEXLINE: analysis.tex:475-486 -/
theorem ex_reduce_mem_le (T : Finset (List Bool)) (x : ℝ) (hx : 0 ≤ x) (w : List Bool)
    (c : ℝ≥0∞) :
    ex (reduce T x) (fun T' => if w ∈ T' then c else 0) ≤
      if w ∈ T then c * ENNReal.ofReal x else 0 := by
  unfold reduce
  rw [ex_map]
  by_cases hw : w ∈ T
  · rw [if_pos hw]
    have := ex_drawAll_eval (fun _ => digitCoin x) false T.toList T.nodup_toList w
      (Finset.mem_toList.2 hw) (fun b => if b = true then c else 0)
    rw [show ((fun T' => if w ∈ T' then c else 0) ∘
        fun keep : List Bool → Bool => T.filter (keep · = true)) =
        fun g => (fun b => if b = true then c else 0) (g w) by
      funext g; simp [Finset.mem_filter, hw], this, ex_bool, mul_comm]
    exact mul_le_mul_right (digitCoin_true_le x hx) _
  · rw [if_neg hw]
    rw [show ((fun T' => if w ∈ T' then c else 0) ∘
        fun keep : List Bool → Bool => T.filter (keep · = true)) = fun _ => 0 by
      funext g; simp [Finset.mem_filter, hw], ex_const]

section Core
variable {Q : Type} [Fintype Q] [LinearOrder Q]

omit [Fintype Q] [LinearOrder Q] in
/-- A word `u·b` survives the selector union only through `σ.pick q u b`.

INTERNAL: step of the proof of atoms_have_expected_value_one.
TEXLINE: analysis.tex:475-486 -/
theorem mem_unionSel_concat {A : PaperNFA Q} (σ : Selector A) (q : Q) (preds : Finset Q)
    (bar : Q → Finset (List Bool)) (u : List Bool) (b : Bool)
    (h : u ++ [b] ∈ unionSel σ q preds bar) :
    ∃ q', σ.pick q u b = some q' ∧ q' ∈ preds ∧ u ++ [b] ∈ bar q' := by
  classical
  unfold unionSel at h
  simp only [Finset.mem_biUnion, Finset.mem_filter] at h
  obtain ⟨q', hq', hmem, w, b', heq, hpick⟩ := h
  obtain ⟨rfl, rfl⟩ : w = u ∧ b' = b := by simpa using heq.symm
  exact ⟨q', hpick, hq', hmem⟩

/-- `Pr[u·b ∈ hat S^r(q)] ≤ 1_{u ∈ S^r(q')} · ρ/p(q')` for `q' = σ(u·b, q)`.

INTERNAL: step of the proof of atoms_have_expected_value_one.
TEXLINE: analysis.tex:475-486 -/
theorem ex_hatSample_le (A : PaperNFA Q) (σ : Selector A) (st : CoreState Q) (i : ℕ) (q : Q)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hp : ∀ q', 0 ≤ st.p (i - 1) q') (r : ℕ) (u : List Bool) (b : Bool)
    (c : ℝ≥0∞) :
    ex (hatSample A σ st i q ρ r) (fun T => if u ++ [b] ∈ T then c else 0) ≤
      Option.elim (σ.pick q u b) 0 fun q' =>
        if u ∈ st.S (i - 1) q' r then c * ENNReal.ofReal (ρ / st.p (i - 1) q') else 0 := by
  unfold hatSample
  rw [ex_map]
  rcases hpk : σ.pick q u b with _ | q'
  · show _ ≤ 0
    refine le_of_eq ((ex_congr _ fun bar _ => ?_).trans (ex_const _ 0))
    simp only [Function.comp_apply]
    split_ifs with hm
    · obtain ⟨q', hq', -⟩ := mem_unionSel_concat σ q _ bar u b hm
      simp [hpk] at hq'
    · rfl
  · simp only [Option.elim]
    by_cases hq' : q' ∈ pred A i q
    · calc ex (drawAll (normalize A st i q ρ r) ∅ (predList A i q))
            ((fun T => if u ++ [b] ∈ T then c else 0) ∘ unionSel σ q (pred A i q))
          ≤ ex (drawAll (normalize A st i q ρ r) ∅ (predList A i q))
            (fun bar => (fun T => if u ++ [b] ∈ T then c else 0) (bar q')) := by
            refine ex_mono _ fun bar _ => ?_
            simp only [Function.comp_apply]
            split_ifs with hm hm'
            · exact le_rfl
            · obtain ⟨q'', h1, -, h3⟩ := mem_unionSel_concat σ q _ bar u b hm
              rw [hpk] at h1
              cases h1
              exact absurd h3 hm'
            · exact bot_le
            · exact le_rfl
        _ = ex (normalize A st i q ρ r q') (fun T => if u ++ [b] ∈ T then c else 0) :=
            ex_drawAll_eval (normalize A st i q ρ r) ∅ (predList A i q)
              (by unfold predList; exact Finset.sort_nodup _ _) q'
              (by unfold predList; exact (Finset.mem_sort _).2 hq')
              (fun T => if u ++ [b] ∈ T then c else 0)
        _ ≤ if u ++ [b] ∈ extendSet (st.S (i - 1) q' r) (labels A q' q) then
              c * ENNReal.ofReal (ρ / st.p (i - 1) q') else 0 :=
            ex_reduce_mem_le _ _ (div_nonneg hρ (hp q')) _ _
        _ ≤ _ := by
            split_ifs with h1 h2
            · exact le_rfl
            · exfalso; apply h2
              unfold extendSet at h1
              simp only [Finset.mem_image, Finset.mem_product] at h1
              obtain ⟨⟨x, b'⟩, ⟨hx, -⟩, heq⟩ := h1
              obtain ⟨rfl, rfl⟩ : x = u ∧ b' = b := by simpa using heq
              exact hx
            · exact bot_le
            · exact le_rfl
    · refine le_trans (le_of_eq ?_) bot_le
      refine (ex_congr _ fun bar _ => ?_).trans
        (ex_const (drawAll (normalize A st i q ρ r) ∅ (predList A i q)) 0)
      simp only [Function.comp_apply]
      split_ifs with hm
      · obtain ⟨q'', h1, h2, -⟩ := mem_unionSel_concat σ q _ bar u b hm
        rw [hpk] at h1
        cases h1
        exact absurd h2 hq'
      · rfl

omit [Fintype Q] [LinearOrder Q] in
/-- The empty word is never in a selector union.

INTERNAL: step of the proof of atoms_have_expected_value_one.
TEXLINE: analysis.tex:475-486 -/
theorem nil_not_mem_unionSel {A : PaperNFA Q} (σ : Selector A) (q : Q) (preds : Finset Q)
    (bar : Q → Finset (List Bool)) : [] ∉ unionSel σ q preds bar := by
  classical
  intro h
  unfold unionSel at h
  simp only [Finset.mem_biUnion, Finset.mem_filter] at h
  obtain ⟨_, _, _, w, b, heq, _⟩ := h
  simp at heq

/-- `λ ∉ hat S^r(q)`.

INTERNAL: step of the proof of atoms_have_expected_value_one.
TEXLINE: analysis.tex:475-486 -/
theorem ex_hatSample_nil (A : PaperNFA Q) (σ : Selector A) (st : CoreState Q) (i : ℕ) (q : Q)
    (ρ : ℝ) (r : ℕ) (c : ℝ≥0∞) :
    ex (hatSample A σ st i q ρ r) (fun T => if [] ∈ T then c else 0) = 0 := by
  unfold hatSample
  rw [ex_map]
  refine (ex_congr _ fun bar _ => ?_).trans (ex_const _ 0)
  simp [nil_not_mem_unionSel]

/-- All `p` values of a state are positive.

INTERNAL: invariant of the proof.
TEXLINE: analysis.tex:475-486 -/
def PosP (st : CoreState Q) : Prop := ∀ ℓ q, 0 < st.p ℓ q

omit [LinearOrder Q] in
/-- `ρ(q) > 0` when every `p` is positive.

INTERNAL: step of the proof of atoms_have_expected_value_one.
TEXLINE: analysis.tex:475-486 -/
theorem rho_pos (A : PaperNFA Q) (st : CoreState Q) (h : PosP st) (i : ℕ) (q : Q) :
    0 < rho A st i q := by
  unfold rho
  split_ifs with hne
  · exact (Finset.lt_inf'_iff hne).2 fun q' _ => h _ _
  · exact one_pos

omit [Fintype Q] [LinearOrder Q] in
/-- `p(q) = takeMin ρ med > 0` when `ρ > 0`.

INTERNAL: step of the proof of atoms_have_expected_value_one.
TEXLINE: analysis.tex:475-486 -/
theorem takeMin_pos (ρ med : ℝ) (hρ : 0 < ρ) : 0 < takeMin ρ med := by
  unfold takeMin
  split_ifs with h
  · exact hρ
  · exact lt_min hρ (by rw [not_le] at h; positivity)

/-- One `estimateAndSample` step: the final-reduce coin cancels `1/p(q)`, leaving `1/ρ(q)` times `Pr[w ∈ hat S^r(q)]`.

INTERNAL: step of the proof of atoms_have_expected_value_one.
TEXLINE: analysis.tex:475-486 -/
theorem ex_eAS_atom_le_of (A : PaperNFA Q) (σ : Selector A) (P : Params) (i : ℕ)
    (st : CoreState Q) (hst : PosP st) (q : Q) (r : ℕ) (w : List Bool) (B : ℝ≥0∞)
    (hB : ex (hatSample A σ st i q (rho A st i q) r)
      (fun T => if w ∈ T then ENNReal.ofReal (1 / rho A st i q) else 0) ≤ B) :
    ex (estimateAndSample A σ P i st q) (Nfa.Analysis.atomVal r i q w) ≤ B := by
  set ρ := rho A st i q with hρdef
  have hρ : 0 < ρ := rho_pos A st hst i q
  unfold estimateAndSample
  rw [ex_bind]
  have hinner : ∀ hatS : ℕ → Finset (List Bool),
      ex ((finalReduce P hatS ρ (takeMin ρ (blockMedian P ρ hatS))).map fun S' =>
        ({ st with
          p := Function.update st.p i (Function.update (st.p i) q
            (takeMin ρ (blockMedian P ρ hatS)))
          S := Function.update st.S i (Function.update (st.S i) q S') } : CoreState Q))
        (Nfa.Analysis.atomVal r i q w) ≤
      (fun g : ℕ → Finset (List Bool) => if r ∈ List.range P.α then
        (fun T => if w ∈ T then ENNReal.ofReal (1 / ρ) else 0) (g r) else 0) hatS := by
    intro hatS
    set p := takeMin ρ (blockMedian P ρ hatS)
    have hp : 0 < p := takeMin_pos _ _ hρ
    rw [ex_map]
    have hfun : (Nfa.Analysis.atomVal r i q w ∘ fun S' : ℕ → Finset (List Bool) =>
        ({ st with
          p := Function.update st.p i (Function.update (st.p i) q p)
          S := Function.update st.S i (Function.update (st.S i) q S') } : CoreState Q)) =
        fun g => (fun T => if w ∈ T then ENNReal.ofReal (1 / p) else 0) (g r) := by
      funext g
      simp [Nfa.Analysis.atomVal]
    rw [hfun]
    unfold finalReduce
    by_cases hr : r ∈ List.range P.α
    · rw [ex_drawAll_eval _ _ _ List.nodup_range r hr
        (fun T => if w ∈ T then ENNReal.ofReal (1 / p) else 0)]
      simp only [if_pos hr]
      refine (ex_reduce_mem_le _ _ (div_nonneg hp.le hρ.le) _ _).trans (le_of_eq ?_)
      split_ifs
      · rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
      · rfl
    · rw [ex_drawAll_eval_not_mem _ _ _ r hr
        (fun T => if w ∈ T then ENNReal.ofReal (1 / p) else 0)]
      simp [hr]
  refine (ex_mono _ fun hatS _ => hinner hatS).trans ?_
  unfold hatSamples
  by_cases hr : r ∈ List.range P.α
  · simp only [if_pos hr]
    rw [ex_drawAll_eval _ _ _ List.nodup_range r hr
      (fun T => if w ∈ T then ENNReal.ofReal (1 / ρ) else 0)]
    exact hB
  · simp only [if_neg hr, ex_const]
    exact bot_le

/-- `1_{w ∈ L(q^ℓ)}`.

INTERNAL: the right-hand side of the atom bound.
TEXLINE: analysis.tex:475-478 -/
noncomputable def langInd (A : PaperNFA Q) (ℓ : ℕ) (q : Q) (w : List Bool) : ℝ≥0∞ :=
  Set.indicator {w : List Bool | w.length = ℓ ∧ q ∈ A.toNFA.eval w} 1 w

omit [Fintype Q] [LinearOrder Q] in
/-- The canonical parent `(u, σ(u·b, q))` of `(u·b, q)` lies in `L` one layer down only if `u·b ∈ L(q)`.

INTERNAL: step of the proof of atoms_have_expected_value_one.
TEXLINE: analysis.tex:475-486 -/
theorem langInd_le (A : PaperNFA Q) (σ : Selector A) (i : ℕ) (hi : 1 ≤ i) (q q' : Q)
    (u : List Bool) (b : Bool) (hpick : σ.pick q u b = some q') :
    langInd A (i - 1) q' u ≤ langInd A i q (u ++ [b]) := by
  unfold langInd
  by_cases hu : u ∈ {w : List Bool | w.length = i - 1 ∧ q' ∈ A.toNFA.eval w}
  · have hw : u ++ [b] ∈ {w : List Bool | w.length = i ∧ q ∈ A.toNFA.eval w} := by
      obtain ⟨hlen, -⟩ := hu
      obtain ⟨hδ, hq'⟩ := σ.pick_sound q u b q' hpick
      refine ⟨by simp [hlen]; omega, ?_⟩
      rw [NFA.eval_append_singleton, NFA.mem_stepSet]
      exact ⟨q', hq', hδ⟩
    rw [Set.indicator_of_mem hu, Set.indicator_of_mem hw]
    simp
  · rw [Set.indicator_of_notMem hu]
    exact bot_le

/-- The invariant carried along `countNFAcore*`: positive `p`, and every atom has
expectation at most `1_{w ∈ L(q^ℓ)}`.

INTERNAL: induction hypothesis of the proof.
TEXLINE: analysis.tex:480-486 -/
def Inv (A : PaperNFA Q) (r : ℕ) (D : PMF (CoreState Q)) : Prop :=
  (∀ st ∈ D.support, PosP st) ∧
    ∀ ℓ q w, ex D (Nfa.Analysis.atomVal r ℓ q w) ≤ langInd A ℓ q w

/-- `estimateAndSample` keeps every `p` positive.

INTERNAL: step of the proof of atoms_have_expected_value_one.
TEXLINE: analysis.tex:475-486 -/
theorem eAS_support_pos (A : PaperNFA Q) (σ : Selector A) (P : Params) (i : ℕ)
    (st : CoreState Q) (hst : PosP st) (q : Q) :
    ∀ st' ∈ (estimateAndSample A σ P i st q).support, PosP st' := by
  intro st' h
  unfold estimateAndSample at h
  rw [PMF.mem_support_bind_iff] at h
  obtain ⟨hatS, -, h⟩ := h
  rw [PMF.mem_support_map_iff] at h
  obtain ⟨S', -, rfl⟩ := h
  intro ℓ q₀
  by_cases h1 : ℓ = i
  · subst h1
    by_cases h2 : q₀ = q
    · subst h2
      simpa using takeMin_pos _ _ (rho_pos A st hst ℓ q₀)
    · simpa [Function.update_of_ne h2] using hst ℓ q₀
  · simpa [Function.update_of_ne h1] using hst ℓ q₀

/-- `estimateAndSample` at `(i, q)` leaves every other atom unchanged.

INTERNAL: step of the proof of atoms_have_expected_value_one.
TEXLINE: analysis.tex:475-486 -/
theorem ex_eAS_atom_other (A : PaperNFA Q) (σ : Selector A) (P : Params) (i : ℕ)
    (st : CoreState Q) (q : Q) (r ℓ : ℕ) (q₀ : Q) (w : List Bool) (h : ¬(ℓ = i ∧ q₀ = q)) :
    ex (estimateAndSample A σ P i st q) (Nfa.Analysis.atomVal r ℓ q₀ w) =
      Nfa.Analysis.atomVal r ℓ q₀ w st := by
  unfold estimateAndSample
  rw [ex_bind]
  refine (ex_congr _ fun hatS _ => ?_).trans (ex_const _ _)
  rw [ex_map]
  refine (ex_congr _ fun S' _ => ?_).trans (ex_const _ _)
  have hS : Function.update st.S i (Function.update (st.S i) q S') ℓ q₀ = st.S ℓ q₀ := by
    by_cases h1 : ℓ = i
    · subst h1
      have h2 : q₀ ≠ q := fun h2 => h ⟨rfl, h2⟩
      simp [Function.update_of_ne h2]
    · simp [Function.update_of_ne h1]
  have hp : ∀ x, Function.update st.p i (Function.update (st.p i) q x) ℓ q₀ = st.p ℓ q₀ := by
    intro x
    by_cases h1 : ℓ = i
    · subst h1
      have h2 : q₀ ≠ q := fun h2 => h ⟨rfl, h2⟩
      simp [Function.update_of_ne h2]
    · simp [Function.update_of_ne h1]
  simp only [Function.comp_apply, Nfa.Analysis.atomVal, hS, hp]

/-- One `estimateAndSample` step preserves `Inv` (tower rule, analysis.tex:480-486).

INTERNAL: step of the proof of atoms_have_expected_value_one.
TEXLINE: analysis.tex:475-486 -/
theorem Inv_step (A : PaperNFA Q) (σ : Selector A) (P : Params) (r : ℕ) (i : ℕ) (hi : 1 ≤ i)
    (q : Q) (D : PMF (CoreState Q)) (hD : Inv A r D) :
    Inv A r (D.bind fun st => estimateAndSample A σ P i st q) := by
  obtain ⟨hpos, hex⟩ := hD
  refine ⟨fun st' h => ?_, fun ℓ q₀ w => ?_⟩
  · rw [PMF.mem_support_bind_iff] at h
    obtain ⟨st, hst, h⟩ := h
    exact eAS_support_pos A σ P i st (hpos st hst) q st' h
  rw [ex_bind]
  by_cases hiq : ℓ = i ∧ q₀ = q
  · obtain ⟨rfl, rfl⟩ := hiq
    rcases List.eq_nil_or_concat w with rfl | ⟨u, b, rfl⟩
    · refine (ex_mono _ (g := fun _ => 0) fun st hst => ?_).trans ?_
      · exact ex_eAS_atom_le_of A σ P ℓ st (hpos st hst) q₀ r [] 0
          (ex_hatSample_nil A σ st ℓ q₀ _ r _).le
      · rw [ex_const]; exact bot_le
    · rw [List.concat_eq_append]
      refine (ex_mono _ (g := fun st => Option.elim (σ.pick q₀ u b) 0 fun q' =>
          Nfa.Analysis.atomVal r (ℓ - 1) q' u st) fun st hst => ?_).trans ?_
      · refine ex_eAS_atom_le_of A σ P ℓ st (hpos st hst) q₀ r _ _ ?_
        have hρ := rho_pos A st (hpos st hst) ℓ q₀
        refine (ex_hatSample_le A σ st ℓ q₀ _ hρ.le (fun q' => (hpos st hst _ _).le) r u b _).trans
          (le_of_eq ?_)
        rcases σ.pick q₀ u b with _ | q'
        · rfl
        · simp only [Option.elim, Nfa.Analysis.atomVal]
          split_ifs
          · rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            field_simp
          · rfl
      · rcases hpk : σ.pick q₀ u b with _ | q'
        · simp only [Option.elim, ex_const]; exact bot_le
        · simp only [Option.elim]
          exact (hex _ _ _).trans (langInd_le A σ ℓ hi q₀ q' u b hpk)
  · refine le_trans (le_of_eq ?_) (hex ℓ q₀ w)
    exact ex_congr _ fun st _ => ex_eAS_atom_other A σ P i st q r ℓ q₀ w hiq

/-- `runStar` along a list of layers `≥ 1` preserves `Inv`.

INTERNAL: step of the proof of atoms_have_expected_value_one.
TEXLINE: analysis.tex:475-486 -/
theorem Inv_runStar (A : PaperNFA Q) (σ : Selector A) (P : Params) (r : ℕ) :
    ∀ (xs : List (ℕ × Q)), (∀ x ∈ xs, 1 ≤ x.1) → ∀ D : PMF (CoreState Q), Inv A r D →
      Inv A r (D.bind fun st => runStar A σ P st xs)
  | [], _, D, hD => by simpa [runStar] using hD
  | x :: xs, hxs, D, hD => by
      simp only [runStar]
      rw [← PMF.bind_bind]
      exact Inv_runStar A σ P r xs (fun y hy => hxs y (List.mem_cons_of_mem _ hy)) _
        (Inv_step A σ P r x.1 (hxs x List.mem_cons_self) x.2 D hD)

omit [Fintype Q] in
/-- `initState` satisfies `Inv` (the base case, analysis.tex:481-482).

INTERNAL: step of the proof of atoms_have_expected_value_one.
TEXLINE: analysis.tex:475-486 -/
theorem Inv_init (A : PaperNFA Q) (P : Params) (r : ℕ) : Inv A r (PMF.pure (initState A P)) := by
  refine ⟨fun st h => ?_, fun ℓ q w => ?_⟩
  · rw [PMF.mem_support_pure_iff] at h
    subst h
    intro ℓ q
    simp [initState]
  · rw [ex_pure]
    unfold Nfa.Analysis.atomVal langInd
    by_cases h : w ∈ (initState A P).S ℓ q r
    · rw [if_pos h]
      simp only [initState] at h
      split_ifs at h with h0
      · obtain ⟨rfl, rfl, -⟩ := h0
        rw [Finset.mem_singleton] at h
        subst h
        rw [Set.indicator_of_mem (by simp [PaperNFA.toNFA])]
        simp [initState]
      · simp at h
    · rw [if_neg h]; exact bot_le

/-- Every listed state of `countNFAcore*` is in a layer `≥ 1`.

INTERNAL: step of the proof of atoms_have_expected_value_one.
TEXLINE: analysis.tex:475-486 -/
theorem corePairs_fst (A : PaperNFA Q) (n : ℕ) : ∀ x ∈ corePairs A n, 1 ≤ x.1 := by
  intro x hx
  unfold corePairs at hx
  simp only [List.mem_flatMap, List.mem_map, List.mem_range'] at hx
  obtain ⟨i, ⟨k, hk, rfl⟩, q, -, rfl⟩ := hx
  simp

end Core
end Nfa.Analysis.AtomAux

namespace Nfa.Analysis

open Nfa.Pseudocode

variable {Q : Type} [Fintype Q] [LinearOrder Q]

/-- **Atoms have expectation at most one** in `countNFAcore*`: for every `r`, `ℓ`,
`q` and word `w`, `E[A_r(w, q^ℓ)] ≤ 1_{w ∈ L(q^ℓ)}`.

PAPER: analysis.tex:475-486 (Proposition atoms_have_expected_value_one, the `≤`
half, for `N*`; the paper's equality is not needed by proba_S(q)). -/
theorem atom_expectation_le (A : PaperNFA Q) (σ : Selector A) (P : Params) (n r ℓ : ℕ)
    (q : Q) (w : List Bool) :
    ∑' st, coreLawStar A σ P n st * atomVal r ℓ q w st ≤
      Set.indicator {w : List Bool | w.length = ℓ ∧ q ∈ A.toNFA.eval w} 1 w := by
  have h := (AtomAux.Inv_runStar A σ P r (corePairs A n) (AtomAux.corePairs_fst A n) _
    (AtomAux.Inv_init A P r)).2 ℓ q w
  rw [PMF.pure_bind] at h
  exact h

end Nfa.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · proved · invariant along `runStar` (positive `p`, atom bound), one step via the coin marginals of `drawAll`
-/
