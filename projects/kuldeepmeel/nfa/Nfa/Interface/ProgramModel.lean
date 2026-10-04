import Nfa.Model.Program
import Nfa.Interface.Pseudocode
import Nfa.Interface.Encoding
import Nfa.Model.Prior
import Nfa.Model.Prelude
import Nfa.Model.Operations
import Nfa.Model.Run
import Nfa.Analysis.ScalarMedianBridge
import Nfa.Analysis.LayerStepFrame

/-!
# The program and the model are the same algorithm

`Nfa.Model.Program` is what the paper's claims are about: a charged
computation whose state is sealed and whose cost is an operator applied to it.
`Nfa.Interface.Pseudocode` is the same algorithm as mathematics for the
answer/output object the correctness theorem measures. Time and space stay over
`Nfa.Model.Program`; this file is only the transport for correctness.

It is a ladder. Each theorem below is proved from the ones above it, and
`output_eq_countOutput` is the top: it is the one lemma the analysis rewrites
through, and the only one anything outside this file should need.

Every rung is proved; the three bridges `layerStep_bridge` → `runLayers_bridge` →
`coreRun_bridge` rest on deterministic program facts (`estimateAndSample_local`,
`estimateAndSample_sample`, `layerStep_invariants`, `layerStep_local`) and on the
bind-transfer lemma `pmf_bind_transfer`, which lets a program state and a pseudocode
state that agree on the bridged projection be continued in lock-step.
-/

set_option autoImplicit false

namespace Nfa

/-- The program's tape law over a list of sites is the same distribution as the pseudocode's sequential `drawAll` of one coin index per site. Every later rung relies on this to move from the shared tape to the pseudocode's monadic draws. -/
theorem tapeLaw_eq_drawAll {Q : Type} [Fintype Q] [LinearOrder Q] (L : List (Nfa.Model.Operations.Site Q)) : Nfa.Run.tapeLaw L = Nfa.Pseudocode.drawAll (fun _ => Nfa.Run.coinIndex) 0 L := by
  induction L with
  | nil => rfl
  | cons s ss ih => simp [Nfa.Run.tapeLaw, Nfa.Pseudocode.drawAll, ih]

/-- A charged coin flip at a site reads off the same Bernoulli outcome as the pseudocode's `digit` of that site's tape value at the real rate `p`. -/
theorem coin_val_eq_digit {Q : Type} (site : Nfa.Model.Operations.Site Q) (p : Nfa.Model.Operations.Scalar) (f : Nfa.Model.Operations.Site Q → ℕ) : (Nfa.Model.Operations.coin site p (Nfa.Model.Operations.Tape.ofFun f)).val = Nfa.Pseudocode.digit (f site) ((p.get : ℚ) : ℝ) := by
  simp [Nfa.Pseudocode.bernoulliDigit_eq_digit]

section DrawAllHelpers

open Nfa.Pseudocode

/-- INTERNAL: independent draws over `L1 ++ L2` are the draws over `L1` followed by those over `L2`, with `L1` winning on overlaps. Generic `drawAll` bookkeeping for the bridges. TEXLINE: algorithm.tex:52 -/
theorem drawAll_append' {ι β : Type} [DecidableEq ι] (f : ι → PMF β) (d : β) (L1 L2 : List ι) :
    drawAll f d (L1 ++ L2) = (drawAll f d L1).bind fun g1 =>
      (drawAll f d L2).map fun g2 x => if x ∈ L1 then g1 x else g2 x := by
  induction L1 with
  | nil =>
    simp only [List.nil_append, drawAll, PMF.pure_bind]
    exact (PMF.map_id _).symm
  | cons a L1 ih =>
    simp only [List.cons_append, drawAll, ih, PMF.map_bind, PMF.bind_bind, PMF.bind_map,
      PMF.map_comp]
    congr 1; funext b; congr 1; funext g1
    simp only [Function.comp_apply]
    congr 1; funext g2 x
    by_cases hx : x = a
    · subst hx; simp
    · simp [hx]

/-- INTERNAL: a statistic reading only the coordinates in `L1` does not see the draws over an appended `L2`. -/
theorem drawAll_append_map {ι β γ : Type} [DecidableEq ι] (f : ι → PMF β) (d : β) (L1 L2 : List ι)
    (G : (ι → β) → γ) (hG : ∀ g g', (∀ x ∈ L1, g x = g' x) → G g = G g') :
    (drawAll f d (L1 ++ L2)).map G = (drawAll f d L1).map G := by
  rw [drawAll_append', PMF.map_bind]
  have : ∀ g1, ((drawAll f d L2).map fun g2 x => if x ∈ L1 then g1 x else g2 x).map G
      = PMF.pure (G g1) := by
    intro g1
    rw [PMF.map_comp]
    have : (G ∘ fun (g2 : ι → β) x => if x ∈ L1 then g1 x else g2 x) = Function.const _ (G g1) := by
      funext g2; exact hG _ _ (fun x hx => by simp [hx])
    rw [this, PMF.map_const]
  simp only [this]; rfl

/-- INTERNAL: for a duplicate-free index list, the order of the independent draws does not matter. -/
theorem drawAll_perm {ι β : Type} [DecidableEq ι] (f : ι → PMF β) (d : β) {L L' : List ι}
    (h : L.Perm L') (hL : L.Nodup) : drawAll f d L = drawAll f d L' := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [drawAll, ih (List.nodup_cons.mp hL).2]
  | swap x y l =>
    have hxy : y ≠ x := by
      intro h; subst h; simp at hL
    simp only [drawAll, PMF.map_bind, PMF.map_comp]
    rw [PMF.bind_comm]
    congr 1; funext a; congr 1; funext b; congr 1; funext g
    simp [Function.update_comm hxy]
  | trans h1 _ ih1 ih2 => rw [ih1 hL, ih2 (h1.nodup_iff.mp hL)]

/-- INTERNAL: marginalisation — a statistic reading only the coordinates in `L' ⊆ L` has the same law under the draws over `L` as under those over `L'`. This is the step that discards the tape's unread sites. -/
theorem drawAll_marginal {ι β γ : Type} [DecidableEq ι] (f : ι → PMF β) (d : β) (L L' : List ι)
    (hL : L.Nodup) (hL' : L'.Nodup) (hsub : ∀ x ∈ L', x ∈ L)
    (G : (ι → β) → γ) (hG : ∀ g g', (∀ x ∈ L', g x = g' x) → G g = G g') :
    (drawAll f d L).map G = (drawAll f d L').map G := by
  have hp : L.Perm (L' ++ L.filter (fun x => x ∉ L')) := by
    rw [List.perm_ext_iff_of_nodup hL]
    · intro x; by_cases hx : x ∈ L' <;> simp [hx, hsub]
    · rw [List.nodup_append]
      refine ⟨hL', hL.filter _, ?_⟩
      intro a ha b hb; simp at hb; rintro rfl; exact hb.2 ha
  rw [drawAll_perm f d hp hL, drawAll_append_map f d _ _ G hG]

/-- INTERNAL: reading Geometric indices through an injective site map and the digit rule is the same as drawing `digitCoin p` per element. -/
theorem drawAll_digit {α ι γ : Type} [DecidableEq α] [DecidableEq ι] (s : α → ι)
    (hs : Function.Injective s) (p : ℝ) (X : List α) (H : (α → Bool) → γ)
    (hH : ∀ k k', (∀ u ∈ X, k u = k' u) → H k = H k') :
    (drawAll (fun _ => Run.coinIndex) 0 (X.map s)).map (fun g => H (fun u => digit (g (s u)) p))
      = (drawAll (fun _ => digitCoin p) false X).map H := by
  induction X generalizing H with
  | nil =>
    simp only [List.map_nil, drawAll, PMF.pure_map]
    rw [hH _ (fun _ => false) (by simp)]
  | cons u X ih =>
    simp only [List.map_cons, drawAll, PMF.map_bind, PMF.map_comp, digitCoin, PMF.bind_map]
    congr 1; funext c
    have key : ∀ g : ι → ℕ, (fun u' => digit (Function.update g (s u) c (s u')) p)
        = Function.update (fun u' => digit (g (s u')) p) u (digit c p) := by
      intro g; funext u'
      by_cases hu : u' = u
      · subst hu; simp
      · rw [Function.update_of_ne hu, Function.update_of_ne (hs.ne hu)]
    have := ih (fun k => H (Function.update k u (digit c p))) (by
      intro k k' hk; apply hH; intro v hv
      by_cases hvu : v = u
      · subst hvu; simp
      · rw [Function.update_of_ne hvu, Function.update_of_ne hvu]
        exact hk v (by simpa [hvu] using hv))
    simp only [Function.comp_def, key]
    rw [PMF.map_comp]
    exact this

/-- INTERNAL: `reduce S p` is the filter of `S` by the digit rule applied to independent Geometric indices at injectively-assigned sites. -/
theorem reduce_eq_coins {ι : Type} [DecidableEq ι] (s : List Bool → ι) (hs : Function.Injective s)
    (S : Finset (List Bool)) (p : ℝ) :
    reduce S p = (drawAll (fun _ => Run.coinIndex) 0 (S.toList.map s)).map
      (fun g => S.filter (fun u => digit (g (s u)) p = true)) := by
  unfold reduce
  rw [drawAll_digit s hs p S.toList (fun k => S.filter (k · = true))]
  intro k k' hk
  exact Finset.filter_congr (fun u hu => by rw [hk u (Finset.mem_toList.mpr hu)])

/-- INTERNAL: one shared tape, read at pairwise-distinct sites `s a u`, realises independent `reduce (E a) (p a)` draws for all `a ∈ ps` at once. This is the independence of the per-predecessor normalisations of eAS.2. TEXLINE: algorithm.tex:64-84 -/
theorem drawAll_reduce_joint {α ι : Type} [DecidableEq α] [DecidableEq ι]
    (s : α → List Bool → ι) (hs : ∀ a u a' u', s a u = s a' u' → a = a' ∧ u = u')
    (E : α → Finset (List Bool)) (p : α → ℝ) (ps : List α) (hps : ps.Nodup)
    (L : List ι) (hL : L.Nodup) (hcov : ∀ a ∈ ps, ∀ u ∈ E a, s a u ∈ L) :
    (drawAll (fun _ => Run.coinIndex) 0 L).map
      (fun f a => if a ∈ ps then (E a).filter (fun u => digit (f (s a u)) (p a) = true) else ∅)
      = drawAll (fun a => reduce (E a) (p a)) ∅ ps := by
  have hinj : ∀ a, Function.Injective (s a) := fun a u u' h => (hs a u a u' h).2
  set L0 : List α → List ι := fun ps => ps.flatMap fun a => (E a).toList.map (s a) with hL0
  have hmem0 : ∀ ps x, x ∈ L0 ps ↔ ∃ a ∈ ps, ∃ u ∈ E a, s a u = x := by
    intro ps x; simp [hL0]
  have hnd0 : ∀ ps : List α, ps.Nodup → (L0 ps).Nodup := by
    intro ps hps
    induction ps with
    | nil => simp [hL0]
    | cons a ps ih =>
      have h1 := List.nodup_cons.mp hps
      show ((E a).toList.map (s a) ++ L0 ps).Nodup
      rw [List.nodup_append]
      refine ⟨(Finset.nodup_toList _).map (hinj a), ih h1.2, ?_⟩
      intro x hx y hy hxy
      subst hxy
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
      obtain ⟨a', ha', u', -, he⟩ := (hmem0 ps _).mp hy
      exact h1.1 ((hs _ _ _ _ he).1 ▸ ha')
  rw [drawAll_marginal _ _ L (L0 ps) hL (hnd0 ps hps)
    (fun x hx => by obtain ⟨a, ha, u, hu, rfl⟩ := (hmem0 ps x).mp hx; exact hcov a ha u hu)]
  swap
  · intro g g' hg; funext a
    split_ifs with ha
    · exact Finset.filter_congr fun u hu => by rw [hg _ ((hmem0 ps _).mpr ⟨a, ha, u, hu, rfl⟩)]
    · rfl
  clear hcov hL L
  induction ps with
  | nil =>
    simp only [hL0, List.flatMap_nil, drawAll, PMF.pure_map]
    congr 1
  | cons a ps ih =>
    have h1 := List.nodup_cons.mp hps
    show (drawAll _ 0 ((E a).toList.map (s a) ++ L0 ps)).map _ = _
    rw [drawAll_append', PMF.map_bind, drawAll, reduce_eq_coins (s a) (hinj a), PMF.bind_map,
      ← ih h1.2]
    congr 1; funext g1
    simp only [Function.comp_apply, PMF.map_comp]
    congr 1; funext g2 a'
    by_cases ha' : a' = a
    · subst ha'
      simp only [List.mem_cons, true_or, if_true, Function.comp_apply, Function.update_self]
      exact Finset.filter_congr fun u hu => by
        rw [if_pos (List.mem_map.mpr ⟨u, Finset.mem_toList.mpr hu, rfl⟩)]
    · simp only [List.mem_cons, ha', false_or, Function.comp_apply,
        Function.update_of_ne ha']
      split_ifs with hps'
      · refine Finset.filter_congr fun u _ => ?_
        rw [if_neg]
        intro hm
        obtain ⟨v, -, hv⟩ := List.mem_map.mp hm
        exact ha' (hs _ _ _ _ hv).1.symm
      · rfl

/-- INTERNAL: `Run.words i` lists exactly the words of length `i`. -/
theorem words_mem_iff (i : ℕ) (u : List Bool) : u ∈ Nfa.Run.words i ↔ u.length = i := by
  induction i generalizing u with
  | zero => simp [Nfa.Run.words]
  | succ i ih =>
    simp only [Nfa.Run.words, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false, ih]
    constructor
    · rintro ⟨w, hw, rfl | rfl⟩ <;> simp [hw]
    · intro hu
      obtain ⟨w, b, rfl⟩ : ∃ w b, u = w ++ [b] := by
        obtain ⟨w, b, h⟩ := List.eq_nil_or_concat u |>.resolve_left (by rintro rfl; simp at hu)
        exact ⟨w, b, by simpa using h⟩
      refine ⟨w, by simpa using hu, ?_⟩
      cases b <;> simp

/-- INTERNAL: `Run.words i` has no duplicates. -/
theorem words_nodup (i : ℕ) : (Nfa.Run.words i).Nodup := by
  induction i with
  | zero => simp [Nfa.Run.words]
  | succ i ih =>
    simp only [Nfa.Run.words]
    rw [List.nodup_flatMap]
    refine ⟨fun w _ => by simp, ih.pairwise_of_forall_ne ?_⟩
    intro a _ b _ hab x hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with h | h <;>
      exact hab (List.append_inj_left' h rfl)

/-- INTERNAL: membership in the result of a charged list fold whose step only adds elements described by `D`. -/
theorem cfoldl_mem_iff {κ κₛ α γ : Type} (F : List γ → α → Arlib.Computation.Charged κ κₛ (List γ))
    (D : α → γ → Prop) (hF : ∀ T x u, u ∈ (F T x).val ↔ u ∈ T ∨ D x u)
    (l : List α) (T0 : List γ) (u : γ) :
    u ∈ (Arlib.Computation.Charged.foldl F l T0).val ↔ u ∈ T0 ∨ ∃ x ∈ l, D x u := by
  induction l generalizing T0 with
  | nil => simp
  | cons a l ih =>
    simp only [Arlib.Computation.Charged.val_foldl_cons, ih, hF, List.mem_cons]
    constructor
    · rintro ((h | h) | ⟨x, hx, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨a, Or.inl rfl, h⟩
      · exact Or.inr ⟨x, Or.inr hx, h⟩
    · rintro (h | ⟨x, rfl | hx, h⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨x, hx, h⟩

end DrawAllHelpers

/-- The program's coin-driven thinning loop over a duplicate-free word list has the same law as the pseudocode's `reduce`, which keeps each element independently at rate p. -/
theorem reduce_bridge {Q : Type} [Fintype Q] [LinearOrder Q] (site : List Bool → Nfa.Model.Operations.Site Q) (hsite : Function.Injective site) (xs : List (List Bool)) (hxs : xs.Nodup) (p : Nfa.Model.Operations.Scalar) : (Nfa.Run.tapeLaw (xs.map site)).map (fun f => ((Arlib.Computation.Charged.foldl (fun (T : List (List Bool)) (u : List Bool) => do let kept ← Nfa.Model.Operations.coin (site u) p (Nfa.Model.Operations.Tape.ofFun f); if kept then Nfa.Model.Operations.addWord u T else pure T) xs []).val).toFinset) = Nfa.Pseudocode.reduce xs.toFinset ((p.get : ℚ) : ℝ) := by
  have hsl : (xs.map site).Perm (xs.toFinset.toList.map site) := by
    refine List.Perm.map _ ?_
    rw [List.perm_ext_iff_of_nodup hxs (Finset.nodup_toList _)]
    intro x; simp
  rw [tapeLaw_eq_drawAll, drawAll_perm _ _ hsl (hxs.map hsite),
    reduce_eq_coins site hsite]
  congr 1; funext f; ext u
  rw [List.mem_toFinset, cfoldl_mem_iff _ (fun x u => (Nfa.Model.Operations.coin (site x) p
    (Nfa.Model.Operations.Tape.ofFun f)).val = true ∧ u = x) ?h]
  case h =>
    intro T x u
    by_cases hc : (Nfa.Model.Operations.coin (site x) p
      (Nfa.Model.Operations.Tape.ofFun f)).val = true <;> simp [hc, or_comm]
  simp only [List.not_mem_nil, false_or, Finset.mem_filter, List.mem_toFinset,
    coin_val_eq_digit]
  constructor
  · rintro ⟨x, hx, hc, rfl⟩; exact ⟨hx, hc⟩
  · rintro ⟨hx, hc⟩; exact ⟨u, hx, hc, rfl⟩

/-- On a cached prefix, the program's cached witness test agrees with the pseudocode's selector predicate `chosen` for the extended word. -/
theorem isWitness_iff_chosen {Q : Type} [Fintype Q] [LinearOrder Q] {A : Nfa.PaperNFA Q} (σ : Nfa.Selector A) (cache : Arlib.Computation.Roster (List Bool)) (q : Q) (w : List Bool) (b : Bool) (q' : Q) (hw : w ∈ cache.toFinset) : (Nfa.Model.Operations.isWitness σ cache q w b q').val = true ↔ Nfa.Pseudocode.chosen σ q q' (w ++ [b]) := by
  unfold Nfa.Model.Operations.isWitness
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Roster.val_mem, hw,
    decide_true, if_true, Arlib.Computation.Charged.val_op]
  unfold Nfa.Pseudocode.chosen
  constructor
  · intro h
    exact ⟨w, b, rfl, by simpa using h⟩
  · rintro ⟨w', b', heq, hpick⟩
    have hb : [b'] = [b] := List.append_inj_right' heq.symm rfl
    have hwe : w' = w := List.append_inj_left' heq.symm rfl
    subst hwe
    simp only [List.cons.injEq] at hb
    obtain ⟨hb', -⟩ := hb
    subst hb'
    simpa using hpick

/-- Up to depth n, layer ℓ of the program's unrolled state array is the pseudocode's `layerList` at ℓ. -/
private theorem cfoldl_val {κ κₛ α β : Type} (f : β → α → Arlib.Computation.Charged κ κₛ β)
    (l : List α) (b : β) :
    (Arlib.Computation.Charged.foldl f l b).val = List.foldl (fun x a => (f x a).val) b l := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih => simp [ih]

set_option maxHeartbeats 1000000 in
private theorem unroll_succ_val {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (n : ℕ) :
    (Nfa.Program.unroll A (n+1)).val =
      (Nfa.Program.unroll A n).val.push
        (List.foldl (fun (acc : List Q) (q : Q) =>
            if (List.foldl (fun (hit : Bool) (q' : Q) =>
                  List.foldl (fun (hit : Bool) (b : Bool) => hit || A.delta q' b q) hit [false, true])
                false ((Nfa.Program.unroll A n).val.back?.getD []))
            then acc ++ [q] else acc) [] ((Finset.univ : Finset Q).sort (· ≤ ·))) := by
  have hn : (Nfa.Program.unroll A n).val =
      List.foldl (fun (layers : Array (List Q)) (_ : ℕ) =>
        (((do
            let last := layers.back?.getD []
            let next ← Arlib.Computation.Charged.foldl (fun (acc : List Q) (q : Q) => do
                let hit ← Arlib.Computation.Charged.foldl (fun (hit : Bool) (q' : Q) =>
                    Arlib.Computation.Charged.foldl (fun (hit : Bool) (b : Bool) => do
                        let t ← Nfa.Model.Operations.transition A q' b q
                        pure (hit || t)) [false, true] hit) last false
                pure (if hit then acc ++ [q] else acc)) ((Finset.univ : Finset Q).sort (· ≤ ·)) []
            pure (layers.push next)) :
              Arlib.Computation.Charged Nfa.Model.Operations.Op Nfa.Model.Operations.Cell (Array (List Q))).val))
        #[[A.qI]] (List.range n) := cfoldl_val _ _ _
  show (Arlib.Computation.Charged.foldl _ (List.range (n+1)) #[[A.qI]]).val = _
  rw [List.range_succ, cfoldl_val, List.foldl_append, ← hn]
  simp [cfoldl_val]
  rfl

private theorem unroll_size {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (n : ℕ) :
    (Nfa.Program.unroll A n).val.size = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [unroll_succ_val, Array.size_push, ih]

private theorem foldl_or_init_eq {α : Type} (f : α → Bool) (l : List α) (init : Bool) :
    List.foldl (fun (hit : Bool) (a : α) => hit || f a) init l =
      (init || List.foldl (fun (hit : Bool) (a : α) => hit || f a) false l) := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons]
    rw [ih (init || f a), ih (false || f a)]
    cases init <;> cases f a <;> simp

private theorem foldl_or_iff {α : Type} (p : α → Bool) (l : List α) (init : Bool) :
    List.foldl (fun hit a => hit || p a) init l = true ↔ init = true ∨ ∃ a ∈ l, p a = true := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih => simp [ih, Bool.or_eq_true, or_assoc]

private theorem foldl_hit_iff {Q : Type} (A : Nfa.PaperNFA Q) (q : Q) (l : List Q) :
    List.foldl (fun (hit : Bool) (q' : Q) =>
        List.foldl (fun (hit : Bool) (b : Bool) => hit || A.delta q' b q) hit [false, true]) false l = true ↔
      ∃ q' ∈ l, ∃ b : Bool, A.delta q' b q = true := by
  have step_eq : (fun (hit : Bool) (q' : Q) =>
      List.foldl (fun (hit : Bool) (b : Bool) => hit || A.delta q' b q) hit [false, true]) =
      (fun (hit : Bool) (q' : Q) =>
        hit || List.foldl (fun (hit : Bool) (b : Bool) => hit || A.delta q' b q) false [false, true]) := by
    funext hit q'
    exact foldl_or_init_eq _ _ hit
  rw [step_eq, foldl_or_iff]
  simp only [Bool.false_eq_true, false_or]
  apply exists_congr
  intro q'
  apply and_congr_right
  intro _
  rw [foldl_or_iff]
  simp

private theorem mem_layerList_iff {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (ℓ : ℕ) (q : Q) :
    q ∈ Nfa.Pseudocode.layerList A ℓ ↔ q ∈ A.layer ℓ := by
  classical
  rw [Nfa.Pseudocode.layerList, Finset.mem_sort, Nfa.Pseudocode.layerSet, Finset.mem_filter]
  simp

private theorem foldl_if_append_eq_filter {Q : Type} (p : Q → Bool) (l acc : List Q) :
    List.foldl (fun acc q => if p q then acc ++ [q] else acc) acc l = acc ++ l.filter p := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons]
    by_cases h : p a = true
    · simp [h, ih, List.filter_cons_of_pos]
    · simp [h, ih, List.filter_cons_of_neg]

private theorem sort_filter_eq_bool {Q : Type} [Fintype Q] [LinearOrder Q] (p : Q → Bool) :
    ((Finset.univ : Finset Q).sort (· ≤ ·)).filter p =
      (Finset.univ.filter (fun q => p q = true)).sort (· ≤ ·) := by
  apply List.Pairwise.eq_of_mem_iff (r := (· < ·))
  · exact ((List.sortedLT_iff_pairwise).mp (Finset.sortedLT_sort (Finset.univ : Finset Q))).filter _
  · exact (List.sortedLT_iff_pairwise).mp (Finset.sortedLT_sort _)
  · intro q
    simp

private theorem layer_succ_mem {Q : Type} (A : Nfa.PaperNFA Q) (ℓ : ℕ) (q : Q) :
    q ∈ A.layer (ℓ+1) ↔ ∃ q' ∈ A.layer ℓ, ∃ b : Bool, A.delta q' b q = true := by
  constructor
  · rintro ⟨w, hw, hmem⟩
    have hne : w ≠ [] := by rintro rfl; simp at hw
    have hd := List.dropLast_append_getLast hne
    set w' := w.dropLast with hw'def
    set b := w.getLast hne with hbdef
    have hlen : w'.length = ℓ := by
      simp [hw'def, List.length_dropLast, hw]
    rw [← hd] at hmem
    rw [Nfa.PaperNFA.toNFA, NFA.eval_append_singleton] at hmem
    rw [NFA.mem_stepSet] at hmem
    obtain ⟨q', hq', hstep⟩ := hmem
    refine ⟨q', ⟨w', hlen, hq'⟩, b, ?_⟩
    simpa [Nfa.PaperNFA.toNFA] using hstep
  · rintro ⟨q', ⟨w', hw', hq'⟩, b, hb⟩
    refine ⟨w' ++ [b], by simp [hw'], ?_⟩
    rw [NFA.eval_append_singleton, NFA.mem_stepSet]
    exact ⟨q', hq', by simpa [Nfa.PaperNFA.toNFA] using hb⟩

private theorem layerList_succ {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (ℓ : ℕ) :
    Nfa.Pseudocode.layerList A (ℓ+1) =
      List.foldl (fun (acc : List Q) (q : Q) =>
          if (List.foldl (fun (hit : Bool) (q' : Q) =>
                List.foldl (fun (hit : Bool) (b : Bool) => hit || A.delta q' b q) hit [false, true])
              false (Nfa.Pseudocode.layerList A ℓ))
          then acc ++ [q] else acc) [] ((Finset.univ : Finset Q).sort (· ≤ ·)) := by
  rw [Nfa.Pseudocode.layerList, foldl_if_append_eq_filter, List.nil_append, sort_filter_eq_bool]
  rw [show (Finset.univ.filter (fun q : Q => List.foldl (fun (hit : Bool) (q' : Q) =>
        List.foldl (fun (hit : Bool) (b : Bool) => hit || A.delta q' b q) hit [false, true])
      false (Nfa.Pseudocode.layerList A ℓ) = true))
      = Nfa.Pseudocode.layerSet A (ℓ+1) from ?_]
  classical
  ext q
  rw [Finset.mem_filter, Nfa.Pseudocode.layerSet, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, foldl_hit_iff, layer_succ_mem]
  apply exists_congr
  intro q'
  apply and_congr_left
  intro _
  exact mem_layerList_iff A ℓ q'

private theorem layerList_zero {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) :
    Nfa.Pseudocode.layerList A 0 = [A.qI] := by
  classical
  have : Nfa.Pseudocode.layerSet A 0 = {A.qI} := by
    ext q
    rw [Nfa.Pseudocode.layerSet, Finset.mem_filter, Finset.mem_singleton]
    simp only [Finset.mem_univ, true_and]
    rw [Nfa.PaperNFA.layer]
    constructor
    · rintro ⟨w, hw, hmem⟩
      rw [List.length_eq_zero_iff] at hw
      subst hw
      simpa [Nfa.PaperNFA.toNFA] using hmem
    · rintro rfl
      exact ⟨[], rfl, by simp [Nfa.PaperNFA.toNFA]⟩
  rw [Nfa.Pseudocode.layerList, this]
  simp

private theorem arr_getD_push_lt {α : Type} (xs : Array α) (a d : α) (l : ℕ) (h : l < xs.size) :
    (xs.push a).getD l d = xs.getD l d := by
  unfold Array.getD
  rw [dif_pos h, dif_pos (by rw [Array.size_push]; omega : l < (xs.push a).size)]
  simp [Array.getElem_push, h]

private theorem arr_getD_push_eq {α : Type} (xs : Array α) (a d : α) : (xs.push a).getD xs.size d = a := by
  simp [Array.getD]

private theorem unroll_back {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (n : ℕ) :
    (Nfa.Program.unroll A n).val.back?.getD [] = Nfa.Pseudocode.layerList A n := by
  induction n with
  | zero =>
    show (#[[A.qI]] : Array (List Q)).back?.getD [] = _
    rw [layerList_zero]
    rfl
  | succ m ih =>
    rw [unroll_succ_val, Array.back?_push, Option.getD_some, ih]
    exact (layerList_succ A m).symm

theorem unroll_getD {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (n ℓ : ℕ) (hℓ : ℓ ≤ n) : (Nfa.Program.unroll A n).val.getD ℓ [] = Nfa.Pseudocode.layerList A ℓ := by
  induction n with
  | zero =>
    interval_cases ℓ
    show (#[[A.qI]] : Array (List Q)).getD 0 [] = _
    rw [layerList_zero]
    rfl
  | succ n ih =>
    rw [unroll_succ_val, unroll_back]
    rcases hℓ.lt_or_eq with hlt | rfl
    · have hsize : ℓ < (Nfa.Program.unroll A n).val.size := by
        rw [unroll_size]; omega
      rw [arr_getD_push_lt _ _ _ _ hsize]
      exact ih (Nat.lt_succ_iff.mp hlt)
    · conv_lhs => rw [show n+1 = (Nfa.Program.unroll A n).val.size from (unroll_size A n).symm]
      rw [arr_getD_push_eq]
      exact (layerList_succ A n).symm

/-- The program's emptiness pre-check at length n holds exactly when the pseudocode's slice L_n(A) is nonempty. -/
theorem acceptsAtLength_iff {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (n : ℕ) : (Nfa.Program.acceptsAtLength A (Nfa.Program.unroll A n).val n).val = true ↔ Nfa.Pseudocode.nonemptySlice A n := by
  show (Arlib.Computation.Charged.foldl _ (((Nfa.Program.unroll A n).val).getD n []) false).val = true ↔ _
  rw [cfoldl_val]
  simp only [Arlib.Computation.Charged.val_bind, Nfa.Interface.val_sameState,
    Arlib.Computation.Charged.val_pure]
  rw [foldl_or_iff]
  simp only [Bool.false_eq_true, false_or, decide_eq_true_eq]
  rw [unroll_getD A n n (le_refl n)]
  classical
  rw [Nfa.Pseudocode.nonemptySlice]
  simp only [Nfa.Pseudocode.layerList, Finset.mem_sort]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro h
    exact ⟨A.qF, h, rfl⟩

/-- The program's predecessor list has the pseudocode's predecessors, in the pseudocode's order, and each entry carries a duplicate-free copy of that edge's label set. -/
private theorem foldl_if_append_eq_filterMap {Q β : Type} (p : Q → Bool) (g : Q → β) (l : List Q) (acc : List β) :
    List.foldl (fun acc q => if p q then acc ++ [g q] else acc) acc l = acc ++ (l.filter p).map g := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons]
    by_cases h : p a = true
    · simp [h, ih, List.filter_cons_of_pos]
    · simp [h, ih, List.filter_cons_of_neg]

private theorem sort_filter_eq_bool_gen {Q : Type} [LinearOrder Q] (S : Finset Q) (p : Q → Bool) :
    (S.sort (· ≤ ·)).filter p = (S.filter (fun q => p q = true)).sort (· ≤ ·) := by
  apply List.Pairwise.eq_of_mem_iff (r := (· < ·))
  · exact ((List.sortedLT_iff_pairwise).mp (Finset.sortedLT_sort S)).filter _
  · exact (List.sortedLT_iff_pairwise).mp (Finset.sortedLT_sort _)
  · intro q
    simp

theorem predecessors_bridge {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (i : ℕ) (q : Q) : ((Nfa.Program.predecessors A (Nfa.Pseudocode.layerList A (i - 1)) q).val.map Prod.fst = Nfa.Pseudocode.predList A i q) ∧ ∀ e ∈ (Nfa.Program.predecessors A (Nfa.Pseudocode.layerList A (i - 1)) q).val, e.2.Nodup ∧ e.2.toFinset = Nfa.Pseudocode.labels A e.1 q := by
  classical
  set L : Q → List Bool := fun q' => [false, true].filter (fun b => A.delta q' b q = true) with hLdef
  have hinner : ∀ q' : Q, (Arlib.Computation.Charged.foldl (fun (ls : List Bool) (b : Bool) => do
      let t ← Nfa.Model.Operations.transition A q' b q
      pure (if t then ls ++ [b] else ls)) [false, true] ([] : List Bool)).val = L q' := by
    intro q'
    rw [cfoldl_val]
    simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
      Nfa.Interface.val_transition, hLdef, List.foldl_cons, List.foldl_nil,
      List.filter_cons, List.filter_nil]
    by_cases h1 : A.delta q' false q = true <;> by_cases h2 : A.delta q' true q = true <;>
      simp [h1, h2]
  have step_eq : (fun (acc : List (Q × List Bool)) (q' : Q) =>
      (((do
          let labels ← Arlib.Computation.Charged.foldl (fun (ls : List Bool) (b : Bool) => do
              let t ← Nfa.Model.Operations.transition A q' b q
              pure (if t then ls ++ [b] else ls)) [false, true] []
          pure (if labels.isEmpty then acc else acc ++ [(q', labels)])) :
            Arlib.Computation.Charged Nfa.Model.Operations.Op Nfa.Model.Operations.Cell
              (List (Q × List Bool))).val)) =
      (fun (acc : List (Q × List Bool)) (q' : Q) =>
        if !(L q').isEmpty then acc ++ [(q', L q')] else acc) := by
    funext acc q'
    simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure]
    rw [hinner q']
    cases h : (L q').isEmpty <;> simp [h]
  have hval : (Nfa.Program.predecessors A (Nfa.Pseudocode.layerList A (i-1)) q).val =
      (((Nfa.Pseudocode.layerList A (i-1)).filter (fun q' => !(L q').isEmpty))).map
        (fun q' => (q', L q')) := by
    show (Arlib.Computation.Charged.foldl _ (Nfa.Pseudocode.layerList A (i-1)) []).val = _
    rw [cfoldl_val, step_eq, foldl_if_append_eq_filterMap]
    simp
  have hiff : ∀ q' : Q, (!(L q').isEmpty) = true ↔ (Nfa.Pseudocode.labels A q' q).Nonempty := by
    intro q'
    rw [hLdef, Bool.not_eq_true', List.isEmpty_eq_false_iff]
    rw [Nfa.Pseudocode.labels, Finset.filter_nonempty_iff]
    constructor
    · intro h
      rw [Ne, List.filter_eq_nil_iff] at h
      push_neg at h
      obtain ⟨b, hb, hbd⟩ := h
      exact ⟨b, Finset.mem_univ _, by simpa using hbd⟩
    · rintro ⟨b, -, hbd⟩
      rw [Ne, List.filter_eq_nil_iff]
      push_neg
      refine ⟨b, ?_, by simpa using hbd⟩
      cases b <;> simp
  have htoFinset : ∀ q' : Q, (L q').toFinset = Nfa.Pseudocode.labels A q' q := by
    intro q'
    rw [hLdef, Nfa.Pseudocode.labels]
    ext b
    simp only [List.mem_toFinset, List.mem_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      decide_eq_true_eq]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨by cases b <;> simp, h⟩
  have hLnodup : ∀ q' : Q, (L q').Nodup := by
    intro q'
    rw [hLdef]
    apply List.Nodup.filter
    simp [List.nodup_cons]
  refine ⟨?_, ?_⟩
  · rw [hval, List.map_map]
    have : (Prod.fst ∘ (fun q' => (q', L q'))) = (id : Q → Q) := by funext q'; rfl
    rw [this, List.map_id]
    rw [Nfa.Pseudocode.predList, Nfa.Pseudocode.layerList, sort_filter_eq_bool_gen]
    congr 1
    rw [Nfa.Pseudocode.pred]
    apply Finset.filter_congr
    intro q' _
    rw [← hiff q']
  · intro e he
    rw [hval] at he
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp he
    exact ⟨hLnodup q', htoFinset q'⟩

/-- INTERNAL: what the program's repetition-`r` normalise-and-union loop (eAS.2–eAS.3) collects: exactly the words `w·b`, `w` a stored sample of a listed predecessor `e.1`, `b` one of its listed labels, whose coin came up heads and which `isWitness` accepts. TEXLINE: algorithm.tex:64-84 -/
theorem hatFold_mem_iff {Q : Type} [Fintype Q] [LinearOrder Q] {A : Nfa.PaperNFA Q} (σ : Nfa.Selector A) (j q r) (s : Nfa.Program.CoreState Q) (normalized : List (Q × List Bool × Nfa.Model.Operations.Scalar)) (t : Nfa.Model.Operations.Tape Q) (u : List Bool) :
    u ∈ (Arlib.Computation.Charged.foldl (fun (T : List (List Bool)) (e : Q × List Bool × Nfa.Model.Operations.Scalar) => Arlib.Computation.Charged.foldl (fun (T : List (List Bool)) (w : List Bool) => Arlib.Computation.Charged.foldl (fun (T : List (List Bool)) (b : Bool) => do let u ← Nfa.Model.Operations.extend w b; let kept ← Nfa.Model.Operations.coin ⟨j, q, r, some e.1, u⟩ e.2.2 t; if kept then (do let chosen ← Nfa.Model.Operations.isWitness σ s.cache q w b e.1; if chosen then Nfa.Model.Operations.addWord u T else pure T) else pure T) e.2.1 T) ((s.prevS e.1).getD r []) T) normalized []).val ↔
      ∃ e ∈ normalized, ∃ w ∈ (s.prevS e.1).getD r [], ∃ b ∈ e.2.1,
        (Nfa.Model.Operations.coin ⟨j, q, r, some e.1, w ++ [b]⟩ e.2.2 t).val = true ∧
        (Nfa.Model.Operations.isWitness σ s.cache q w b e.1).val = true ∧ u = w ++ [b] := by
  rw [cfoldl_mem_iff _ (fun e u => ∃ w ∈ (s.prevS e.1).getD r [], ∃ b ∈ e.2.1,
      (Nfa.Model.Operations.coin ⟨j, q, r, some e.1, w ++ [b]⟩ e.2.2 t).val = true ∧
      (Nfa.Model.Operations.isWitness σ s.cache q w b e.1).val = true ∧ u = w ++ [b]) ?h1]
  case h1 =>
    intro T e u
    rw [cfoldl_mem_iff _ (fun w u => ∃ b ∈ e.2.1,
      (Nfa.Model.Operations.coin ⟨j, q, r, some e.1, w ++ [b]⟩ e.2.2 t).val = true ∧
      (Nfa.Model.Operations.isWitness σ s.cache q w b e.1).val = true ∧ u = w ++ [b]) ?h2]
    case h2 =>
      intro T w u
      rw [cfoldl_mem_iff _ (fun b u =>
        (Nfa.Model.Operations.coin ⟨j, q, r, some e.1, w ++ [b]⟩ e.2.2 t).val = true ∧
        (Nfa.Model.Operations.isWitness σ s.cache q w b e.1).val = true ∧ u = w ++ [b]) ?h3]
      case h3 =>
        intro T b u
        simp only [Arlib.Computation.Charged.val_bind, Nfa.Interface.val_extend]
        by_cases h1 : (Nfa.Model.Operations.coin ⟨j, q, r, some e.1, w ++ [b]⟩ e.2.2 t).val = true <;>
          by_cases h2 : (Nfa.Model.Operations.isWitness σ s.cache q w b e.1).val = true <;>
          simp [h1, h2, or_comm]
  simp

/-- For one repetition r, the program's triple loop over predecessors, stored words and letters (extend, flip a coin, test the witness, keep) has the same law as the pseudocode's `hatSample`, given that the previous-layer sets agree. -/
theorem hatSample_bridge {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (j i r : ℕ) (hi : 1 ≤ i) (q : Q) (s : Nfa.Program.CoreState Q) (st : Nfa.Pseudocode.CoreState Q) (ρ : ℝ) (normalized : List (Q × List Bool × Nfa.Model.Operations.Scalar)) (hpred : normalized.map Prod.fst = Nfa.Pseudocode.predList A i q) (hlab : ∀ e ∈ normalized, e.2.1.Nodup ∧ e.2.1.toFinset = Nfa.Pseudocode.labels A e.1 q) (hratio : ∀ e ∈ normalized, ((e.2.2.get : ℚ) : ℝ) = ρ / st.p (i - 1) e.1) (hS : ∀ q', Nfa.Interface.prevSet s q' r = st.S (i - 1) q' r) (hnd : ∀ q', ((s.prevS q').getD r []).Nodup) (hlen : ∀ q', ∀ w ∈ (s.prevS q').getD r [], w.length = i - 1) (hcache : ∀ q', ∀ w ∈ (s.prevS q').getD r [], w ∈ Nfa.Interface.cacheRows s) : (Nfa.Run.tapeLaw ((Finset.univ : Finset Q).toList.flatMap fun q' => (Nfa.Run.words i).map fun u => (⟨j, q, r, some q', u⟩ : Nfa.Model.Operations.Site Q))).map (fun f => ((Arlib.Computation.Charged.foldl (fun (T : List (List Bool)) (e : Q × List Bool × Nfa.Model.Operations.Scalar) => Arlib.Computation.Charged.foldl (fun (T : List (List Bool)) (w : List Bool) => Arlib.Computation.Charged.foldl (fun (T : List (List Bool)) (b : Bool) => do let u ← Nfa.Model.Operations.extend w b; let kept ← Nfa.Model.Operations.coin ⟨j, q, r, some e.1, u⟩ e.2.2 (Nfa.Model.Operations.Tape.ofFun f); if kept then (do let chosen ← Nfa.Model.Operations.isWitness σ s.cache q w b e.1; if chosen then Nfa.Model.Operations.addWord u T else pure T) else pure T) e.2.1 T) ((s.prevS e.1).getD r []) T) normalized []).val).toFinset) = Nfa.Pseudocode.hatSample A σ st i q ρ r := by
  have hinj : ∀ (a : Q) (u : List Bool) (a' : Q) (u' : List Bool),
      (⟨j, q, r, some a, u⟩ : Nfa.Model.Operations.Site Q) = ⟨j, q, r, some a', u'⟩ →
      a = a' ∧ u = u' := by
    intro a u a' u' h
    simp only [Nfa.Model.Operations.Site.mk.injEq, Option.some.injEq, true_and] at h
    exact h
  have hpnd : (Nfa.Pseudocode.predList A i q).Nodup := Finset.sort_nodup _ _
  have hLnd : ((Finset.univ : Finset Q).toList.flatMap fun q' => (Nfa.Run.words i).map
      fun u => (⟨j, q, r, some q', u⟩ : Nfa.Model.Operations.Site Q)).Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun a _ => (words_nodup i).map (fun u u' h => (hinj a u a u' h).2), ?_⟩
    refine (Finset.nodup_toList _).pairwise_of_forall_ne ?_
    intro a _ b _ hab x hx hy
    obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx
    obtain ⟨v, -, hv⟩ := List.mem_map.mp hy
    exact hab (hinj _ _ _ _ hv).1.symm
  rw [tapeLaw_eq_drawAll]
  unfold Nfa.Pseudocode.hatSample
  have hn : Nfa.Pseudocode.normalize A st i q ρ r = fun a =>
      Nfa.Pseudocode.reduce (Nfa.Pseudocode.extendSet (st.S (i - 1) a r) (Nfa.Pseudocode.labels A a q))
        (ρ / st.p (i - 1) a) := rfl
  rw [hn, ← drawAll_reduce_joint (fun a u => (⟨j, q, r, some a, u⟩ : Nfa.Model.Operations.Site Q))
    hinj _ _ _ hpnd _ hLnd ?cov, PMF.map_comp]
  case cov =>
    intro a _ u hu
    obtain ⟨⟨w, b⟩, hwb, rfl⟩ := Finset.mem_image.mp hu
    rw [Finset.mem_product, ← hS, Nfa.Interface.prevSet, Nfa.Interface.sampleSet,
      List.mem_toFinset] at hwb
    have hw := hlen a w hwb.1
    refine List.mem_flatMap.mpr ⟨a, Finset.mem_toList.mpr (Finset.mem_univ _), ?_⟩
    refine List.mem_map.mpr ⟨w ++ [b], (words_mem_iff _ _).mpr ?_, rfl⟩
    simp only [List.length_append, hw, List.length_singleton]; omega
  congr 1; funext f
  ext u
  rw [List.mem_toFinset, hatFold_mem_iff]
  rw [Function.comp_apply]
  unfold Nfa.Pseudocode.unionSel
  simp only [Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨e, he, w, hw, b, hb, hc, hwit, rfl⟩
    rw [isWitness_iff_chosen σ s.cache q w b e.1 (hcache e.1 w hw)] at hwit
    have hmemP : e.1 ∈ Nfa.Pseudocode.predList A i q := hpred ▸ List.mem_map_of_mem he
    have hmemp : e.1 ∈ Nfa.Pseudocode.pred A i q := (Finset.mem_sort _).mp hmemP
    refine ⟨e.1, hmemp, ?_, hwit⟩
    rw [if_pos hmemP, Finset.mem_filter]
    refine ⟨Finset.mem_image.mpr ⟨(w, b), Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩, ?_⟩
    · rw [← hS, Nfa.Interface.prevSet, Nfa.Interface.sampleSet]; exact List.mem_toFinset.mpr hw
    · rw [← (hlab e he).2]; exact List.mem_toFinset.mpr hb
    · rw [← hratio e he, ← coin_val_eq_digit]; exact hc
  · rintro ⟨a, ha, hmem, hch⟩
    have hmemP : a ∈ Nfa.Pseudocode.predList A i q := (Finset.mem_sort _).mpr ha
    rw [if_pos hmemP, Finset.mem_filter] at hmem
    obtain ⟨hE, hd⟩ := hmem
    obtain ⟨⟨w, b⟩, hwb, rfl⟩ := Finset.mem_image.mp hE
    rw [Finset.mem_product] at hwb
    rw [← hpred] at hmemP
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmemP
    have hw : w ∈ (s.prevS e.1).getD r [] := by
      have := hwb.1
      rw [← hS, Nfa.Interface.prevSet, Nfa.Interface.sampleSet] at this
      exact List.mem_toFinset.mp this
    refine ⟨e, he, w, hw, b, ?_, ?_, ?_, rfl⟩
    · have := hwb.2; rw [← (hlab e he).2] at this; exact List.mem_toFinset.mp this
    · rw [coin_val_eq_digit, hratio e he]; exact hd
    · exact (isWitness_iff_chosen σ s.cache q w b e.1 (hcache e.1 w hw)).mpr hch


/-- INTERNAL: a snoc-fold is a `map`. -/
private theorem foldl_snoc_eq {α β : Type} (g : α → β) (l : List α) (init : List β) :
    List.foldl (fun acc x => acc ++ [g x]) init l = init ++ l.map g := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih => simp [ih]

/-- INTERNAL: a push-fold into an array, as a list. -/
private theorem foldl_push_toList {α β : Type} (g : α → β) (l : List α) (init : Array β) :
    (List.foldl (fun acc x => acc.push (g x)) init l).toList = init.toList ++ l.map g := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih => simp

/-- INTERNAL: reading back entry `r` of an array pushed over `List.range n`. -/
private theorem foldl_push_range_getD {β : Type} (g : ℕ → β) (n r : ℕ) (d : β) :
    (List.foldl (fun acc x => acc.push (g x)) #[] (List.range n)).getD r d
      = if r < n then g r else d := by
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, foldl_push_toList]
  split_ifs with h
  · simp [h]
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

/-- INTERNAL: the array component of a pair-fold that pushes into it. -/
private theorem foldl_pair_fst {α β γ : Type} (g : α → β) (h : (Array β × γ) → α → γ) (l : List α)
    (init : Array β × γ) :
    (List.foldl (fun acc x => (acc.1.push (g x), h acc x)) init l).1
      = List.foldl (fun acc x => acc.push (g x)) init.1 l := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih => simp [ih]

/-- INTERNAL: the program's running `size` sum, as a rational. -/
private theorem foldl_add_size_get (L : ℕ → List (List Bool)) (l : List ℕ) (z : Nfa.Model.Operations.Scalar) :
    (List.foldl (fun x a => (x.add (Nfa.Model.Operations.size (L a)).val).val) z l).get
      = z.get + (l.map fun a => ((L a).length : ℚ)).sum := by
  induction l generalizing z with
  | nil => simp
  | cons a l ih => simp [ih]; ring

/-- INTERNAL: membership in the result of a list fold whose step only adds elements described by `D`. -/
private theorem list_foldl_mem_iff {α γ : Type} (F : List γ → α → List γ)
    (D : α → γ → Prop) (hF : ∀ T x u, u ∈ F T x ↔ u ∈ T ∨ D x u)
    (l : List α) (T0 : List γ) (u : γ) :
    u ∈ List.foldl F T0 l ↔ u ∈ T0 ∨ ∃ x ∈ l, D x u := by
  induction l generalizing T0 with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, ih, hF, List.mem_cons]
    constructor
    · rintro ((h | h) | ⟨x, hx, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨a, Or.inl rfl, h⟩
      · exact Or.inr ⟨x, Or.inr hx, h⟩
    · rintro (h | ⟨x, rfl | hx, h⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨x, hx, h⟩

/-- INTERNAL: the program's repetition-`r` normalise-and-union loop, as a plain list fold. -/
noncomputable def hatList {Q : Type} [LinearOrder Q] {A : Nfa.PaperNFA Q} (σ : Nfa.Selector A) (s : Nfa.Program.CoreState Q) (j : ℕ) (q : Q) (NL : List (Q × List Bool × Nfa.Model.Operations.Scalar)) (t : Nfa.Model.Operations.Tape Q) (r : ℕ) : List (List Bool) :=
  List.foldl (fun x e => List.foldl (fun x w => List.foldl (fun x b =>
    if (Nfa.Model.Operations.coin ⟨j, q, r, some e.1, (Nfa.Model.Operations.extend w b).val⟩ e.2.2 t).val = true then
      if (Nfa.Model.Operations.isWitness σ s.cache q w b e.1).val = true then
        (Nfa.Model.Operations.addWord (Nfa.Model.Operations.extend w b).val x).val else x
    else x) x e.2.1) x ((s.prevS e.1).getD r [])) [] NL

/-- INTERNAL: folding the `simp`-normal form of the loop back into `hatList`. -/
theorem hatList_fold {Q : Type} [LinearOrder Q] {A : Nfa.PaperNFA Q} (σ : Nfa.Selector A) (s : Nfa.Program.CoreState Q) (j : ℕ) (q : Q) (NL : List (Q × List Bool × Nfa.Model.Operations.Scalar)) (t : Nfa.Model.Operations.Tape Q) (r : ℕ) :
  List.foldl (fun x e => List.foldl (fun x w => List.foldl (fun x b =>
    if (Nfa.Model.Operations.coin ⟨j, q, r, some e.1, (Nfa.Model.Operations.extend w b).val⟩ e.2.2 t).val = true then
      if (Nfa.Model.Operations.isWitness σ s.cache q w b e.1).val = true then
        (Nfa.Model.Operations.addWord (Nfa.Model.Operations.extend w b).val x).val else x
    else x) x e.2.1) x ((s.prevS e.1).getD r [])) [] NL = hatList σ s j q NL t r := rfl

/-- INTERNAL: `hatList` is the program's charged repetition-`r` loop. -/
theorem hatList_eq {Q : Type} [LinearOrder Q] {A : Nfa.PaperNFA Q} (σ : Nfa.Selector A) (s : Nfa.Program.CoreState Q) (j : ℕ) (q : Q) (NL : List (Q × List Bool × Nfa.Model.Operations.Scalar)) (t : Nfa.Model.Operations.Tape Q) (r : ℕ) :
    hatList σ s j q NL t r = (Arlib.Computation.Charged.foldl (fun (T : List (List Bool)) (e : Q × List Bool × Nfa.Model.Operations.Scalar) => Arlib.Computation.Charged.foldl (fun (T : List (List Bool)) (w : List Bool) => Arlib.Computation.Charged.foldl (fun (T : List (List Bool)) (b : Bool) => do let u ← Nfa.Model.Operations.extend w b; let kept ← Nfa.Model.Operations.coin ⟨j, q, r, some e.1, u⟩ e.2.2 t; if kept then (do let chosen ← Nfa.Model.Operations.isWitness σ s.cache q w b e.1; if chosen then Nfa.Model.Operations.addWord u T else pure T) else pure T) e.2.1 T) ((s.prevS e.1).getD r []) T) NL []).val := by
  simp only [hatList, cfoldl_val, Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
    apply_ite Arlib.Computation.Charged.val]

/-- INTERNAL: for a fixed tape, the program's `(p(q), S^r(q))` after `estimateAndSample` is the pseudocode's eAS.4–eAS.8 arithmetic applied to the sets `hatList … r` (eAS.2–eAS.3), with the final-reduce coins read at the sites `⟨j, q, r, none, u⟩`. Deterministic; no probability. TEXLINE: algorithm.tex:64-84 -/
theorem estimateAndSample_det {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (P : Nfa.Params) (j : ℕ) (prev : List Q) (q : Q) (one zero : Nfa.Model.Operations.Scalar) (hone : one.get = 1) (hzero : zero.get = 0) (s : Nfa.Program.CoreState Q) (ρs : Nfa.Model.Operations.Scalar)
    (hρ1 : (Nfa.Program.predecessors A prev q).val = [] → ρs = one)
    (hρ2 : ∀ x rest, (Nfa.Program.predecessors A prev q).val = x :: rest →
      ρs = (Arlib.Computation.Charged.foldl (fun (m : Nfa.Model.Operations.Scalar) (e : Q × List Bool) => Nfa.Model.Operations.Scalar.min m (s.prevP e.1)) rest (s.prevP x.1)).val)
    (NL : List (Q × List Bool × Nfa.Model.Operations.Scalar))
    (hNL : NL = (Nfa.Program.predecessors A prev q).val.map fun e => (e.1, e.2, (Nfa.Model.Operations.Scalar.div ρs (s.prevP e.1)).val))
    (f : Nfa.Model.Operations.Site Q → ℕ)
    (hndNL : ∀ r, (hatList σ s j q NL (Nfa.Model.Operations.Tape.ofFun f) r).Nodup) (H : ℕ → Finset (List Bool))
    (hH : ∀ r, H r = if r < P.α then (hatList σ s j q NL (Nfa.Model.Operations.Tape.ofFun f) r).toFinset else ∅) :
    (Nfa.Interface.curPReal (Nfa.Program.estimateAndSample A σ P (Nfa.Model.Operations.Tape.ofFun f) j prev one zero s q).val q,
      fun r => Nfa.Interface.curSet (Nfa.Program.estimateAndSample A σ P (Nfa.Model.Operations.Tape.ofFun f) j prev one zero s q).val q r)
    = (Nfa.Pseudocode.takeMin (Nfa.Interface.real ρs) (Nfa.Pseudocode.blockMedian P (Nfa.Interface.real ρs) H),
       fun r => if r ∈ List.range P.α then (H r).filter (fun u => Nfa.Pseudocode.digit (f ⟨j, q, r, none, u⟩)
         (Nfa.Pseudocode.takeMin (Nfa.Interface.real ρs) (Nfa.Pseudocode.blockMedian P (Nfa.Interface.real ρs) H) / Nfa.Interface.real ρs) = true) else ∅) := by
  unfold Nfa.Program.estimateAndSample
  simp only [Arlib.Computation.Charged.val_bind]
  rcases hpr : (Nfa.Program.predecessors A prev q).val with _ | ⟨x, rest⟩
  on_goal 1 =>
    rw [show (pure one : Arlib.Computation.Charged Nfa.Model.Operations.Op Nfa.Model.Operations.Cell
      Nfa.Model.Operations.Scalar) = pure ρs by rw [hρ1 hpr]]
    simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure]
    rw [← hpr]
  on_goal 2 =>
    simp only [Arlib.Computation.Charged.val_bind]
    rw [← hρ2 x rest hpr, ← hpr]
  all_goals
    simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure, cfoldl_val,
      apply_ite Arlib.Computation.Charged.val, Nfa.Interface.curPReal, Nfa.Interface.curSet,
      Nfa.Interface.sampleSet, Function.update_self, foldl_pair_fst, foldl_push_range_getD,
      foldl_snoc_eq, List.nil_append]
    have hcard : ∀ k, (((if k < P.α then hatList σ s j q NL (Nfa.Model.Operations.Tape.ofFun f) k else []).length : ℚ) : ℝ) = ((H k).card : ℝ) := by
      intro k
      rw [hH k]
      split_ifs with hk
      · rw [List.toFinset_card_of_nodup (hndNL k)]; push_cast; rfl
      · simp
    have hmed : Nfa.Interface.real (Nfa.Model.Operations.Scalar.median ((List.range P.γ).map (fun b => ((List.foldl (fun acc a => (acc.add (Nfa.Model.Operations.size (if P.β * b + a < P.α then hatList σ s j q NL (Nfa.Model.Operations.Tape.ofFun f) (P.β * b + a) else [])).val).val) zero (List.range P.β)).div ((Nfa.Model.Operations.Scalar.lit (P.β : ℚ)).val.mul ρs).val).val))).val
        = Nfa.Pseudocode.blockMedian P (Nfa.Interface.real ρs) H := by
      rw [Nfa.Analysis.scalarMedian_real_eq_medianOf]
      unfold Nfa.Pseudocode.blockMedian
      congr 1; funext b
      simp only [Nfa.Interface.real, Nfa.Interface.get_val_div, Nfa.Interface.get_val_mul,
        Nfa.Interface.get_val_lit, foldl_add_size_get, hzero, zero_add, Nfa.Pseudocode.blockMean]
      push_cast
      congr 1
      rw [List.map_map,
        show ∀ g : ℕ → ℝ, ((List.range P.β).map g).sum = ∑ i ∈ Finset.range P.β, g i from fun g => rfl]
      exact Finset.sum_congr rfl (fun a _ => hcard _)
    have hfinal : ∀ pv : Nfa.Model.Operations.Scalar, ∀ r, ((List.foldl (fun acc x => acc.push (List.foldl (fun x_1 a => if (Nfa.Model.Operations.coin ⟨j, q, x, none, a⟩ (pv.div ρs).val (Nfa.Model.Operations.Tape.ofFun f)).val = true then (Nfa.Model.Operations.addWord a x_1).val else x_1) [] (if x < P.α then hatList σ s j q NL (Nfa.Model.Operations.Tape.ofFun f) x else []))) #[] (List.range P.α)).getD r []).toFinset
        = if r ∈ List.range P.α then (H r).filter (fun u => Nfa.Pseudocode.digit (f ⟨j, q, r, none, u⟩) (Nfa.Interface.real pv / Nfa.Interface.real ρs) = true) else ∅ := by
      intro pv r
      rw [foldl_push_range_getD, hH r]
      simp only [List.mem_range]
      split_ifs with hr
      · ext u
        rw [List.mem_toFinset, list_foldl_mem_iff _ (fun a u => (Nfa.Model.Operations.coin ⟨j, q, r, none, a⟩ (pv.div ρs).val (Nfa.Model.Operations.Tape.ofFun f)).val = true ∧ u = a) ?hF]
        case hF =>
          intro T a u
          split_ifs with hc <;> simp [hc, or_comm]
        have hrd : (((pv.div ρs).val.get : ℚ) : ℝ) = Nfa.Interface.real pv / Nfa.Interface.real ρs := by
          simp [Nfa.Interface.real]
        simp only [List.not_mem_nil, false_or, Finset.mem_filter, List.mem_toFinset,
          coin_val_eq_digit, hrd]
        constructor
        · rintro ⟨a, ha, hc, rfl⟩; exact ⟨ha, hc⟩
        · rintro ⟨ha, hc⟩; exact ⟨u, ha, hc, rfl⟩
      · ext u; simp
    split_ifs with hc
    all_goals
      simp only [hatList_fold] at hc ⊢
      rw [← hNL] at hc ⊢
    · have hle : Nfa.Pseudocode.blockMedian P (Nfa.Interface.real ρs) H ≤ 0 := by
        rw [← hmed]
        simp only [Nfa.Interface.val_le, hzero, decide_eq_true_eq] at hc
        simp only [Nfa.Interface.real]; exact_mod_cast hc
      have hp : Nfa.Pseudocode.takeMin (Nfa.Interface.real ρs) (Nfa.Pseudocode.blockMedian P (Nfa.Interface.real ρs) H) = Nfa.Interface.real ρs := by
        unfold Nfa.Pseudocode.takeMin; rw [if_pos hle]
      simp only [Function.update_self]
      rw [hp]
      refine Prod.ext rfl ?_
      funext r
      exact hfinal ρs r
    · have hlt : ¬ Nfa.Pseudocode.blockMedian P (Nfa.Interface.real ρs) H ≤ 0 := by
        rw [← hmed]
        simp only [Nfa.Interface.val_le, hzero, decide_eq_true_eq] at hc
        simp only [Nfa.Interface.real]; exact_mod_cast hc
      have key : ∀ M : Nfa.Model.Operations.Scalar, Nfa.Interface.real M = Nfa.Pseudocode.blockMedian P (Nfa.Interface.real ρs) H →
          Nfa.Pseudocode.takeMin (Nfa.Interface.real ρs) (Nfa.Pseudocode.blockMedian P (Nfa.Interface.real ρs) H)
            = Nfa.Interface.real (ρs.min (one.div M).val).val := by
        intro M hM
        unfold Nfa.Pseudocode.takeMin
        rw [if_neg hlt, ← hM]
        simp [Nfa.Interface.real, hone]
      simp only [Function.update_self]
      rw [key _ hmed]
      refine Prod.ext rfl ?_
      funext r
      exact hfinal _ r

/-- INTERNAL: membership in `hatList`, from `hatFold_mem_iff`. -/
theorem hatList_mem {Q : Type} [Fintype Q] [LinearOrder Q] {A : Nfa.PaperNFA Q} (σ : Nfa.Selector A) (s : Nfa.Program.CoreState Q) (j : ℕ) (q : Q) (NL : List (Q × List Bool × Nfa.Model.Operations.Scalar)) (t : Nfa.Model.Operations.Tape Q) (r : ℕ) (u : List Bool) :
    u ∈ hatList σ s j q NL t r ↔
      ∃ e ∈ NL, ∃ w ∈ (s.prevS e.1).getD r [], ∃ b ∈ e.2.1,
        (Nfa.Model.Operations.coin ⟨j, q, r, some e.1, w ++ [b]⟩ e.2.2 t).val = true ∧
        (Nfa.Model.Operations.isWitness σ s.cache q w b e.1).val = true ∧ u = w ++ [b] := by
  rw [hatList_eq, hatFold_mem_iff]

/-- INTERNAL: the set `hatList … r` reads the tape only at the sites `⟨j, q, r, some e.1, w·b⟩`. -/
theorem hatList_toFinset_congr {Q : Type} [Fintype Q] [LinearOrder Q] {A : Nfa.PaperNFA Q} (σ : Nfa.Selector A) (s : Nfa.Program.CoreState Q) (j : ℕ) (q : Q) (NL : List (Q × List Bool × Nfa.Model.Operations.Scalar)) (r : ℕ) (f f' : Nfa.Model.Operations.Site Q → ℕ)
    (h : ∀ e ∈ NL, ∀ w ∈ (s.prevS e.1).getD r [], ∀ b ∈ e.2.1,
      f ⟨j, q, r, some e.1, w ++ [b]⟩ = f' ⟨j, q, r, some e.1, w ++ [b]⟩) :
    (hatList σ s j q NL (Nfa.Model.Operations.Tape.ofFun f) r).toFinset
      = (hatList σ s j q NL (Nfa.Model.Operations.Tape.ofFun f') r).toFinset := by
  ext u
  simp only [List.mem_toFinset, hatList_mem, Nfa.Interface.val_coin_ofFun]
  constructor
  · rintro ⟨e, he, w, hw, b, hb, hc, hwit, rfl⟩
    exact ⟨e, he, w, hw, b, hb, by rwa [← h e he w hw b hb], hwit, rfl⟩
  · rintro ⟨e, he, w, hw, b, hb, hc, hwit, rfl⟩
    exact ⟨e, he, w, hw, b, hb, by rwa [h e he w hw b hb], hwit, rfl⟩

/-- INTERNAL: every word of `hatList … r` has length `i` when the stored samples have length `i - 1`. -/
theorem hatList_length {Q : Type} [Fintype Q] [LinearOrder Q] {A : Nfa.PaperNFA Q} (σ : Nfa.Selector A) (s : Nfa.Program.CoreState Q) (j : ℕ) (q : Q) (NL : List (Q × List Bool × Nfa.Model.Operations.Scalar)) (t : Nfa.Model.Operations.Tape Q) (r i : ℕ) (hi : 1 ≤ i)
    (hlen : ∀ q', ∀ w ∈ (s.prevS q').getD r [], w.length = i - 1) (u : List Bool)
    (hu : u ∈ hatList σ s j q NL t r) : u.length = i := by
  obtain ⟨e, -, w, hw, b, -, -, -, rfl⟩ := (hatList_mem σ s j q NL t r u).mp hu
  simp only [List.length_append, hlen e.1 w hw, List.length_singleton]; omega

/-- INTERNAL: the list `hatList … r` reads the tape only at the sites `⟨j, q, r, some e.1, w·b⟩`. -/
theorem hatList_congr {Q : Type} [Fintype Q] [LinearOrder Q] {A : Nfa.PaperNFA Q} (σ : Nfa.Selector A) (s : Nfa.Program.CoreState Q) (j : ℕ) (q : Q) (NL : List (Q × List Bool × Nfa.Model.Operations.Scalar)) (r : ℕ) (f f' : Nfa.Model.Operations.Site Q → ℕ)
    (h : ∀ e ∈ NL, ∀ w ∈ (s.prevS e.1).getD r [], ∀ b ∈ e.2.1,
      f ⟨j, q, r, some e.1, w ++ [b]⟩ = f' ⟨j, q, r, some e.1, w ++ [b]⟩) :
    hatList σ s j q NL (Nfa.Model.Operations.Tape.ofFun f) r
      = hatList σ s j q NL (Nfa.Model.Operations.Tape.ofFun f') r := by
  unfold hatList
  apply List.foldl_ext; intro x e he
  apply List.foldl_ext; intro x w hw
  apply List.foldl_ext; intro x b hb
  have hc : (Nfa.Model.Operations.coin ⟨j, q, r, some e.1, (Nfa.Model.Operations.extend w b).val⟩ e.2.2 (Nfa.Model.Operations.Tape.ofFun f)).val
      = (Nfa.Model.Operations.coin ⟨j, q, r, some e.1, (Nfa.Model.Operations.extend w b).val⟩ e.2.2 (Nfa.Model.Operations.Tape.ofFun f')).val := by
    simp only [Nfa.Interface.val_coin_ofFun, Nfa.Interface.val_extend]
    rw [h e he w hw b hb]
  rw [hc]

/-- INTERNAL: `estimateAndSample(q)` at layer `i` reads the tape only at the sites of run `j`, state `q`, repetition `< α`, word length `i`. Deterministic. TEXLINE: algorithm.tex:64-84 -/
theorem estimateAndSample_local {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (P : Nfa.Params) (j : ℕ) (prev : List Q) (q : Q) (one zero : Nfa.Model.Operations.Scalar) (s : Nfa.Program.CoreState Q) (i : ℕ) (hi : 1 ≤ i)
    (hlen : ∀ q' r, ∀ w ∈ (s.prevS q').getD r [], w.length = i - 1)
    (f f' : Nfa.Model.Operations.Site Q → ℕ)
    (hff : ∀ x : Nfa.Model.Operations.Site Q, x.run = j → x.state = q → x.rep < P.α → x.word.length = i → f x = f' x) :
    (Nfa.Program.estimateAndSample A σ P (Nfa.Model.Operations.Tape.ofFun f) j prev one zero s q).val
      = (Nfa.Program.estimateAndSample A σ P (Nfa.Model.Operations.Tape.ofFun f') j prev one zero s q).val := by
  have hH : ∀ NL, List.foldl (fun x a => Array.push x (hatList σ s j q NL (Nfa.Model.Operations.Tape.ofFun f) a)) #[] (List.range P.α)
      = List.foldl (fun x a => Array.push x (hatList σ s j q NL (Nfa.Model.Operations.Tape.ofFun f') a)) #[] (List.range P.α) := by
    intro NL
    apply List.foldl_ext
    intro acc a ha
    rw [hatList_congr σ s j q NL a f f' (fun e _ w hw b _ => hff _ rfl rfl (List.mem_range.mp ha)
      (by simp only [List.length_append, hlen e.1 a w hw, List.length_singleton]; omega))]
  have hHlen : ∀ NL a, a < P.α → ∀ u ∈ (List.foldl (fun x a => Array.push x (hatList σ s j q NL (Nfa.Model.Operations.Tape.ofFun f') a)) #[] (List.range P.α)).getD a [], u.length = i := by
    intro NL a ha u hu
    rw [foldl_push_range_getD, if_pos ha] at hu
    exact hatList_length σ s j q NL _ a i hi (hlen · a) u hu
  have hfin : ∀ (HS : Array (List (List Bool))) (ratio : Nfa.Model.Operations.Scalar),
      (∀ a, a < P.α → ∀ u ∈ HS.getD a [], u.length = i) →
      ∀ init : Nfa.Program.Samples × Nfa.Model.Operations.Scalar,
      List.foldl (fun x a => (x.1.push (List.foldl (fun x a_1 => if (Nfa.Model.Operations.coin ⟨j, q, a, none, a_1⟩ ratio (Nfa.Model.Operations.Tape.ofFun f)).val = true then (Nfa.Model.Operations.addWord a_1 x).val else x) [] (HS.getD a [])),
          (x.2.add (Nfa.Model.Operations.size (List.foldl (fun x a_1 => if (Nfa.Model.Operations.coin ⟨j, q, a, none, a_1⟩ ratio (Nfa.Model.Operations.Tape.ofFun f)).val = true then (Nfa.Model.Operations.addWord a_1 x).val else x) [] (HS.getD a []))).val).val)) init (List.range P.α)
      = List.foldl (fun x a => (x.1.push (List.foldl (fun x a_1 => if (Nfa.Model.Operations.coin ⟨j, q, a, none, a_1⟩ ratio (Nfa.Model.Operations.Tape.ofFun f')).val = true then (Nfa.Model.Operations.addWord a_1 x).val else x) [] (HS.getD a [])),
          (x.2.add (Nfa.Model.Operations.size (List.foldl (fun x a_1 => if (Nfa.Model.Operations.coin ⟨j, q, a, none, a_1⟩ ratio (Nfa.Model.Operations.Tape.ofFun f')).val = true then (Nfa.Model.Operations.addWord a_1 x).val else x) [] (HS.getD a []))).val).val)) init (List.range P.α) := by
    intro HS ratio hHS init
    apply List.foldl_ext
    intro x a ha
    have hin : List.foldl (fun x a_1 => if (Nfa.Model.Operations.coin ⟨j, q, a, none, a_1⟩ ratio (Nfa.Model.Operations.Tape.ofFun f)).val = true then (Nfa.Model.Operations.addWord a_1 x).val else x) [] (HS.getD a [])
        = List.foldl (fun x a_1 => if (Nfa.Model.Operations.coin ⟨j, q, a, none, a_1⟩ ratio (Nfa.Model.Operations.Tape.ofFun f')).val = true then (Nfa.Model.Operations.addWord a_1 x).val else x) [] (HS.getD a []) := by
      apply List.foldl_ext
      intro T u hu
      have hc : (Nfa.Model.Operations.coin ⟨j, q, a, none, u⟩ ratio (Nfa.Model.Operations.Tape.ofFun f)).val
          = (Nfa.Model.Operations.coin ⟨j, q, a, none, u⟩ ratio (Nfa.Model.Operations.Tape.ofFun f')).val := by
        simp only [Nfa.Interface.val_coin_ofFun]
        rw [hff _ rfl rfl (List.mem_range.mp ha) (hHS a (List.mem_range.mp ha) u hu)]
      rw [hc]
    rw [hin]
  unfold Nfa.Program.estimateAndSample
  simp only [Arlib.Computation.Charged.val_bind]
  rcases hpr : (Nfa.Program.predecessors A prev q).val with _ | ⟨x, rest⟩
  on_goal 1 =>
    simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure]
    rw [← hpr]
  on_goal 2 =>
    simp only [Arlib.Computation.Charged.val_bind]
    generalize (Arlib.Computation.Charged.foldl (fun (m : Nfa.Model.Operations.Scalar) (e : Q × List Bool) => Nfa.Model.Operations.Scalar.min m (s.prevP e.1)) rest (s.prevP x.1)).val = ρc
    rw [← hpr]
  all_goals
    simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure, cfoldl_val,
      apply_ite Arlib.Computation.Charged.val, foldl_snoc_eq, List.nil_append, hatList_fold, hH]
  all_goals
    split_ifs
  all_goals
    rw [hfin _ _ (hHlen _)]

/-- INTERNAL: a `Scalar.min` fold, read as reals. -/
private theorem foldl_min_real {α : Type} (g : α → Nfa.Model.Operations.Scalar) (l : List α) (a : Nfa.Model.Operations.Scalar) :
    Nfa.Interface.real (List.foldl (fun m e => (Nfa.Model.Operations.Scalar.min m (g e)).val) a l)
      = List.foldl (fun m e => min m (Nfa.Interface.real (g e))) (Nfa.Interface.real a) l := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldl_cons, ih]
    congr 1
    simp [Nfa.Interface.real]

/-- INTERNAL: a `min` fold over `x :: rest` is the `inf'` over its elements. -/
private theorem foldl_min_eq_inf' {α : Type} [DecidableEq α] (g : α → ℝ) (x : α) (rest : List α) :
    List.foldl (fun m e => min m (g e)) (g x) rest
      = (insert x rest.toFinset).inf' (Finset.insert_nonempty _ _) g := by
  induction rest generalizing x with
  | nil => simp
  | cons y rest ih =>
    have h2 : ∀ (a : ℝ) (l : List α) (b : ℝ), List.foldl (fun m e => min m (g e)) (min a b) l
        = min a (List.foldl (fun m e => min m (g e)) b l) := by
      intro a l
      induction l with
      | nil => intro b; rfl
      | cons z l ihl => intro b; simp only [List.foldl_cons, min_assoc, ihl]
    simp only [List.foldl_cons]
    rw [h2, ih y, List.toFinset_cons,
      Finset.inf'_insert (s := insert y rest.toFinset) (H := Finset.insert_nonempty _ _)]

/-- INTERNAL: the program's `ρ` (eAS.1, the `match` on the predecessor list) is the pseudocode's `rho`. TEXLINE: algorithm.tex:64-84 -/
theorem rho_real_eq {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (i : ℕ) (q : Q) (one : Nfa.Model.Operations.Scalar) (hone : one.get = 1) (s : Nfa.Program.CoreState Q) (st : Nfa.Pseudocode.CoreState Q) (hp : ∀ q', Nfa.Interface.prevPReal s q' = st.p (i - 1) q') (ρs : Nfa.Model.Operations.Scalar)
    (hρ1 : (Nfa.Program.predecessors A (Nfa.Pseudocode.layerList A (i - 1)) q).val = [] → ρs = one)
    (hρ2 : ∀ x rest, (Nfa.Program.predecessors A (Nfa.Pseudocode.layerList A (i - 1)) q).val = x :: rest →
      ρs = (Arlib.Computation.Charged.foldl (fun (m : Nfa.Model.Operations.Scalar) (e : Q × List Bool) => Nfa.Model.Operations.Scalar.min m (s.prevP e.1)) rest (s.prevP x.1)).val) :
    Nfa.Interface.real ρs = Nfa.Pseudocode.rho A st i q := by
  obtain ⟨hfst, -⟩ := predecessors_bridge A i q
  unfold Nfa.Pseudocode.rho
  rcases hpr : (Nfa.Program.predecessors A (Nfa.Pseudocode.layerList A (i - 1)) q).val with _ | ⟨x, rest⟩
  · rw [hρ1 hpr]
    rw [hpr, List.map_nil] at hfst
    have hempty : Nfa.Pseudocode.pred A i q = ∅ := by
      have := congrArg List.length hfst
      rw [List.length_nil, Nfa.Pseudocode.predList, Finset.length_sort] at this
      exact Finset.card_eq_zero.mp this.symm
    rw [dif_neg (by rw [hempty]; exact Finset.not_nonempty_empty)]
    simp [Nfa.Interface.real, hone]
  · rw [hρ2 x rest hpr, cfoldl_val, foldl_min_real]
    have hg : ∀ e : Q × List Bool, Nfa.Interface.real (s.prevP e.1) = st.p (i - 1) e.1 := fun e => hp e.1
    simp only [hg]
    have hfm : List.foldl (fun m (e : Q × List Bool) => min m (st.p (i - 1) e.1)) (st.p (i - 1) x.1) rest
        = List.foldl (fun m q' => min m (st.p (i - 1) q')) (st.p (i - 1) x.1) (rest.map Prod.fst) := by
      rw [List.foldl_map]
    rw [hfm, foldl_min_eq_inf' (fun q' => st.p (i - 1) q') x.1]
    have hset : insert x.1 (rest.map Prod.fst).toFinset = Nfa.Pseudocode.pred A i q := by
      rw [hpr, List.map_cons] at hfst
      rw [← List.toFinset_cons, hfst, Nfa.Pseudocode.predList, Finset.sort_toFinset]
    have hne : (Nfa.Pseudocode.pred A i q).Nonempty := hset ▸ Finset.insert_nonempty _ _
    rw [dif_pos hne]
    congr 1

/-- INTERNAL: a charged fold whose step prepends `D x` is a reversed `flatMap`. -/
private theorem cfoldl_val_eq_flatMap {κ κₛ α γ : Type} (F : List γ → α → Arlib.Computation.Charged κ κₛ (List γ))
    (D : α → List γ) (hF : ∀ T x, (F T x).val = D x ++ T) (l : List α) (T0 : List γ) :
    (Arlib.Computation.Charged.foldl F l T0).val = l.reverse.flatMap D ++ T0 := by
  induction l generalizing T0 with
  | nil => simp
  | cons a l ih => simp [ih, hF]

/-- INTERNAL: the program's repetition-`r` loop never adds a word twice: `w·b` determines `(w, b)`, and the selector picks one predecessor, so `size` is the cardinality of the set. TEXLINE: algorithm.tex:20-31 -/
theorem hatFold_nodup {Q : Type} [Fintype Q] [LinearOrder Q] {A : Nfa.PaperNFA Q} (σ : Nfa.Selector A) (j q r) (s : Nfa.Program.CoreState Q) (normalized : List (Q × List Bool × Nfa.Model.Operations.Scalar)) (t : Nfa.Model.Operations.Tape Q)
    (hfst : (normalized.map Prod.fst).Nodup) (hlab : ∀ e ∈ normalized, e.2.1.Nodup)
    (hnd : ∀ q', ((s.prevS q').getD r []).Nodup) :
    (Arlib.Computation.Charged.foldl (fun (T : List (List Bool)) (e : Q × List Bool × Nfa.Model.Operations.Scalar) => Arlib.Computation.Charged.foldl (fun (T : List (List Bool)) (w : List Bool) => Arlib.Computation.Charged.foldl (fun (T : List (List Bool)) (b : Bool) => do let u ← Nfa.Model.Operations.extend w b; let kept ← Nfa.Model.Operations.coin ⟨j, q, r, some e.1, u⟩ e.2.2 t; if kept then (do let chosen ← Nfa.Model.Operations.isWitness σ s.cache q w b e.1; if chosen then Nfa.Model.Operations.addWord u T else pure T) else pure T) e.2.1 T) ((s.prevS e.1).getD r []) T) normalized []).val.Nodup := by
  set ok : (Q × List Bool × Nfa.Model.Operations.Scalar) → List Bool → Bool → Prop := fun e w b =>
    (Nfa.Model.Operations.coin ⟨j, q, r, some e.1, w ++ [b]⟩ e.2.2 t).val = true ∧
    (Nfa.Model.Operations.isWitness σ s.cache q w b e.1).val = true with hok
  classical
  set D3 := fun (e : Q × List Bool × Nfa.Model.Operations.Scalar) (w : List Bool) (b : Bool) =>
    if ok e w b then [w ++ [b]] else [] with hD3
  set D2 := fun (e : Q × List Bool × Nfa.Model.Operations.Scalar) (w : List Bool) =>
    e.2.1.reverse.flatMap (D3 e w) with hD2
  set D1 := fun (e : Q × List Bool × Nfa.Model.Operations.Scalar) =>
    ((s.prevS e.1).getD r []).reverse.flatMap (D2 e) with hD1
  rw [cfoldl_val_eq_flatMap _ D1 ?h1, List.append_nil]
  case h1 =>
    intro T e
    rw [cfoldl_val_eq_flatMap _ (D2 e) ?h2]
    case h2 =>
      intro T w
      rw [cfoldl_val_eq_flatMap _ (D3 e w) ?h3]
      case h3 =>
        intro T b
        simp only [Arlib.Computation.Charged.val_bind, Nfa.Interface.val_extend, hD3, hok]
        by_cases h1 : (Nfa.Model.Operations.coin ⟨j, q, r, some e.1, w ++ [b]⟩ e.2.2 t).val = true <;>
          by_cases h2 : (Nfa.Model.Operations.isWitness σ s.cache q w b e.1).val = true <;>
          simp [h1, h2]
  -- membership in each piece
  have hmem3 : ∀ e w b u, u ∈ D3 e w b ↔ ok e w b ∧ u = w ++ [b] := by
    intro e w b u; simp only [hD3]; split_ifs with h <;> simp [h]
  have hpick : ∀ e w b, ok e w b → σ.pick q w b = some e.1 := by
    intro e w b h
    have := h.2
    unfold Nfa.Model.Operations.isWitness at this
    simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Roster.val_mem] at this
    split_ifs at this <;> simp_all
  have hnd3 : ∀ e w b, (D3 e w b).Nodup := by
    intro e w b; simp only [hD3]; split_ifs <;> simp
  have hnd2 : ∀ e ∈ normalized, ∀ w, (D2 e w).Nodup := by
    intro e he w
    rw [List.nodup_flatMap]
    refine ⟨fun b _ => hnd3 e w b, (List.nodup_reverse.mpr (hlab e he)).pairwise_of_forall_ne ?_⟩
    intro b _ b' _ hbb u hu hu'
    rw [hmem3] at hu hu'
    exact hbb (List.append_inj_right' (hu.2.symm.trans hu'.2) rfl |> fun h => by simpa using h)
  have hmem2 : ∀ e w u, u ∈ D2 e w → ok e w (u.getLast?.getD false) ∧ ∃ b, u = w ++ [b] ∧ ok e w b := by
    intro e w u hu
    simp only [hD2, List.mem_flatMap, List.mem_reverse, hmem3] at hu
    obtain ⟨b, -, hb, rfl⟩ := hu
    exact ⟨by simpa using hb, b, rfl, hb⟩
  have hnd1 : ∀ e ∈ normalized, (D1 e).Nodup := by
    intro e he
    rw [List.nodup_flatMap]
    refine ⟨fun w _ => hnd2 e he w, (List.nodup_reverse.mpr (hnd e.1)).pairwise_of_forall_ne ?_⟩
    intro w _ w' _ hww u hu hu'
    obtain ⟨-, b, rfl, -⟩ := hmem2 e w _ hu
    obtain ⟨-, b', hb', -⟩ := hmem2 e w' _ hu'
    exact hww (List.append_inj_left' hb' rfl)
  have hnorm : normalized.Nodup := List.Nodup.of_map _ hfst
  rw [List.nodup_flatMap]
  refine ⟨fun e he => hnd1 e (List.mem_reverse.mp he), (List.nodup_reverse.mpr hnorm).pairwise_of_forall_ne ?_⟩
  intro e he e' he' hee u hu hu'
  rw [List.mem_reverse] at he he'
  simp only [hD1, List.mem_flatMap, List.mem_reverse] at hu hu'
  obtain ⟨w, -, hw⟩ := hu
  obtain ⟨w', -, hw'⟩ := hu'
  obtain ⟨-, b, rfl, hok1⟩ := hmem2 e w _ hw
  obtain ⟨-, b', hb', hok2⟩ := hmem2 e' w' _ hw'
  have hw : w = w' := List.append_inj_left' hb' rfl
  have hb : b = b' := by
    have := List.append_inj_right' hb' rfl; simpa using this
  subst hw hb
  have h1 := hpick e w b hok1
  have h2 := hpick e' w b hok2
  rw [h1] at h2
  have he1 : e.1 = e'.1 := Option.some.inj h2
  exact hee (List.inj_on_of_nodup_map hfst he he' he1)


/-- INTERNAL: a cons-filter fold is a reversed filter. -/
private theorem foldl_cons_filter {α : Type} (c : α → Bool) (l acc : List α) :
    List.foldl (fun x u => if c u = true then u :: x else x) acc l = (l.filter c).reverse ++ acc := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih => by_cases h : c a = true <;> simp [ih, h]

/-- INTERNAL: the running total of the program's final-reduce fold. -/
private theorem foldl_pair_snd_get (g : ℕ → List (List Bool)) (l : List ℕ) (init : Nfa.Program.Samples × Nfa.Model.Operations.Scalar) :
    (List.foldl (fun x a => (x.1.push (g a), (x.2.add (Nfa.Model.Operations.size (g a)).val).val)) init l).2.get
      = init.2.get + (l.map fun a => ((g a).length : ℚ)).sum := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih => simp [ih]; ring

/-- INTERNAL: the generic shape of the final-reduce fold of `estimateAndSample`: filtering duplicate-free lists of length-`i` words, with the running total. -/
private theorem sample_finish (α i : ℕ) (H : ℕ → List (List Bool)) (c : ℕ → List Bool → Bool)
    (hHnd : ∀ r, r < α → (H r).Nodup) (hHlen : ∀ r, r < α → ∀ u ∈ H r, u.length = i)
    (init : Nfa.Model.Operations.Scalar) :
    (∀ r, (if r < α then List.foldl (fun x a => if c r a = true then a :: x else x) [] (if r < α then H r else []) else []).Nodup ∧
      (∀ u ∈ (if r < α then List.foldl (fun x a => if c r a = true then a :: x else x) [] (if r < α then H r else []) else []), u.length = i) ∧
      (α ≤ r → (if r < α then List.foldl (fun x a => if c r a = true then a :: x else x) [] (if r < α then H r else []) else []) = [])) ∧
    (List.foldl (fun x a => (x.1.push (List.foldl (fun x a_1 => if c a a_1 = true then a_1 :: x else x) [] (if a < α then H a else [])),
        (x.2.add (Nfa.Model.Operations.size (List.foldl (fun x a_1 => if c a a_1 = true then a_1 :: x else x) [] (if a < α then H a else []))).val).val))
        (#[], init) (List.range α)).2.get
      = init.get + ((List.range α).map fun r => (((if r < α then List.foldl (fun x a => if c r a = true then a :: x else x) [] (if r < α then H r else []) else [])).length : ℚ)).sum := by
  refine ⟨fun r => ?_, ?_⟩
  · by_cases hr : r < α
    · simp only [if_pos hr, foldl_cons_filter, List.append_nil]
      refine ⟨List.nodup_reverse.mpr ((hHnd r hr).filter _), fun u hu => ?_, fun h => absurd hr (by omega)⟩
      exact hHlen r hr u (List.mem_of_mem_filter (List.mem_reverse.mp hu))
    · simp [hr]
  · rw [foldl_pair_snd_get]
    congr 1
    refine congrArg List.sum (List.map_congr_left fun r hr => ?_)
    simp only [if_pos (List.mem_range.mp hr)]

/-- INTERNAL: after `estimateAndSample(q)` at layer `i`, each stored sample list of `q` is duplicate-free, holds words of length `i`, and is empty past repetition `α`; the running total grows by their lengths. Deterministic. TEXLINE: algorithm.tex:64-84 -/
theorem estimateAndSample_sample {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (P : Nfa.Params) (t : Nfa.Model.Operations.Tape Q) (j : ℕ) (prev : List Q) (q : Q) (one zero : Nfa.Model.Operations.Scalar) (s : Nfa.Program.CoreState Q) (i : ℕ) (hi : 1 ≤ i)
    (hfst : ((Nfa.Program.predecessors A prev q).val.map Prod.fst).Nodup)
    (hlab : ∀ e ∈ (Nfa.Program.predecessors A prev q).val, e.2.Nodup)
    (hnd : ∀ q' r, ((s.prevS q').getD r []).Nodup)
    (hlen : ∀ q' r, ∀ w ∈ (s.prevS q').getD r [], w.length = i - 1) :
    (∀ r, (((Nfa.Program.estimateAndSample A σ P t j prev one zero s q).val.curS q).getD r []).Nodup ∧
      (∀ u ∈ ((Nfa.Program.estimateAndSample A σ P t j prev one zero s q).val.curS q).getD r [], u.length = i) ∧
      (P.α ≤ r → ((Nfa.Program.estimateAndSample A σ P t j prev one zero s q).val.curS q).getD r [] = [])) ∧
    (Nfa.Program.estimateAndSample A σ P t j prev one zero s q).val.total.get
      = s.total.get + ((List.range P.α).map fun r => ((((Nfa.Program.estimateAndSample A σ P t j prev one zero s q).val.curS q).getD r []).length : ℚ)).sum := by
  unfold Nfa.Program.estimateAndSample
  simp only [Arlib.Computation.Charged.val_bind]
  rcases hpr : (Nfa.Program.predecessors A prev q).val with _ | ⟨x, rest⟩
  on_goal 1 =>
    simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure]
    rw [← hpr]
  on_goal 2 =>
    simp only [Arlib.Computation.Charged.val_bind]
    generalize (Arlib.Computation.Charged.foldl (fun (m : Nfa.Model.Operations.Scalar) (e : Q × List Bool) => Nfa.Model.Operations.Scalar.min m (s.prevP e.1)) rest (s.prevP x.1)).val = ρc
    rw [← hpr]
  all_goals
    simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure, cfoldl_val,
      apply_ite Arlib.Computation.Charged.val, foldl_snoc_eq, List.nil_append, hatList_fold]
  all_goals
    split_ifs
  all_goals
    simp only [Function.update_self, foldl_pair_fst, foldl_push_range_getD, Nfa.Interface.val_addWord]
    refine sample_finish P.α i _ _ (fun r _ => ?_) (fun r _ u hu => hatList_length σ s j q _ t r i hi (hlen · r) u hu) _
    rw [hatList_eq]
    refine hatFold_nodup σ j q r s _ t ?_ ?_ (hnd · r)
    · rw [List.map_map]; exact hfst
    · intro e he
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
      exact hlab e' he'

/-- INTERNAL: `estimateAndSample(q)` rewrites only `p(q)`, `S(q)` and the running total of the program state. -/
theorem estimateAndSample_shape {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (P : Nfa.Params) (t : Nfa.Model.Operations.Tape Q) (j : ℕ) (prev : List Q) (one zero : Nfa.Model.Operations.Scalar) (s : Nfa.Program.CoreState Q) (q : Q) :
    ∃ p' S' t', (Nfa.Program.estimateAndSample A σ P t j prev one zero s q).val
      = { s with curP := Function.update s.curP q p', curS := Function.update s.curS q S', total := t' } := by
  unfold Nfa.Program.estimateAndSample
  simp only [Arlib.Computation.Charged.val_bind]
  split <;> simp only [Arlib.Computation.Charged.val_bind] <;> split <;> exact ⟨_, _, _, rfl⟩

/-- INTERNAL: the predecessor lists the program computes from layer `i - 1` are duplicate-free, and so are their label lists. -/
theorem predecessors_nodup {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (i : ℕ) (q : Q) :
    ((Nfa.Program.predecessors A (Nfa.Pseudocode.layerList A (i - 1)) q).val.map Prod.fst).Nodup ∧
    ∀ e ∈ (Nfa.Program.predecessors A (Nfa.Pseudocode.layerList A (i - 1)) q).val, e.2.Nodup := by
  obtain ⟨h1, h2⟩ := predecessors_bridge A i q
  refine ⟨?_, fun e he => (h2 e he).1⟩
  rw [h1]; exact Finset.sort_nodup _ _

/-- INTERNAL: independent draws over disjoint blocks of sites, one statistic per block, are independent draws of the per-block laws. -/
theorem drawAll_blocks {κ ι β γ : Type} [DecidableEq κ] [DecidableEq ι] (f : ι → PMF β) (d : β)
    (rs : List κ) (hrs : rs.Nodup) (L : κ → List ι)
    (hdisj : ∀ r ∈ rs, ∀ r' ∈ rs, r ≠ r' → ∀ x ∈ L r, x ∉ L r')
    (Φ : κ → (ι → β) → γ) (hΦ : ∀ r g g', (∀ x ∈ L r, g x = g' x) → Φ r g = Φ r g') (e : γ) :
    (Nfa.Pseudocode.drawAll f d (rs.flatMap L)).map (fun g r => if r ∈ rs then Φ r g else e)
      = Nfa.Pseudocode.drawAll (fun r => (Nfa.Pseudocode.drawAll f d (L r)).map (Φ r)) e rs := by
  induction rs with
  | nil =>
    simp only [List.flatMap_nil, Nfa.Pseudocode.drawAll, PMF.pure_map]
    congr 1
  | cons a rs ih =>
    have h1 := List.nodup_cons.mp hrs
    rw [List.flatMap_cons, drawAll_append', PMF.map_bind, Nfa.Pseudocode.drawAll, PMF.bind_map,
      ← ih h1.2 (fun r hr r' hr' h => hdisj r (List.mem_cons_of_mem _ hr) r'
        (List.mem_cons_of_mem _ hr') h)]
    congr 1; funext g1
    simp only [Function.comp_apply, PMF.map_comp]
    congr 1; funext g2 r
    by_cases hr : r = a
    · subst hr
      simp only [List.mem_cons, true_or, if_true, Function.comp_apply, Function.update_self]
      exact hΦ _ _ _ (fun x hx => by simp [hx])
    · simp only [List.mem_cons, hr, false_or, Function.comp_apply, Function.update_of_ne hr]
      split_ifs with hrs'
      · refine hΦ _ _ _ (fun x hx => ?_)
        rw [if_neg]
        exact hdisj r (List.mem_cons_of_mem _ hrs') a (List.mem_cons_self) hr x hx
      · rfl


/-- INTERNAL: a `flatMap` over a duplicate-free list with duplicate-free, pairwise-disjoint blocks is duplicate-free. -/
private theorem nodup_flatMap_of {α β : Type} (l : List α) (g : α → List β) (hl : l.Nodup)
    (hg : ∀ a ∈ l, (g a).Nodup) (hd : ∀ a ∈ l, ∀ b ∈ l, ∀ x, x ∈ g a → x ∈ g b → a = b) :
    (l.flatMap g).Nodup := by
  rw [List.nodup_flatMap]
  exact ⟨hg, hl.pairwise_of_forall_ne fun a ha b hb hab x hxa hxb => hab (hd a ha b hb x hxa hxb)⟩

/-- For each state q, the program's estimate-and-sample step gives the same joint law of (p(i,q), S^r(i,q)) as the pseudocode. That the program's `Scalar.median` matches `Arlib.Probability.medianOf` is an Analysis-side helper used inside the proof, not a rung. -/
theorem estimateAndSample_bridge {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (P : Nfa.Params) (j i : ℕ) (hi : 1 ≤ i) (q : Q) (one zero : Nfa.Model.Operations.Scalar) (hone : one.get = 1) (hzero : zero.get = 0) (s : Nfa.Program.CoreState Q) (st : Nfa.Pseudocode.CoreState Q) (hp : ∀ q', Nfa.Interface.prevPReal s q' = st.p (i - 1) q') (hS : ∀ q' r, Nfa.Interface.prevSet s q' r = st.S (i - 1) q' r) (hnd : ∀ q' r, ((s.prevS q').getD r []).Nodup) (hlen : ∀ q' r, ∀ w ∈ (s.prevS q').getD r [], w.length = i - 1) (hcache : ∀ q' r, ∀ w ∈ (s.prevS q').getD r [], w ∈ Nfa.Interface.cacheRows s) : (Nfa.Run.tapeLaw ((List.range P.α).flatMap fun r => (none :: (Finset.univ : Finset Q).toList.map some).flatMap fun src => (Nfa.Run.words i).map fun u => (⟨j, q, r, src, u⟩ : Nfa.Model.Operations.Site Q))).map (fun f => (Nfa.Interface.curPReal (Nfa.Program.estimateAndSample A σ P (Nfa.Model.Operations.Tape.ofFun f) j (Nfa.Pseudocode.layerList A (i - 1)) one zero s q).val q, fun r => Nfa.Interface.curSet (Nfa.Program.estimateAndSample A σ P (Nfa.Model.Operations.Tape.ofFun f) j (Nfa.Pseudocode.layerList A (i - 1)) one zero s q).val q r)) = (Nfa.Pseudocode.estimateAndSample A σ P i st q).map fun st' => (st'.p i q, fun r => st'.S i q r) := by
  obtain ⟨hfst, hlabp⟩ := predecessors_bridge A i q
  obtain ⟨ρs, hρ1, hρ2⟩ : ∃ ρs : Nfa.Model.Operations.Scalar,
      ((Nfa.Program.predecessors A (Nfa.Pseudocode.layerList A (i - 1)) q).val = [] → ρs = one) ∧
      (∀ x rest, (Nfa.Program.predecessors A (Nfa.Pseudocode.layerList A (i - 1)) q).val = x :: rest →
        ρs = (Arlib.Computation.Charged.foldl (fun (m : Nfa.Model.Operations.Scalar) (e : Q × List Bool) => Nfa.Model.Operations.Scalar.min m (s.prevP e.1)) rest (s.prevP x.1)).val) := by
    rcases h : (Nfa.Program.predecessors A (Nfa.Pseudocode.layerList A (i - 1)) q).val with _ | ⟨x, rest⟩
    · exact ⟨one, fun _ => rfl, fun x rest h' => by simp at h'⟩
    · exact ⟨_, fun h' => by simp at h', fun x' rest' h' => by
        simp only [List.cons.injEq] at h'; obtain ⟨rfl, rfl⟩ := h'; rfl⟩
  have hρ : Nfa.Interface.real ρs = Nfa.Pseudocode.rho A st i q :=
    rho_real_eq A i q one hone s st hp ρs hρ1 hρ2
  obtain ⟨NL, hNL⟩ : ∃ NL : List (Q × List Bool × Nfa.Model.Operations.Scalar),
      NL = (Nfa.Program.predecessors A (Nfa.Pseudocode.layerList A (i - 1)) q).val.map
        fun e => (e.1, e.2, (Nfa.Model.Operations.Scalar.div ρs (s.prevP e.1)).val) := ⟨_, rfl⟩
  have hNLfst : NL.map Prod.fst = Nfa.Pseudocode.predList A i q := by
    rw [hNL, List.map_map]; exact hfst
  have hNLlab : ∀ e ∈ NL, e.2.1.Nodup ∧ e.2.1.toFinset = Nfa.Pseudocode.labels A e.1 q := by
    intro e he
    rw [hNL] at he
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    exact hlabp e' he'
  have hNLratio : ∀ e ∈ NL, ((e.2.2.get : ℚ) : ℝ) = Nfa.Pseudocode.rho A st i q / st.p (i - 1) e.1 := by
    intro e he
    rw [hNL] at he
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    rw [← hρ, ← hp e'.1]
    simp [Nfa.Interface.real, Nfa.Interface.prevPReal]
  have hNLnd : (NL.map Prod.fst).Nodup := by rw [hNLfst]; exact Finset.sort_nodup _ _
  have hndHL : ∀ (f : Nfa.Model.Operations.Site Q → ℕ) r, (hatList σ s j q NL (Nfa.Model.Operations.Tape.ofFun f) r).Nodup := by
    intro f r
    rw [hatList_eq]
    exact hatFold_nodup σ j q r s NL _ hNLnd (fun e he => (hNLlab e he).1) (fun q' => hnd q' r)
  obtain ⟨Hf, hHf⟩ : ∃ Hf : (Nfa.Model.Operations.Site Q → ℕ) → ℕ → Finset (List Bool),
      ∀ f r, Hf f r = if r ∈ List.range P.α then (hatList σ s j q NL (Nfa.Model.Operations.Tape.ofFun f) r).toFinset else ∅ :=
    ⟨fun f r => if r ∈ List.range P.α then (hatList σ s j q NL (Nfa.Model.Operations.Tape.ofFun f) r).toFinset else ∅,
      fun _ _ => rfl⟩
  have hdet := fun f => estimateAndSample_det A σ P j (Nfa.Pseudocode.layerList A (i - 1)) q one zero hone hzero s ρs hρ1 hρ2 NL hNL f
    (hndHL f) (Hf f) (fun r => by rw [hHf]; simp only [List.mem_range])
  simp only [hdet]
  rw [hρ]
  unfold Nfa.Pseudocode.estimateAndSample
  simp only [PMF.map_bind, PMF.map_comp]
  generalize Nfa.Pseudocode.rho A st i q = ρ at hNLratio ⊢
  obtain ⟨Lr, hLr⟩ : ∃ Lr : ℕ → List (Nfa.Model.Operations.Site Q), ∀ r, Lr r =
      (Finset.univ : Finset Q).toList.flatMap fun q' => (Nfa.Run.words i).map fun u =>
        (⟨j, q, r, some q', u⟩ : Nfa.Model.Operations.Site Q) := ⟨_, fun _ => rfl⟩
  obtain ⟨Ln, hLn⟩ : ∃ Ln : List (Nfa.Model.Operations.Site Q), Ln =
      (List.range P.α).flatMap fun r => (Nfa.Run.words i).map fun u =>
        (⟨j, q, r, none, u⟩ : Nfa.Model.Operations.Site Q) := ⟨_, rfl⟩
  have hmemLr : ∀ r x, x ∈ Lr r ↔ ∃ q' u, u.length = i ∧ x = ⟨j, q, r, some q', u⟩ := by
    intro r x
    rw [hLr]
    simp only [List.mem_flatMap, Finset.mem_toList, Finset.mem_univ, true_and, List.mem_map,
      words_mem_iff]
    constructor
    · rintro ⟨q', u, hu, rfl⟩; exact ⟨q', u, hu, rfl⟩
    · rintro ⟨q', u, hu, rfl⟩; exact ⟨q', u, hu, rfl⟩
  have hmemLn : ∀ x, x ∈ Ln ↔ ∃ r u, r < P.α ∧ u.length = i ∧ x = ⟨j, q, r, none, u⟩ := by
    intro x
    rw [hLn]
    simp only [List.mem_flatMap, List.mem_range, List.mem_map, words_mem_iff]
    constructor
    · rintro ⟨r, hr, u, hu, rfl⟩; exact ⟨r, u, hr, hu, rfl⟩
    · rintro ⟨r, u, hr, hu, rfl⟩; exact ⟨r, hr, u, hu, rfl⟩
  have hsiteinj : ∀ (r : ℕ) (src : Option Q), Function.Injective
      (fun u => (⟨j, q, r, src, u⟩ : Nfa.Model.Operations.Site Q)) := by
    intro r src u u' h; simpa using h
  have hLfnd : ((List.range P.α).flatMap fun r => (none :: (Finset.univ : Finset Q).toList.map some).flatMap
      fun src => (Nfa.Run.words i).map fun u => (⟨j, q, r, src, u⟩ : Nfa.Model.Operations.Site Q)).Nodup := by
    refine nodup_flatMap_of _ _ List.nodup_range (fun r _ => ?_) ?_
    · refine nodup_flatMap_of _ _ ?_ (fun src _ => (words_nodup i).map (hsiteinj r src)) ?_
      · exact List.nodup_cons.mpr ⟨by simp, (Finset.nodup_toList _).map (Option.some_injective _)⟩
      · intro a _ b _ x hx hy
        obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx
        obtain ⟨u', -, hu'⟩ := List.mem_map.mp hy
        simp only [Nfa.Model.Operations.Site.mk.injEq] at hu'
        exact hu'.2.2.2.1.symm
    · intro a _ b _ x hx hy
      obtain ⟨src, -, u, -, rfl⟩ := by simpa only [List.mem_flatMap, List.mem_map] using hx
      obtain ⟨src', -, u', -, hu'⟩ := by simpa only [List.mem_flatMap, List.mem_map] using hy
      simp only [Nfa.Model.Operations.Site.mk.injEq] at hu'
      exact hu'.2.2.1.symm
  have hLsnd : ((List.range P.α).flatMap Lr).Nodup := by
    refine nodup_flatMap_of _ _ List.nodup_range (fun r _ => ?_) ?_
    · rw [hLr]
      refine nodup_flatMap_of _ _ (Finset.nodup_toList _)
        (fun q' _ => (words_nodup i).map (hsiteinj r (some q'))) ?_
      intro a _ b _ x hx hy
      obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx
      obtain ⟨u', -, hu'⟩ := List.mem_map.mp hy
      simp only [Nfa.Model.Operations.Site.mk.injEq, Option.some.injEq] at hu'
      exact hu'.2.2.2.1.symm
    · intro a _ b _ x hx hy
      obtain ⟨q', u, -, rfl⟩ := (hmemLr a x).mp hx
      obtain ⟨q'', u', -, hu'⟩ := (hmemLr b _).mp hy
      simp only [Nfa.Model.Operations.Site.mk.injEq] at hu'
      exact hu'.2.2.1
  have hLnnd : Ln.Nodup := by
    rw [hLn]
    refine nodup_flatMap_of _ _ List.nodup_range (fun r _ => (words_nodup i).map (hsiteinj r none)) ?_
    intro a _ b _ x hx hy
    obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx
    obtain ⟨u', -, hu'⟩ := List.mem_map.mp hy
    simp only [Nfa.Model.Operations.Site.mk.injEq] at hu'
    exact hu'.2.2.1.symm
  have hperm : ((List.range P.α).flatMap fun r => (none :: (Finset.univ : Finset Q).toList.map some).flatMap
      fun src => (Nfa.Run.words i).map fun u => (⟨j, q, r, src, u⟩ : Nfa.Model.Operations.Site Q)).Perm
      ((List.range P.α).flatMap Lr ++ Ln) := by
    rw [List.perm_ext_iff_of_nodup hLfnd]
    · intro x
      simp only [List.mem_append, List.mem_flatMap, List.mem_range, hmemLr, hmemLn, List.mem_cons,
        List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and, words_mem_iff]
      constructor
      · rintro ⟨r, hr, src, hsrc, u, hu, rfl⟩
        rcases hsrc with rfl | ⟨q', rfl⟩
        · exact Or.inr ⟨r, u, hr, hu, rfl⟩
        · exact Or.inl ⟨r, hr, q', u, hu, rfl⟩
      · rintro (⟨r, hr, q', u, hu, rfl⟩ | ⟨r, u, hr, hu, rfl⟩)
        · exact ⟨r, hr, some q', Or.inr ⟨q', rfl⟩, u, hu, rfl⟩
        · exact ⟨r, hr, none, Or.inl rfl, u, hu, rfl⟩
    · rw [List.nodup_append]
      refine ⟨hLsnd, hLnnd, ?_⟩
      intro x hx y hy hxy
      subst hxy
      obtain ⟨r, -, hr⟩ := List.mem_flatMap.mp hx
      obtain ⟨q', u, -, rfl⟩ := (hmemLr r x).mp hr
      obtain ⟨r', u', -, -, h⟩ := (hmemLn _).mp hy
      simp at h
  rw [tapeLaw_eq_drawAll, drawAll_perm _ _ hperm hLfnd, drawAll_append', PMF.map_bind]
  have hH : (Nfa.Pseudocode.drawAll (fun _ => Nfa.Run.coinIndex) 0 ((List.range P.α).flatMap Lr)).map Hf
      = Nfa.Pseudocode.hatSamples A σ P st i q ρ := by
    have hHf' : Hf = fun f r => if r ∈ List.range P.α then
        (fun r (g : Nfa.Model.Operations.Site Q → ℕ) => (hatList σ s j q NL (Nfa.Model.Operations.Tape.ofFun g) r).toFinset) r f
        else ∅ := by
      funext f r; exact hHf f r
    rw [hHf', drawAll_blocks (fun _ => Nfa.Run.coinIndex) 0 (List.range P.α) List.nodup_range Lr ?hdisj _ ?hΦ ∅]
    case hdisj =>
      intro r _ r' _ hrr x hx hx'
      obtain ⟨q', u, -, rfl⟩ := (hmemLr r x).mp hx
      obtain ⟨q'', u', -, h⟩ := (hmemLr r' _).mp hx'
      simp only [Nfa.Model.Operations.Site.mk.injEq] at h
      exact hrr h.2.2.1
    case hΦ =>
      intro r g g' hg
      apply hatList_toFinset_congr
      intro e _ w hw b _
      apply hg
      refine (hmemLr r _).mpr ⟨e.1, w ++ [b], ?_, rfl⟩
      simp only [List.length_append, hlen e.1 r w hw, List.length_singleton]; omega
    unfold Nfa.Pseudocode.hatSamples
    congr 1
    funext r
    rw [hLr r, ← tapeLaw_eq_drawAll]
    simp only [hatList_eq]
    exact hatSample_bridge A σ j i r hi q s st ρ NL hNLfst hNLlab hNLratio (hS · r) (hnd · r)
      (hlen · r) (hcache · r)
  rw [← hH, PMF.bind_map]
  congr 1; funext g1
  simp only [Function.comp_apply, PMF.map_comp]
  have hcombH : ∀ g2 : Nfa.Model.Operations.Site Q → ℕ,
      Hf (fun x => if x ∈ (List.range P.α).flatMap Lr then g1 x else g2 x) = Hf g1 := by
    intro g2; funext r
    rw [hHf, hHf]
    split_ifs with hr
    · apply hatList_toFinset_congr
      intro e _ w hw b _
      rw [if_pos]
      refine List.mem_flatMap.mpr ⟨r, hr, (hmemLr r _).mpr ⟨e.1, w ++ [b], ?_, rfl⟩⟩
      simp only [List.length_append, hlen e.1 r w hw, List.length_singleton]; omega
    · rfl
  have hcombN : ∀ (g2 : Nfa.Model.Operations.Site Q → ℕ) r u,
      (if (⟨j, q, r, none, u⟩ : Nfa.Model.Operations.Site Q) ∈ (List.range P.α).flatMap Lr then g1 ⟨j, q, r, none, u⟩ else g2 ⟨j, q, r, none, u⟩) = g2 ⟨j, q, r, none, u⟩ := by
    intro g2 r u
    rw [if_neg]
    intro hm
    obtain ⟨r', -, hr'⟩ := List.mem_flatMap.mp hm
    obtain ⟨q', u', -, h⟩ := (hmemLr r' _).mp hr'
    simp at h
  simp only [Function.comp_def, hcombH, hcombN]
  have hsN : ∀ (a : ℕ) (u : List Bool) (a' : ℕ) (u' : List Bool),
      (⟨j, q, a, none, u⟩ : Nfa.Model.Operations.Site Q) = ⟨j, q, a', none, u'⟩ → a = a' ∧ u = u' := by
    intro a u a' u' h; simp only [Nfa.Model.Operations.Site.mk.injEq] at h; exact ⟨h.2.2.1, h.2.2.2.2⟩
  have hcov : ∀ a ∈ List.range P.α, ∀ u ∈ Hf g1 a, (⟨j, q, a, none, u⟩ : Nfa.Model.Operations.Site Q) ∈ Ln := by
    intro a ha u hu
    rw [hHf, if_pos ha, List.mem_toFinset] at hu
    exact (hmemLn _).mpr ⟨a, u, List.mem_range.mp ha,
      hatList_length σ s j q NL _ a i hi (hlen · a) u hu, rfl⟩
  have hjoint := drawAll_reduce_joint (fun r u => (⟨j, q, r, none, u⟩ : Nfa.Model.Operations.Site Q)) hsN (Hf g1)
    (fun _ => Nfa.Pseudocode.takeMin ρ (Nfa.Pseudocode.blockMedian P ρ (Hf g1)) / ρ) (List.range P.α)
    List.nodup_range Ln hLnnd hcov
  unfold Nfa.Pseudocode.finalReduce
  rw [← hjoint, PMF.map_comp]
  congr 1
  funext g2
  simp [Function.update_self]

/-! ### Program-side facts about one layer step (deterministic, one tape) -/

/-- INTERNAL: one iteration of the program's countNFA.9–11 loop for state `q`: `estimateAndSample(q)`, then the interrupt test; nothing once stopped. -/
noncomputable def eStep {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (P : Nfa.Params) (t : Nfa.Model.Operations.Tape Q) (j : ℕ) (prev : List Q) (one zero θs : Nfa.Model.Operations.Scalar) (s : Nfa.Program.CoreState Q) (q : Q) : Nfa.Program.CoreState Q :=
  if s.stopped then s else
    { (Nfa.Program.estimateAndSample A σ P t j prev one zero s q).val with
      stopped := (Nfa.Model.Operations.Scalar.le θs (Nfa.Program.estimateAndSample A σ P t j prev one zero s q).val.total).val }

/-- INTERNAL: the program state at the start of layer `i`: the current layer becomes the previous one, the new layer starts at `p ≡ 1`, `S ≡ ∅`. -/
abbrev shiftState {Q : Type} (s : Nfa.Program.CoreState Q) (one : Nfa.Model.Operations.Scalar) (i : ℕ) : Nfa.Program.CoreState Q :=
  { s with prevP := s.curP, prevS := s.curS, curP := fun _ => one, curS := fun _ => #[], layerIdx := i }

/-- INTERNAL: a fold whose step only grows a set-valued view only grows it. -/
theorem list_foldl_mono {α β γ : Type} (F : β → α → β) (S : β → Set γ)
    (hF : ∀ b a, S b ⊆ S (F b a)) (l : List α) (b : β) : S b ⊆ S (l.foldl F b) := by
  induction l generalizing b with
  | nil => exact le_rfl
  | cons a l ih => exact (hF b a).trans (ih _)

/-- INTERNAL: every element a monotone fold step adds survives to the end of the fold. -/
theorem list_foldl_mem_all {α β γ : Type} (F : β → α → β) (S : β → Set γ)
    (hF : ∀ b a, S b ⊆ S (F b a)) (R : α → γ → Prop) (hR : ∀ b a x, R a x → x ∈ S (F b a))
    (l : List α) (b : β) : ∀ a ∈ l, ∀ x, R a x → x ∈ S (l.foldl F b) := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
    intro a' ha' x hx
    rcases List.mem_cons.mp ha' with rfl | ha'
    · exact list_foldl_mono F S hF l _ (hR b a' x hx)
    · exact ih _ a' ha' x hx

/-- INTERNAL: one step of the program's updateCache(i) loop. -/
def cacheStep {Q : Type} (cur : List Q) (c : Arlib.Computation.Roster (List Bool)) (u : List Bool) :
    Arlib.Computation.Charged Nfa.Model.Operations.Op Nfa.Model.Operations.Cell (Arlib.Computation.Roster (List Bool)) := do
  let present ← Arlib.Computation.Roster.mem u c
  if present then pure c else do
    let _ ← Arlib.Computation.Charged.foldl (fun (_ : Unit) (_ : Q) => Nfa.Model.Operations.cacheEntry) cur ()
    Arlib.Computation.Roster.insert u c

/-- INTERNAL: one updateCache(i) step keeps the rows it had and adds its word. -/
theorem cacheStep_mem {Q : Type} (cur : List Q) (c : Arlib.Computation.Roster (List Bool)) (u : List Bool) :
    (c.toFinset : Set (List Bool)) ⊆ (cacheStep cur c u).val.toFinset ∧ u ∈ (cacheStep cur c u).val.toFinset := by
  unfold cacheStep
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Roster.val_mem]
  by_cases hu : u ∈ c.toFinset
  · simp [hu]
  · simp only [hu, decide_false, Bool.false_eq_true, ↓reduceIte, Arlib.Computation.Charged.val_bind,
      Arlib.Computation.Roster.toFinset_insert, Finset.coe_insert]
    exact ⟨Set.subset_insert _ _, Finset.mem_insert_self _ _⟩

/-- INTERNAL: the updateCache(i) loop over one sample list adds all its words. -/
theorem cacheRow_mem {Q : Type} (cur : List Q) (T : List (List Bool)) (c : Arlib.Computation.Roster (List Bool)) :
    (c.toFinset : Set (List Bool)) ⊆ (Arlib.Computation.Charged.foldl (cacheStep cur) T c).val.toFinset ∧
      ∀ u ∈ T, u ∈ (Arlib.Computation.Charged.foldl (cacheStep cur) T c).val.toFinset := by
  rw [cfoldl_val]
  refine ⟨list_foldl_mono _ (fun c => (c.toFinset : Set (List Bool))) (fun c u => (cacheStep_mem cur c u).1) T c, ?_⟩
  intro u hu
  exact list_foldl_mem_all _ (fun c => (c.toFinset : Set (List Bool))) (fun c u => (cacheStep_mem cur c u).1)
    (fun a x => x = a) (fun c a x hx => hx ▸ (cacheStep_mem cur c a).2) T c u hu u rfl

/-- INTERNAL: the updateCache(i) loop over the sample lists of one state adds all their words. -/
theorem cacheQ_mem {Q : Type} (cur : List Q) (Ts : List (List (List Bool))) (c : Arlib.Computation.Roster (List Bool)) :
    (c.toFinset : Set (List Bool)) ⊆ (Arlib.Computation.Charged.foldl (fun c T => Arlib.Computation.Charged.foldl (cacheStep cur) T c) Ts c).val.toFinset ∧
      ∀ T ∈ Ts, ∀ u ∈ T, u ∈ (Arlib.Computation.Charged.foldl (fun c T => Arlib.Computation.Charged.foldl (cacheStep cur) T c) Ts c).val.toFinset := by
  rw [cfoldl_val]
  refine ⟨list_foldl_mono _ (fun c => (c.toFinset : Set (List Bool))) (fun c T => (cacheRow_mem cur T c).1) Ts c, ?_⟩
  intro T hT u hu
  exact list_foldl_mem_all _ (fun c => (c.toFinset : Set (List Bool))) (fun c T => (cacheRow_mem cur T c).1)
    (fun T x => x ∈ T) (fun c T x hx => (cacheRow_mem cur T c).2 x hx) Ts c T hT u hu

/-- INTERNAL: the rebuilt cache of updateCache(i) holds every word stored for a state of the layer. -/
theorem cacheFold_mem {Q : Type} (cur : List Q) (S : Q → List (List (List Bool))) :
    ∀ q ∈ cur, ∀ T ∈ S q, ∀ u ∈ T, u ∈
    (Arlib.Computation.Charged.foldl (fun c q => Arlib.Computation.Charged.foldl (fun c T => Arlib.Computation.Charged.foldl (cacheStep cur) T c) (S q) c) cur Arlib.Computation.Roster.empty).val.toFinset := by
  intro q hq T hT u hu
  rw [cfoldl_val]
  exact list_foldl_mem_all _ (fun c => (c.toFinset : Set (List Bool))) (fun c q => (cacheQ_mem cur (S q) c).1)
    (fun q x => ∃ T ∈ S q, x ∈ T)
    (fun c q x ⟨T, hT, hx⟩ => (cacheQ_mem cur (S q) c).2 T hT x hx) cur _ q hq u ⟨T, hT, hu⟩

/-- INTERNAL: a word read off an entry of an array of lists lies in one of its lists. -/
theorem getD_mem_exists {α : Type} (a : Array (List α)) (r : ℕ) (w : α) (hw : w ∈ a.getD r []) :
    ∃ T ∈ a.toList, w ∈ T := by
  rw [Array.getD_eq_getD_getElem?] at hw
  rcases h : a[r]? with _ | T
  · simp [h] at hw
  · rw [h] at hw
    refine ⟨T, ?_, hw⟩
    obtain ⟨hr, rfl⟩ := Array.getElem?_eq_some_iff.mp h
    exact Array.getElem_mem_toList hr

/-- INTERNAL: the fields of a core state the bridges read (everything but the cache). -/
def coreFields {Q : Type} (s : Nfa.Program.CoreState Q) :=
  (s.prevP, s.prevS, s.curP, s.curS, s.layerIdx, s.total, s.stopped)

/-- INTERNAL: apart from the cache, a non-stopped program layer step is the per-state fold over the layer from the shifted state. -/
theorem layerStep_fields {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (P : Nfa.Params) (t : Nfa.Model.Operations.Tape Q) (j : ℕ) (layers : Array (List Q)) (one zero θs : Nfa.Model.Operations.Scalar) (s : Nfa.Program.CoreState Q) (i : ℕ) (hs : s.stopped = false) :
    coreFields (Nfa.Program.layerStep A σ P t j layers one zero θs s i).val
      = coreFields ((layers.getD i []).foldl (eStep A σ P t j (layers.getD (i - 1) []) one zero θs) (shiftState s one i)) := by
  unfold Nfa.Program.layerStep
  rw [if_neg (by simp [hs])]
  simp only [Arlib.Computation.Charged.val_bind, cfoldl_val]
  have hstep : (fun (x : Nfa.Program.CoreState Q) (a : Q) => (if x.stopped = true then pure x else do
          let s ← Nfa.Program.estimateAndSample A σ P t j (layers.getD (i - 1) []) one zero x a
          let over ← Nfa.Model.Operations.Scalar.le θs s.total
          pure { s with stopped := over } : Arlib.Computation.Charged Nfa.Model.Operations.Op Nfa.Model.Operations.Cell (Nfa.Program.CoreState Q)).val)
      = eStep A σ P t j (layers.getD (i - 1) []) one zero θs := by
    funext x a; unfold eStep; split <;> rfl
  rw [hstep]
  split_ifs <;> rfl

/-- INTERNAL: when a layer finishes without the interrupt, every stored word of a state of the layer is a cache row. -/
theorem layerStep_cache {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (P : Nfa.Params) (t : Nfa.Model.Operations.Tape Q) (j : ℕ) (layers : Array (List Q)) (one zero θs : Nfa.Model.Operations.Scalar) (s : Nfa.Program.CoreState Q) (i : ℕ) (hs : s.stopped = false)
    (h2 : ((layers.getD i []).foldl (eStep A σ P t j (layers.getD (i - 1) []) one zero θs) (shiftState s one i)).stopped = false) :
    ∀ q ∈ layers.getD i [], ∀ r, ∀ w ∈ (((layers.getD i []).foldl (eStep A σ P t j (layers.getD (i - 1) []) one zero θs) (shiftState s one i)).curS q).getD r [],
      w ∈ Nfa.Interface.cacheRows (Nfa.Program.layerStep A σ P t j layers one zero θs s i).val := by
  unfold Nfa.Program.layerStep
  rw [if_neg (by simp [hs])]
  simp only [Arlib.Computation.Charged.val_bind, cfoldl_val]
  have hstep : (fun (x : Nfa.Program.CoreState Q) (a : Q) => (if x.stopped = true then pure x else do
          let s ← Nfa.Program.estimateAndSample A σ P t j (layers.getD (i - 1) []) one zero x a
          let over ← Nfa.Model.Operations.Scalar.le θs s.total
          pure { s with stopped := over } : Arlib.Computation.Charged Nfa.Model.Operations.Op Nfa.Model.Operations.Cell (Nfa.Program.CoreState Q)).val)
      = eStep A σ P t j (layers.getD (i - 1) []) one zero θs := by
    funext x a; unfold eStep; split <;> rfl
  rw [hstep]
  generalize ((layers.getD i []).foldl (eStep A σ P t j (layers.getD (i - 1) []) one zero θs) (shiftState s one i)) = s2 at h2 ⊢
  rw [if_neg (by simp [h2])]
  intro q hq r w hw
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure, Nfa.Interface.cacheRows]
  obtain ⟨T, hT, hwT⟩ := getD_mem_exists _ r w hw
  exact cacheFold_mem _ (fun q => (s2.curS q).toList) q hq T hT w hwT

/-- INTERNAL: one per-state step of a layer (`estimateAndSample` then the interrupt test) touches only `p(q)`, `S(q)`, the total and the stopped flag. -/
theorem eStep_frame {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (P : Nfa.Params) (t : Nfa.Model.Operations.Tape Q) (j : ℕ) (prev : List Q) (one zero θs : Nfa.Model.Operations.Scalar) (x : Nfa.Program.CoreState Q) (q : Q) :
    (eStep A σ P t j prev one zero θs x q).prevS = x.prevS ∧
    (eStep A σ P t j prev one zero θs x q).prevP = x.prevP ∧
    (eStep A σ P t j prev one zero θs x q).layerIdx = x.layerIdx ∧
    (eStep A σ P t j prev one zero θs x q).cache = x.cache ∧
    ∀ q', q' ≠ q → (eStep A σ P t j prev one zero θs x q).curS q' = x.curS q' ∧
      (eStep A σ P t j prev one zero θs x q).curP q' = x.curP q' := by
  unfold eStep
  split_ifs with h
  · exact ⟨rfl, rfl, rfl, rfl, fun _ _ => ⟨rfl, rfl⟩⟩
  · obtain ⟨p', S', t', he⟩ := estimateAndSample_shape A σ P t j prev one zero x q
    rw [he]
    exact ⟨rfl, rfl, rfl, rfl, fun q' hq' => ⟨Function.update_of_ne hq' _ _, Function.update_of_ne hq' _ _⟩⟩

/-- INTERNAL: the fold of the per-state steps over (part of) a layer keeps the previous layer, the layer index and the cache, keeps the stored lists duplicate-free with words of length `i`, and leaves the states it does not visit alone. -/
theorem eStepFold_inv {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (P : Nfa.Params) (t : Nfa.Model.Operations.Tape Q) (j : ℕ) (one zero θs : Nfa.Model.Operations.Scalar) (i : ℕ) (hi : 1 ≤ i)
    (S0 : Q → Nfa.Program.Samples) (hnd0 : ∀ q' r, ((S0 q').getD r []).Nodup)
    (hlen0 : ∀ q' r, ∀ w ∈ (S0 q').getD r [], w.length = i - 1) :
    ∀ (l : List Q) (x : Nfa.Program.CoreState Q), x.prevS = S0 →
    (∀ q r, ((x.curS q).getD r []).Nodup ∧ ∀ w ∈ (x.curS q).getD r [], w.length = i) →
    (l.foldl (eStep A σ P t j (Nfa.Pseudocode.layerList A (i - 1)) one zero θs) x).prevS = S0 ∧
    (l.foldl (eStep A σ P t j (Nfa.Pseudocode.layerList A (i - 1)) one zero θs) x).layerIdx = x.layerIdx ∧
    (∀ q r, (((l.foldl (eStep A σ P t j (Nfa.Pseudocode.layerList A (i - 1)) one zero θs) x).curS q).getD r []).Nodup ∧
      ∀ w ∈ ((l.foldl (eStep A σ P t j (Nfa.Pseudocode.layerList A (i - 1)) one zero θs) x).curS q).getD r [], w.length = i) ∧
    (∀ q, q ∉ l → (l.foldl (eStep A σ P t j (Nfa.Pseudocode.layerList A (i - 1)) one zero θs) x).curS q = x.curS q) := by
  intro l
  induction l with
  | nil => intro x h0 h1; exact ⟨h0, rfl, h1, fun _ _ => rfl⟩
  | cons a l ih =>
    intro x h0 h1
    obtain ⟨f1, -, f3, -, f5⟩ := eStep_frame A σ P t j (Nfa.Pseudocode.layerList A (i - 1)) one zero θs x a
    have hstep : ∀ q r, (((eStep A σ P t j (Nfa.Pseudocode.layerList A (i - 1)) one zero θs x a).curS q).getD r []).Nodup ∧
        ∀ w ∈ ((eStep A σ P t j (Nfa.Pseudocode.layerList A (i - 1)) one zero θs x a).curS q).getD r [], w.length = i := by
      intro q r
      by_cases hq : q = a
      · subst hq
        unfold eStep
        split_ifs with hx
        · exact h1 q r
        · obtain ⟨hpf, hpl⟩ := predecessors_nodup A i q
          have := (estimateAndSample_sample A σ P t j (Nfa.Pseudocode.layerList A (i - 1)) q one zero x i hi
            hpf hpl (fun q' r => h0 ▸ hnd0 q' r) (fun q' r => h0 ▸ hlen0 q' r)).1 r
          exact ⟨this.1, this.2.1⟩
      · rw [(f5 q hq).1]; exact h1 q r
    obtain ⟨g1, g2, g3, g4⟩ := ih _ (f1.trans h0) hstep
    refine ⟨g1, g2.trans f3, g3, fun q hq => ?_⟩
    rw [List.foldl_cons, g4 q (fun h => hq (List.mem_cons_of_mem a h)),
      (f5 q (fun h => hq (h ▸ List.mem_cons_self))).1]

/-- INTERNAL: the program-side invariants of the `runLayers` bridge are preserved by one
layer step, for every tape.
TEXLINE: algorithm.tex:90-112 -/
theorem layerStep_invariants {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q)
    (σ : Nfa.Selector A) (P : Nfa.Params) (t : Nfa.Model.Operations.Tape Q) (j : ℕ)
    (layers : Array (List Q)) (one zero θs : Nfa.Model.Operations.Scalar)
    (s : Nfa.Program.CoreState Q) (i : ℕ) (hi : 1 ≤ i)
    (hprev : layers.getD (i - 1) [] = Nfa.Pseudocode.layerList A (i - 1))
    (hidx : s.layerIdx ≤ i - 1) (hrun : s.stopped = false → s.layerIdx = i - 1)
    (hnd : ∀ q r, ((s.curS q).getD r []).Nodup)
    (hlen : s.stopped = false → ∀ q r, ∀ w ∈ (s.curS q).getD r [], w.length = i - 1) :
    (Nfa.Program.layerStep A σ P t j layers one zero θs s i).val.layerIdx ≤ i ∧
    ((Nfa.Program.layerStep A σ P t j layers one zero θs s i).val.stopped = false →
      (Nfa.Program.layerStep A σ P t j layers one zero θs s i).val.layerIdx = i) ∧
    (∀ q r, (((Nfa.Program.layerStep A σ P t j layers one zero θs s i).val.curS q).getD r []).Nodup) ∧
    ((Nfa.Program.layerStep A σ P t j layers one zero θs s i).val.stopped = false →
      ∀ q r, ∀ w ∈ ((Nfa.Program.layerStep A σ P t j layers one zero θs s i).val.curS q).getD r [],
        w.length = i) ∧
    ((Nfa.Program.layerStep A σ P t j layers one zero θs s i).val.stopped = false →
      ∀ q r, ∀ w ∈ ((Nfa.Program.layerStep A σ P t j layers one zero θs s i).val.curS q).getD r [],
        w ∈ Nfa.Interface.cacheRows (Nfa.Program.layerStep A σ P t j layers one zero θs s i).val) := by
  by_cases hs : s.stopped = true
  · -- a stopped run is left alone
    have hval : (Nfa.Program.layerStep A σ P t j layers one zero θs s i).val = s := by
      simp [Nfa.Program.layerStep, hs]
    rw [hval]
    refine ⟨by omega, fun h => by simp [hs] at h, hnd, fun h => by simp [hs] at h,
      fun h => by simp [hs] at h⟩
  · have hs' : s.stopped = false := by simpa using hs
    have hf := layerStep_fields A σ P t j layers one zero θs s i hs'
    simp only [coreFields, Prod.mk.injEq] at hf
    obtain ⟨-, -, -, hcS, hli, -, hst⟩ := hf
    have hc := layerStep_cache A σ P t j layers one zero θs s i hs'
    rw [hprev] at hcS hli hst hc
    obtain ⟨-, k2, k3, k4⟩ := eStepFold_inv A σ P t j one zero θs i hi s.curS hnd (hlen hs')
      (layers.getD i []) (shiftState s one i) rfl (fun q r => by simp [shiftState])
    simp only [shiftState] at k2 k4
    refine ⟨by rw [hli, k2], fun _ => by rw [hli, k2], fun q r => by rw [hcS]; exact (k3 q r).1,
      fun _ q r => by rw [hcS]; exact (k3 q r).2, fun h q r w hw => ?_⟩
    rw [hcS] at hw
    rw [hst] at h
    by_cases hq : q ∈ layers.getD i []
    · exact hc h q hq r w hw
    · rw [k4 q hq] at hw; simp at hw


/-- INTERNAL: one per-state step reads the tape only at the sites of run `j`, its state `q`, repetition `< α`, word length `i`. -/
theorem eStep_local {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (P : Nfa.Params) (j : ℕ) (prev : List Q) (one zero θs : Nfa.Model.Operations.Scalar) (i : ℕ) (hi : 1 ≤ i)
    (x : Nfa.Program.CoreState Q) (q : Q) (hlen : ∀ q' r, ∀ w ∈ (x.prevS q').getD r [], w.length = i - 1)
    (f f' : Nfa.Model.Operations.Site Q → ℕ)
    (hff : ∀ y : Nfa.Model.Operations.Site Q, y.run = j → y.state = q → y.rep < P.α → y.word.length = i → f y = f' y) :
    eStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j prev one zero θs x q
      = eStep A σ P (Nfa.Model.Operations.Tape.ofFun f') j prev one zero θs x q := by
  unfold eStep
  split_ifs
  · rfl
  · rw [estimateAndSample_local A σ P j prev q one zero x i hi hlen f f' hff]

/-- INTERNAL: the per-state fold over a list of states reads the tape only at the sites of run `j`, a state of the list, repetition `< α`, word length `i`. -/
theorem eStepFold_local {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (P : Nfa.Params) (j : ℕ) (prev : List Q) (one zero θs : Nfa.Model.Operations.Scalar) (i : ℕ) (hi : 1 ≤ i)
    (S0 : Q → Nfa.Program.Samples) (hlen0 : ∀ q' r, ∀ w ∈ (S0 q').getD r [], w.length = i - 1)
    (f f' : Nfa.Model.Operations.Site Q → ℕ) (l : List Q)
    (hff : ∀ y : Nfa.Model.Operations.Site Q, y.run = j → y.state ∈ l → y.rep < P.α → y.word.length = i → f y = f' y) :
    ∀ (x : Nfa.Program.CoreState Q), x.prevS = S0 →
    l.foldl (eStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j prev one zero θs) x
      = l.foldl (eStep A σ P (Nfa.Model.Operations.Tape.ofFun f') j prev one zero θs) x := by
  induction l with
  | nil => intro x _; rw [List.foldl_nil, List.foldl_nil]
  | cons a l ih =>
    intro x h0
    rw [List.foldl_cons, List.foldl_cons,
      eStep_local A σ P j prev one zero θs i hi x a (fun q' r => h0 ▸ hlen0 q' r) f f'
        (fun y h1 h2 h3 h4 => hff y h1 (h2 ▸ List.mem_cons_self) h3 h4)]
    exact ih (fun y h1 h2 h3 h4 => hff y h1 (List.mem_cons_of_mem a h2) h3 h4) _
      ((eStep_frame A σ P _ j prev one zero θs x a).1.trans h0)

/-- INTERNAL: once stopped, the per-state fold does nothing. -/
theorem eStepFold_stopped {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (P : Nfa.Params) (t : Nfa.Model.Operations.Tape Q) (j : ℕ) (prev : List Q) (one zero θs : Nfa.Model.Operations.Scalar)
    (l : List Q) (x : Nfa.Program.CoreState Q) (hx : x.stopped = true) :
    l.foldl (eStep A σ P t j prev one zero θs) x = x := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldl_cons, show eStep A σ P t j prev one zero θs x a = x by unfold eStep; rw [if_pos hx]]
    exact ih

/-- INTERNAL: one layer step depends on the tape only through the sites of run `j`,
repetition `< α`, word length `i`.
TEXLINE: algorithm.tex:64-84 -/
theorem layerStep_local {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q)
    (σ : Nfa.Selector A) (P : Nfa.Params) (j : ℕ)
    (layers : Array (List Q)) (one zero θs : Nfa.Model.Operations.Scalar)
    (s : Nfa.Program.CoreState Q) (i : ℕ) (hi : 1 ≤ i)
    (hlen : s.stopped = false → ∀ q r, ∀ w ∈ (s.curS q).getD r [], w.length = i - 1)
    (f f' : Nfa.Model.Operations.Site Q → ℕ)
    (hff : ∀ x : Nfa.Model.Operations.Site Q, x.run = j → x.rep < P.α → x.word.length = i →
      f x = f' x) :
    (Nfa.Program.layerStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j layers one zero θs s i).val
      = (Nfa.Program.layerStep A σ P (Nfa.Model.Operations.Tape.ofFun f') j layers one zero θs s i).val := by
  by_cases hs : s.stopped = true
  · simp [Nfa.Program.layerStep, hs]
  · have hs' : s.stopped = false := by simpa using hs
    unfold Nfa.Program.layerStep
    rw [if_neg (by simp [hs']), if_neg (by simp [hs'])]
    simp only [Arlib.Computation.Charged.val_bind, cfoldl_val]
    have hstep : ∀ g : Nfa.Model.Operations.Site Q → ℕ, (fun (x : Nfa.Program.CoreState Q) (a : Q) => (if x.stopped = true then pure x else do
          let s ← Nfa.Program.estimateAndSample A σ P (Nfa.Model.Operations.Tape.ofFun g) j (layers.getD (i - 1) []) one zero x a
          let over ← Nfa.Model.Operations.Scalar.le θs s.total
          pure { s with stopped := over } : Arlib.Computation.Charged Nfa.Model.Operations.Op Nfa.Model.Operations.Cell (Nfa.Program.CoreState Q)).val)
        = eStep A σ P (Nfa.Model.Operations.Tape.ofFun g) j (layers.getD (i - 1) []) one zero θs := by
      intro g; funext x a; unfold eStep; split <;> rfl
    rw [hstep f, hstep f', eStepFold_local A σ P j _ one zero θs i hi s.curS (hlen hs') f f' _
      (fun y h1 _ h3 h4 => hff y h1 h3 h4) _ rfl]


/-- INTERNAL: binding against a PMF only sees the continuation on its support. -/
private theorem pmf_bind_congr_support {α β : Type} (p : PMF α) (f g : α → PMF β)
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  ext b
  simp only [PMF.bind_apply]
  congr 1; funext a
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · rw [(PMF.apply_eq_zero_iff p a).mpr ha]; simp

/-- INTERNAL: two binds agree when their first stages have equal laws on projections `π`, `ρ` and each continuation, on the support, depends only on that projection — the pseudocode continuation `H` through `ρ`, and the program continuation `G` matching `H` at every pseudocode state with the same projection. -/
theorem pmf_bind_transfer {T S X Y : Type} (μ : PMF T) (ν : PMF S) (π : T → X) (ρ : S → X)
    (hlaw : μ.map π = ν.map ρ) (G : T → PMF Y) (H : S → PMF Y)
    (hH : ∀ a ∈ ν.support, ∀ b ∈ ν.support, ρ a = ρ b → H a = H b)
    (hG : ∀ t ∈ μ.support, ∀ a ∈ ν.support, ρ a = π t → G t = H a) :
    μ.bind G = ν.bind H := by
  classical
  obtain ⟨a0, -⟩ := ν.support_nonempty
  let K : X → PMF Y := fun x => if h : ∃ a ∈ ν.support, ρ a = x then H h.choose else H a0
  have hK : ∀ a ∈ ν.support, K (ρ a) = H a := by
    intro a ha
    have h : ∃ b ∈ ν.support, ρ b = ρ a := ⟨a, ha, rfl⟩
    simp only [K, dif_pos h]
    exact hH _ h.choose_spec.1 a ha h.choose_spec.2
  have hπ : ∀ t ∈ μ.support, ∃ a ∈ ν.support, ρ a = π t := by
    intro t ht
    have : π t ∈ (ν.map ρ).support := by
      rw [← hlaw, PMF.mem_support_map_iff]; exact ⟨t, ht, rfl⟩
    exact (PMF.mem_support_map_iff _ _ _).mp this
  calc μ.bind G = μ.bind (K ∘ π) := by
        apply pmf_bind_congr_support
        intro t ht
        obtain ⟨a, ha, hρ⟩ := hπ t ht
        rw [Function.comp_apply, ← hρ, hK a ha]
        exact hG t ht a ha hρ
    _ = ν.bind (K ∘ ρ) := by rw [← PMF.bind_map, hlaw, PMF.bind_map]
    _ = ν.bind H := pmf_bind_congr_support _ _ _ (fun a ha => hK a ha)

/-- INTERNAL: the tape sites of layer `ℓ` in core run `j` are those of run `j`, repetition `< α`, word length `ℓ`. -/
theorem mem_layerSites_iff {Q : Type} [Fintype Q] (P : Nfa.Params) (j ℓ : ℕ) (x : Nfa.Model.Operations.Site Q) :
    x ∈ ((Finset.univ : Finset Q).toList.flatMap fun q => (List.range P.α).flatMap fun r => (none :: (Finset.univ : Finset Q).toList.map some).flatMap fun src => (Nfa.Run.words ℓ).map fun u => (⟨j, q, r, src, u⟩ : Nfa.Model.Operations.Site Q))
      ↔ x.run = j ∧ x.rep < P.α ∧ x.word.length = ℓ := by
  obtain ⟨run, q, r, src, u⟩ := x
  simp only [List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons, Finset.mem_toList,
    Finset.mem_univ, true_and, words_mem_iff, Nfa.Model.Operations.Site.mk.injEq]
  constructor
  · rintro ⟨q', r', hr', src', -, u', hu', rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨rfl, hr', hu'⟩
  · rintro ⟨rfl, hr, hu⟩
    refine ⟨q, r, hr, src, ?_, u, hu, rfl, rfl, rfl, rfl, rfl⟩
    cases src with
    | none => exact Or.inl rfl
    | some q'' => exact Or.inr ⟨q'', rfl⟩

/-- INTERNAL: the tape sites `estimateAndSample(q)` may read at layer `i` of run `j`. -/
noncomputable def stateSites {Q : Type} [Fintype Q] (P : Nfa.Params) (j i : ℕ) (q : Q) : List (Nfa.Model.Operations.Site Q) :=
  (List.range P.α).flatMap fun r => (none :: (Finset.univ : Finset Q).toList.map some).flatMap fun src =>
    (Nfa.Run.words i).map fun u => (⟨j, q, r, src, u⟩ : Nfa.Model.Operations.Site Q)

/-- INTERNAL: membership in `stateSites`. -/
theorem mem_stateSites_iff {Q : Type} [Fintype Q] (P : Nfa.Params) (j i : ℕ) (q : Q) (x : Nfa.Model.Operations.Site Q) :
    x ∈ stateSites P j i q ↔ x.run = j ∧ x.state = q ∧ x.rep < P.α ∧ x.word.length = i := by
  obtain ⟨run, q', r, src, u⟩ := x
  simp only [stateSites, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons, Finset.mem_toList,
    Finset.mem_univ, true_and, words_mem_iff, Nfa.Model.Operations.Site.mk.injEq]
  constructor
  · rintro ⟨r', hr', src', -, u', hu', rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, hr', hu'⟩
  · rintro ⟨rfl, rfl, hr, hu⟩
    refine ⟨r, hr, src, ?_, u, hu, rfl, rfl, rfl, rfl, rfl⟩
    cases src with
    | none => exact Or.inl rfl
    | some q'' => exact Or.inr ⟨q'', rfl⟩

/-- INTERNAL: the sites of distinct states are distinct, so the site list of a duplicate-free list of states is duplicate-free. -/
theorem stateSites_flatMap_nodup {Q : Type} [Fintype Q] (P : Nfa.Params) (j i : ℕ) (l : List Q) (hl : l.Nodup) :
    (l.flatMap (stateSites P j i)).Nodup := by
  refine nodup_flatMap_of _ _ hl (fun q _ => ?_) ?_
  · have hsiteinj : ∀ (r : ℕ) (src : Option Q), Function.Injective
        (fun u => (⟨j, q, r, src, u⟩ : Nfa.Model.Operations.Site Q)) := by
      intro r src u u' h; simpa using h
    refine nodup_flatMap_of _ _ List.nodup_range (fun r _ => ?_) ?_
    · refine nodup_flatMap_of _ _ ?_ (fun src _ => (words_nodup i).map (hsiteinj r src)) ?_
      · exact List.nodup_cons.mpr ⟨by simp, (Finset.nodup_toList _).map (Option.some_injective _)⟩
      · intro a _ b _ x hx hy
        obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx
        obtain ⟨u', -, hu'⟩ := List.mem_map.mp hy
        simp only [Nfa.Model.Operations.Site.mk.injEq] at hu'
        exact hu'.2.2.2.1.symm
    · intro a _ b _ x hx hy
      obtain ⟨src, -, u, -, rfl⟩ := by simpa only [List.mem_flatMap, List.mem_map] using hx
      obtain ⟨src', -, u', -, hu'⟩ := by simpa only [List.mem_flatMap, List.mem_map] using hy
      simp only [Nfa.Model.Operations.Site.mk.injEq] at hu'
      exact hu'.2.2.1.symm
  · intro a _ b _ x hx hy
    rw [mem_stateSites_iff] at hx hy
    exact hx.2.1.symm.trans hy.2.1

/-- INTERNAL: membership in the site list of a list of states. -/
theorem mem_flatMap_stateSites_iff {Q : Type} [Fintype Q] (P : Nfa.Params) (j i : ℕ) (l : List Q) (x : Nfa.Model.Operations.Site Q) :
    x ∈ l.flatMap (stateSites P j i) ↔ x.run = j ∧ x.state ∈ l ∧ x.rep < P.α ∧ x.word.length = i := by
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨q, hq, hx⟩
    obtain ⟨h1, rfl, h3, h4⟩ := (mem_stateSites_iff P j i q x).mp hx
    exact ⟨h1, hq, h3, h4⟩
  · rintro ⟨h1, hq, h3, h4⟩
    exact ⟨x.state, hq, (mem_stateSites_iff P j i _ x).mpr ⟨h1, rfl, h3, h4⟩⟩

/-- INTERNAL: every outcome of the pseudocode's `estimateAndSample(q)` at layer `i` is the input state with `p(q^i)` and `S(q^i)` overwritten. -/
theorem pseudo_eAS_support {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (P : Nfa.Params) (i : ℕ) (y : Nfa.Pseudocode.CoreState Q) (q : Q)
    (a : Nfa.Pseudocode.CoreState Q) (ha : a ∈ (Nfa.Pseudocode.estimateAndSample A σ P i y q).support) :
    a = { y with p := Function.update y.p i (Function.update (y.p i) q (a.p i q)),
                 S := Function.update y.S i (Function.update (y.S i) q (a.S i q)) } := by
  unfold Nfa.Pseudocode.estimateAndSample at ha
  simp only [PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at ha
  obtain ⟨hatS, -, S', -, rfl⟩ := ha
  simp

/-- INTERNAL: writing a fresh state's sample sets at layer `i ≤ n` raises the stored total by their sizes. -/
theorem storedTotal_upd {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (n : ℕ) (P : Nfa.Params) (y : Nfa.Pseudocode.CoreState Q) (i : ℕ) (q : Q)
    (pv : ℝ) (S' : ℕ → Finset (List Bool)) (hin : i ≤ n) (hq : q ∈ Nfa.Pseudocode.layerSet A i)
    (hy : ∀ r, y.S i q r = ∅) :
    Nfa.Pseudocode.storedTotal A n P
        { y with p := Function.update y.p i (Function.update (y.p i) q pv),
                 S := Function.update y.S i (Function.update (y.S i) q S') }
      = Nfa.Pseudocode.storedTotal A n P y + ∑ r ∈ Finset.range P.α, (S' r).card := by
  classical
  unfold Nfa.Pseudocode.storedTotal
  have key : ∀ ℓ q' r, (Function.update y.S i (Function.update (y.S i) q S') ℓ q' r).card
      = (y.S ℓ q' r).card + if ℓ = i ∧ q' = q then (S' r).card else 0 := by
    intro ℓ q' r
    by_cases hℓ : ℓ = i
    · subst hℓ
      by_cases hq' : q' = q
      · subst hq'; simp [hy]
      · simp [hq']
    · simp [Function.update_of_ne hℓ, hℓ]
  simp only [key, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single q]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd hq h
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-- INTERNAL: the states of layer `i`, one at a time (countNFA.9–11): folding the program's per-state step over a duplicate-free list of states of `Q^i` has the law of the pseudocode's `processLayer` on the projection (layer-`i` `p`, layer-`i` `S`, stopped flag, stored total), provided the two states agree on that projection and on layer `i - 1`, and the listed states are still fresh. Induction on the list; each step is `estimateAndSample_bridge` followed by the interrupt test. TEXLINE: algorithm.tex:97-102 -/
theorem processLayer_bridge {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (P : Nfa.Params) (n j i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n)
    (one zero θs : Nfa.Model.Operations.Scalar) (hone : one.get = 1) (hzero : zero.get = 0) (hθ : θs.get = (P.θ : ℚ))
    (S0 : Q → Nfa.Program.Samples) (hnd0 : ∀ q r, ((S0 q).getD r []).Nodup)
    (hlen0 : ∀ q r, ∀ w ∈ (S0 q).getD r [], w.length = i - 1) :
    ∀ (l : List Q) (x : Nfa.Program.CoreState Q) (y : Nfa.Pseudocode.CoreState Q),
    l.Nodup → (∀ q ∈ l, q ∈ Nfa.Pseudocode.layerSet A i) → x.prevS = S0 →
    (∀ q r, ∀ w ∈ (S0 q).getD r [], w ∈ Nfa.Interface.cacheRows x) →
    (∀ q', Nfa.Interface.prevPReal x q' = y.p (i - 1) q') →
    (∀ q' r, Nfa.Interface.prevSet x q' r = y.S (i - 1) q' r) →
    (∀ q', Nfa.Interface.curPReal x q' = y.p i q') →
    (∀ q' r, Nfa.Interface.curSet x q' r = y.S i q' r) →
    x.stopped = y.stopped →
    Nfa.Interface.totalReal x = ((Nfa.Pseudocode.storedTotal A n P y : ℕ) : ℝ) →
    (∀ q ∈ l, y.p i q = 1 ∧ ∀ r, y.S i q r = ∅) →
    (Nfa.Run.tapeLaw (l.flatMap (stateSites P j i))).map (fun f =>
      (Nfa.Interface.curPReal (l.foldl (eStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j (Nfa.Pseudocode.layerList A (i - 1)) one zero θs) x),
       Nfa.Interface.curSet (l.foldl (eStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j (Nfa.Pseudocode.layerList A (i - 1)) one zero θs) x),
       (l.foldl (eStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j (Nfa.Pseudocode.layerList A (i - 1)) one zero θs) x).stopped,
       Nfa.Interface.totalReal (l.foldl (eStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j (Nfa.Pseudocode.layerList A (i - 1)) one zero θs) x)))
      = (Nfa.Pseudocode.processLayer A σ P n i y l).map
          (fun w => (w.p i, w.S i, w.stopped, ((Nfa.Pseudocode.storedTotal A n P w : ℕ) : ℝ))) := by
  have hconst : ∀ {α β : Type} (p : PMF α) (b : β), p.map (fun _ => b) = PMF.pure b :=
    fun p b => PMF.map_const p b
  intro l
  induction l with
  | nil =>
    intro x y _ _ _ _ _ _ hcP hcS hst htot _
    simp only [List.flatMap_nil, List.foldl_nil, Nfa.Pseudocode.processLayer, PMF.pure_map, hconst]
    rw [show Nfa.Interface.curPReal x = y.p i from funext hcP,
      show Nfa.Interface.curSet x = y.S i from funext fun q => funext (hcS q), hst, htot]
  | cons q l ih =>
    intro x y hnd hsub hpS hcache hpP hpSet hcP hcS hst htot hfr
    by_cases hx : x.stopped = true
    · have hy : y.stopped = true := hst ▸ hx
      simp only [eStepFold_stopped _ _ _ _ _ _ _ _ _ _ x hx, Nfa.Pseudocode.processLayer, hy, if_true,
        PMF.pure_map, hconst]
      rw [show Nfa.Interface.curPReal x = y.p i from funext hcP,
        show Nfa.Interface.curSet x = y.S i from funext fun q => funext (hcS q), hst, htot, hy]
    · have hx' : x.stopped = false := by simpa using hx
      have hy' : y.stopped = false := hst ▸ hx'
      have hqL : q ∈ Nfa.Pseudocode.layerSet A i := hsub q List.mem_cons_self
      have hql : q ∉ l := (List.nodup_cons.mp hnd).1
      have hndx : ∀ q' r, ((x.prevS q').getD r []).Nodup := fun q' r => by rw [hpS]; exact hnd0 q' r
      have hlenx : ∀ q' r, ∀ w ∈ (x.prevS q').getD r [], w.length = i - 1 := fun q' r => by
        rw [hpS]; exact hlen0 q' r
      rw [List.flatMap_cons, tapeLaw_eq_drawAll, drawAll_append', PMF.map_bind]
      simp only [Nfa.Pseudocode.processLayer, hy', Bool.false_eq_true, if_false, PMF.map_bind]
      have hbr := estimateAndSample_bridge A σ P j i hi q one zero hone hzero x y hpP hpSet hndx hlenx
        (fun q' r => by rw [hpS]; exact hcache q' r)
      rw [tapeLaw_eq_drawAll] at hbr
      refine pmf_bind_transfer _ _ _ _ hbr _ _ ?_ ?_
      · intro a ha b hb hab
        simp only [Prod.mk.injEq] at hab
        rw [pseudo_eAS_support A σ P i y q a ha, pseudo_eAS_support A σ P i y q b hb, hab.1,
          show a.S i q = b.S i q from funext fun r => congrFun hab.2 r]
      · intro t ht a ha hat
        simp only [Prod.mk.injEq] at hat
        obtain ⟨hatP, hatS⟩ := hat
        -- the pseudocode outcome `a` only rewrote `p(q^i)` and `S(q^i)`
        have hapl : ∀ ℓ, ℓ ≠ i → a.p ℓ = y.p ℓ := by
          intro ℓ hℓ; rw [pseudo_eAS_support A σ P i y q a ha]; simp [Function.update_of_ne hℓ]
        have hasl : ∀ ℓ, ℓ ≠ i → a.S ℓ = y.S ℓ := by
          intro ℓ hℓ; rw [pseudo_eAS_support A σ P i y q a ha]; simp [Function.update_of_ne hℓ]
        have hapq : ∀ q', q' ≠ q → a.p i q' = y.p i q' := by
          intro q' hq'; rw [pseudo_eAS_support A σ P i y q a ha]; simp [Function.update_of_ne hq']
        have hasq : ∀ q', q' ≠ q → a.S i q' = y.S i q' := by
          intro q' hq'; rw [pseudo_eAS_support A σ P i y q a ha]; simp [Function.update_of_ne hq']
        -- the program's state after the step at `q`
        obtain ⟨pv, Sv, tv, hshape⟩ := estimateAndSample_shape A σ P (Nfa.Model.Operations.Tape.ofFun t) j
          (Nfa.Pseudocode.layerList A (i - 1)) one zero x q
        have hx'eq : eStep A σ P (Nfa.Model.Operations.Tape.ofFun t) j (Nfa.Pseudocode.layerList A (i - 1)) one zero θs x q
            = { (Nfa.Program.estimateAndSample A σ P (Nfa.Model.Operations.Tape.ofFun t) j (Nfa.Pseudocode.layerList A (i - 1)) one zero x q).val with
                stopped := (Nfa.Model.Operations.Scalar.le θs (Nfa.Program.estimateAndSample A σ P (Nfa.Model.Operations.Tape.ofFun t) j (Nfa.Pseudocode.layerList A (i - 1)) one zero x q).val.total).val } := by
          unfold eStep; rw [if_neg (by simp [hx'])]
        obtain ⟨hpf, hpl⟩ := predecessors_nodup A i q
        obtain ⟨hsamp, htotq⟩ := estimateAndSample_sample A σ P (Nfa.Model.Operations.Tape.ofFun t) j
          (Nfa.Pseudocode.layerList A (i - 1)) q one zero x i hi hpf hpl hndx hlenx
        -- the stored total after the step
        have hstore := storedTotal_upd A n P y i q (a.p i q) (a.S i q) hin hqL (hfr q List.mem_cons_self).2
        rw [← pseudo_eAS_support A σ P i y q a ha] at hstore
        have hxtot : x.total.get = (Nfa.Pseudocode.storedTotal A n P y : ℚ) := by
          have := htot; simp only [Nfa.Interface.totalReal, Nfa.Interface.real] at this; exact_mod_cast this
        have hcard : ∀ r, ((((Nfa.Program.estimateAndSample A σ P (Nfa.Model.Operations.Tape.ofFun t) j (Nfa.Pseudocode.layerList A (i - 1)) one zero x q).val.curS q).getD r []).length : ℚ)
            = ((a.S i q r).card : ℚ) := by
          intro r
          have h1 := congrFun hatS r
          simp only [Nfa.Interface.curSet, Nfa.Interface.sampleSet] at h1
          rw [h1, List.toFinset_card_of_nodup (hsamp r).1]
        have htot' : (Nfa.Program.estimateAndSample A σ P (Nfa.Model.Operations.Tape.ofFun t) j (Nfa.Pseudocode.layerList A (i - 1)) one zero x q).val.total.get
            = (Nfa.Pseudocode.storedTotal A n P a : ℚ) := by
          rw [htotq, hxtot, hstore, List.map_congr_left (fun r _ => hcard r)]
          push_cast
          rfl
        have hfrm := eStep_frame A σ P (Nfa.Model.Operations.Tape.ofFun t) j (Nfa.Pseudocode.layerList A (i - 1)) one zero θs x q
        have hia : ∀ ℓ, (Nfa.Pseudocode.interrupt A n P a).p ℓ = a.p ℓ := fun _ => rfl
        have hiaS : ∀ ℓ, (Nfa.Pseudocode.interrupt A n P a).S ℓ = a.S ℓ := fun _ => rfl
        rw [PMF.map_comp, ← ih (eStep A σ P (Nfa.Model.Operations.Tape.ofFun t) j (Nfa.Pseudocode.layerList A (i - 1)) one zero θs x q)
          (Nfa.Pseudocode.interrupt A n P a) (List.nodup_cons.mp hnd).2
          (fun q' hq' => hsub q' (List.mem_cons_of_mem q hq')) (hfrm.1.trans hpS) ?hc ?hpp ?hps ?hcp ?hcs ?hst ?htot ?hfr,
          tapeLaw_eq_drawAll]
        case hc =>
          intro q' r w hw
          simp only [Nfa.Interface.cacheRows, hfrm.2.2.2.1]
          exact hcache q' r w hw
        case hpp =>
          intro q'
          simp only [Nfa.Interface.prevPReal, hfrm.2.1, hia, hapl (i - 1) (by omega)]
          exact hpP q'
        case hps =>
          intro q' r
          simp only [Nfa.Interface.prevSet, hfrm.1, hiaS, hasl (i - 1) (by omega)]
          exact hpSet q' r
        case hcp =>
          intro q'
          rw [hia]
          by_cases hq' : q' = q
          · subst hq'; rw [hx'eq]; exact hatP.symm
          · rw [hapq q' hq', ← hcP q']
            simp only [Nfa.Interface.curPReal, (hfrm.2.2.2.2 q' hq').2]
        case hcs =>
          intro q' r
          rw [hiaS]
          by_cases hq' : q' = q
          · subst hq'; rw [hx'eq]; exact (congrFun hatS r).symm
          · rw [hasq q' hq', ← hcS q' r]
            simp only [Nfa.Interface.curSet, (hfrm.2.2.2.2 q' hq').1]
        case hst =>
          rw [hx'eq]
          simp only [Nfa.Pseudocode.interrupt, Nfa.Interface.val_le, hθ, htot']
          simp only [Nat.cast_le]
        case htot =>
          rw [hx'eq]
          simp only [Nfa.Interface.totalReal, Nfa.Interface.real, htot']
          rfl
        case hfr =>
          intro q' hq'
          have hne : q' ≠ q := fun h => hql (h ▸ hq')
          rw [hia, hiaS, hapq q' hne, hasq q' hne]
          exact hfr q' (List.mem_cons_of_mem q hq')
        refine congrArg₂ PMF.map ?_ rfl
        funext g2
        simp only [Function.comp_apply, List.foldl_cons]
        rw [eStep_local A σ P j _ one zero θs i hi x q hlenx _ t ?loc1,
          eStepFold_local A σ P j _ one zero θs i hi S0 hlen0 _ g2 l ?loc2 _ (hfrm.1.trans hpS)]
        case loc1 =>
          intro z h1 h2 h3 h4
          rw [if_pos ((mem_stateSites_iff P j i q z).mpr ⟨h1, h2, h3, h4⟩)]
        case loc2 =>
          intro z h1 h2 h3 h4
          rw [if_neg (fun hm => hql (((mem_stateSites_iff P j i q z).mp hm).2.1 ▸ h2))]

/-- One layer of the program (every state of layer i, then the θ-overflow stop check) has the same law as the pseudocode's `layerStep` on the projection (current p, current S, stopped flag, stored total). -/
theorem layerStep_bridge {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (P : Nfa.Params) (n j i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) (layers : Array (List Q)) (hlayers : ∀ ℓ ≤ n, layers.getD ℓ [] = Nfa.Pseudocode.layerList A ℓ) (one zero θs : Nfa.Model.Operations.Scalar) (hone : one.get = 1) (hzero : zero.get = 0) (hθ : θs.get = (P.θ : ℚ)) (s : Nfa.Program.CoreState Q) (st : Nfa.Pseudocode.CoreState Q) (hidx : s.layerIdx ≤ i - 1) (hrun : s.stopped = false → s.layerIdx = i - 1) (hproj : ((fun q => if s.layerIdx = i - 1 then Nfa.Interface.curPReal s q else 1), (fun q r => if s.layerIdx = i - 1 then Nfa.Interface.curSet s q r else ∅), s.stopped, Nfa.Interface.totalReal s) = (st.p (i - 1), st.S (i - 1), st.stopped, ((Nfa.Pseudocode.storedTotal A n P st : ℕ) : ℝ))) (hnd : ∀ q r, ((s.curS q).getD r []).Nodup) (hlen : s.stopped = false → ∀ q r, ∀ w ∈ (s.curS q).getD r [], w.length = i - 1) (hcache : s.stopped = false → ∀ q r, ∀ w ∈ (s.curS q).getD r [], w ∈ Nfa.Interface.cacheRows s) (hfresh : ∀ ℓ, i ≤ ℓ → ∀ q, st.p ℓ q = 1 ∧ ∀ r, st.S ℓ q r = ∅) : (Nfa.Run.tapeLaw ((Finset.univ : Finset Q).toList.flatMap fun q => (List.range P.α).flatMap fun r => (none :: (Finset.univ : Finset Q).toList.map some).flatMap fun src => (Nfa.Run.words i).map fun u => (⟨j, q, r, src, u⟩ : Nfa.Model.Operations.Site Q))).map (fun f => ((fun q => if (Nfa.Program.layerStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j layers one zero θs s i).val.layerIdx = i then Nfa.Interface.curPReal (Nfa.Program.layerStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j layers one zero θs s i).val q else 1), (fun q r => if (Nfa.Program.layerStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j layers one zero θs s i).val.layerIdx = i then Nfa.Interface.curSet (Nfa.Program.layerStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j layers one zero θs s i).val q r else ∅), (Nfa.Program.layerStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j layers one zero θs s i).val.stopped, Nfa.Interface.totalReal (Nfa.Program.layerStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j layers one zero θs s i).val)) = (Nfa.Pseudocode.layerStep A σ P n st i).map (fun st' => (st'.p i, st'.S i, st'.stopped, ((Nfa.Pseudocode.storedTotal A n P st' : ℕ) : ℝ))) := by
  classical
  have hconst : ∀ {α β : Type} (p : PMF α) (b : β), p.map (fun _ => b) = PMF.pure b :=
    fun p b => PMF.map_const p b
  simp only [Prod.mk.injEq] at hproj
  obtain ⟨hP, hS, hstop, htot⟩ := hproj
  by_cases hs : s.stopped = true
  · have hst : st.stopped = true := hstop ▸ hs
    have hval : ∀ f, (Nfa.Program.layerStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j layers one zero θs s i).val = s :=
      fun f => by simp [Nfa.Program.layerStep, hs]
    have hli : s.layerIdx ≠ i := by omega
    simp only [hval, hli, if_false, hconst]
    unfold Nfa.Pseudocode.layerStep
    rw [if_pos hst, PMF.pure_map]
    have hpi : st.p i = fun _ => 1 := funext fun q => (hfresh i le_rfl q).1
    have hSi : st.S i = fun _ _ => ∅ := funext fun q => funext fun r => (hfresh i le_rfl q).2 r
    rw [hpi, hSi, hs, hst, htot]
  · have hs' : s.stopped = false := by simpa using hs
    have hli : s.layerIdx = i - 1 := hrun hs'
    simp only [hli, if_true] at hP hS
    have hst : st.stopped = false := hstop ▸ hs'
    have hcur : layers.getD i [] = Nfa.Pseudocode.layerList A i := hlayers i hin
    have hprev : layers.getD (i - 1) [] = Nfa.Pseudocode.layerList A (i - 1) := hlayers (i - 1) (by omega)
    have hfun : ∀ f : Nfa.Model.Operations.Site Q → ℕ,
        ((fun q => if (Nfa.Program.layerStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j layers one zero θs s i).val.layerIdx = i then Nfa.Interface.curPReal (Nfa.Program.layerStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j layers one zero θs s i).val q else 1),
         (fun q r => if (Nfa.Program.layerStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j layers one zero θs s i).val.layerIdx = i then Nfa.Interface.curSet (Nfa.Program.layerStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j layers one zero θs s i).val q r else ∅),
         (Nfa.Program.layerStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j layers one zero θs s i).val.stopped,
         Nfa.Interface.totalReal (Nfa.Program.layerStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j layers one zero θs s i).val)
        = (Nfa.Interface.curPReal (List.foldl (eStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j (Nfa.Pseudocode.layerList A (i - 1)) one zero θs) (shiftState s one i) (Nfa.Pseudocode.layerList A i)), Nfa.Interface.curSet (List.foldl (eStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j (Nfa.Pseudocode.layerList A (i - 1)) one zero θs) (shiftState s one i) (Nfa.Pseudocode.layerList A i)), (List.foldl (eStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j (Nfa.Pseudocode.layerList A (i - 1)) one zero θs) (shiftState s one i) (Nfa.Pseudocode.layerList A i)).stopped, Nfa.Interface.totalReal (List.foldl (eStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j (Nfa.Pseudocode.layerList A (i - 1)) one zero θs) (shiftState s one i) (Nfa.Pseudocode.layerList A i))) := by
      intro f
      have hf := layerStep_fields A σ P (Nfa.Model.Operations.Tape.ofFun f) j layers one zero θs s i hs'
      simp only [coreFields, Prod.mk.injEq] at hf
      obtain ⟨-, -, hcP, hcS, hli2, htot2, hst2⟩ := hf
      rw [hprev, hcur] at hcP hcS hli2 htot2 hst2
      have hidx2 := (eStepFold_inv A σ P (Nfa.Model.Operations.Tape.ofFun f) j one zero θs i hi s.curS hnd (hlen hs')
        (Nfa.Pseudocode.layerList A i) (shiftState s one i) rfl (fun q r => by simp [shiftState])).2.1
      simp only [shiftState] at hidx2
      simp only [Nfa.Interface.curPReal, Nfa.Interface.curSet, Nfa.Interface.totalReal, hcP, hcS, hli2, htot2,
        hst2, hidx2, if_true]
      rfl
    simp only [hfun]
    have hLeq : ((Finset.univ : Finset Q).toList.flatMap fun q => (List.range P.α).flatMap fun r => (none :: (Finset.univ : Finset Q).toList.map some).flatMap fun src => (Nfa.Run.words i).map fun u => (⟨j, q, r, src, u⟩ : Nfa.Model.Operations.Site Q))
        = (Finset.univ : Finset Q).toList.flatMap (stateSites P j i) := rfl
    rw [hLeq, tapeLaw_eq_drawAll, drawAll_marginal _ _ _ ((Nfa.Pseudocode.layerList A i).flatMap (stateSites P j i))
      (stateSites_flatMap_nodup P j i _ (Finset.nodup_toList _))
      (stateSites_flatMap_nodup P j i _ (Finset.sort_nodup _ _)) ?hsub _ ?hG, ← tapeLaw_eq_drawAll]
    case hsub =>
      intro x hx
      obtain ⟨h1, -, h3, h4⟩ := (mem_flatMap_stateSites_iff P j i _ x).mp hx
      exact (mem_flatMap_stateSites_iff P j i _ x).mpr ⟨h1, Finset.mem_toList.mpr (Finset.mem_univ _), h3, h4⟩
    case hG =>
      intro g g' hgg
      rw [eStepFold_local A σ P j _ one zero θs i hi s.curS (hlen hs') g g' (Nfa.Pseudocode.layerList A i)
        (fun z h1 h2 h3 h4 => hgg z ((mem_flatMap_stateSites_iff P j i _ z).mpr ⟨h1, h2, h3, h4⟩)) _ rfl]
    have hmemL : ∀ q ∈ Nfa.Pseudocode.layerList A i, q ∈ Nfa.Pseudocode.layerSet A i :=
      fun q hq => (Finset.mem_sort _).mp hq
    rw [processLayer_bridge A σ P n j i hi hin one zero θs hone hzero hθ s.curS hnd (hlen hs')
      (Nfa.Pseudocode.layerList A i) (shiftState s one i) st (Finset.sort_nodup _ _) hmemL rfl
      (hcache hs') (fun q' => congrFun hP q') (fun q' r => congrFun (congrFun hS q') r) ?hcp ?hcs hstop htot
      (fun q _ => hfresh i le_rfl q)]
    case hcp =>
      intro q'
      simp [Nfa.Interface.curPReal, Nfa.Interface.real, shiftState, hone, (hfresh i le_rfl q').1]
    case hcs =>
      intro q' r
      simp [Nfa.Interface.curSet, Nfa.Interface.sampleSet, shiftState, (hfresh i le_rfl q').2 r]
    unfold Nfa.Pseudocode.layerStep
    rw [if_neg (by simp [hst])]

/-- INTERNAL: folding the program's layer step over layers `i, …, i + k - 1` reads the tape only at sites of run `j`, repetition `< α`, word length `≥ i`. Induction from `layerStep_local`, carrying `layerStep_invariants`. -/
theorem runLayers_local {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (P : Nfa.Params) (n j : ℕ) (layers : Array (List Q)) (hlayers : ∀ ℓ ≤ n, layers.getD ℓ [] = Nfa.Pseudocode.layerList A ℓ) (one zero θs : Nfa.Model.Operations.Scalar) (f f' : Nfa.Model.Operations.Site Q → ℕ) :
    ∀ (k i : ℕ) (s : Nfa.Program.CoreState Q), 1 ≤ i → i + k ≤ n + 1 →
    s.layerIdx ≤ i - 1 → (s.stopped = false → s.layerIdx = i - 1) →
    (∀ q r, ((s.curS q).getD r []).Nodup) →
    (s.stopped = false → ∀ q r, ∀ w ∈ (s.curS q).getD r [], w.length = i - 1) →
    (∀ x : Nfa.Model.Operations.Site Q, x.run = j → x.rep < P.α → i ≤ x.word.length → x.word.length < i + k → f x = f' x) →
    (Arlib.Computation.Charged.foldl (Nfa.Program.layerStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j layers one zero θs) (List.range' i k) s).val
      = (Arlib.Computation.Charged.foldl (Nfa.Program.layerStep A σ P (Nfa.Model.Operations.Tape.ofFun f') j layers one zero θs) (List.range' i k) s).val := by
  intro k
  induction k with
  | zero =>
    intro i s _ _ _ _ _ _ _
    simp only [List.range'_zero, Arlib.Computation.Charged.val_foldl_nil]
  | succ k ih =>
    intro i s hi hk hidx hrun hnd hlen hff
    rw [List.range'_succ, Arlib.Computation.Charged.val_foldl_cons, Arlib.Computation.Charged.val_foldl_cons,
      Nfa.layerStep_local A σ P j layers one zero θs s i hi hlen f f'
        (fun x h1 h2 h3 => hff x h1 h2 (by omega) (by omega))]
    have hprev : layers.getD (i - 1) [] = Nfa.Pseudocode.layerList A (i - 1) := hlayers _ (by omega)
    obtain ⟨h1, h2, h3, h4, -⟩ := Nfa.layerStep_invariants A σ P (Nfa.Model.Operations.Tape.ofFun f') j
      layers one zero θs s i hi hprev hidx hrun hnd hlen
    exact ih (i + 1) _ (by omega) (by omega) (by simpa using h1) (by simpa using h2) h3
      (by simpa using h4) (fun x a b c d => hff x a b (by omega) (by omega))

/-- Induction on k: folding the program's layer step over layers i..i+k-1 has the same law as the pseudocode's `runLayers` on the same projection, because the invariants carry from one layer to the next. -/
theorem runLayers_bridge {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (P : Nfa.Params) (n j i k : ℕ) (hi : 1 ≤ i) (hk : i + k ≤ n + 1) (layers : Array (List Q)) (hlayers : ∀ ℓ ≤ n, layers.getD ℓ [] = Nfa.Pseudocode.layerList A ℓ) (one zero θs : Nfa.Model.Operations.Scalar) (hone : one.get = 1) (hzero : zero.get = 0) (hθ : θs.get = (P.θ : ℚ)) (s : Nfa.Program.CoreState Q) (st : Nfa.Pseudocode.CoreState Q) (hidx : s.layerIdx ≤ i - 1) (hrun : s.stopped = false → s.layerIdx = i - 1) (hproj : ((fun q => if s.layerIdx = i - 1 then Nfa.Interface.curPReal s q else 1), (fun q r => if s.layerIdx = i - 1 then Nfa.Interface.curSet s q r else ∅), s.stopped, Nfa.Interface.totalReal s) = (st.p (i - 1), st.S (i - 1), st.stopped, ((Nfa.Pseudocode.storedTotal A n P st : ℕ) : ℝ))) (hnd : ∀ q r, ((s.curS q).getD r []).Nodup) (hlen : s.stopped = false → ∀ q r, ∀ w ∈ (s.curS q).getD r [], w.length = i - 1) (hcache : s.stopped = false → ∀ q r, ∀ w ∈ (s.curS q).getD r [], w ∈ Nfa.Interface.cacheRows s) (hfresh : ∀ ℓ, i ≤ ℓ → ∀ q, st.p ℓ q = 1 ∧ ∀ r, st.S ℓ q r = ∅) : (Nfa.Run.tapeLaw ((List.range' i k).flatMap fun ℓ => (Finset.univ : Finset Q).toList.flatMap fun q => (List.range P.α).flatMap fun r => (none :: (Finset.univ : Finset Q).toList.map some).flatMap fun src => (Nfa.Run.words ℓ).map fun u => (⟨j, q, r, src, u⟩ : Nfa.Model.Operations.Site Q))).map (fun f => ((fun q => if (Arlib.Computation.Charged.foldl (Nfa.Program.layerStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j layers one zero θs) (List.range' i k) s).val.layerIdx = i + k - 1 then Nfa.Interface.curPReal (Arlib.Computation.Charged.foldl (Nfa.Program.layerStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j layers one zero θs) (List.range' i k) s).val q else 1), (fun q r => if (Arlib.Computation.Charged.foldl (Nfa.Program.layerStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j layers one zero θs) (List.range' i k) s).val.layerIdx = i + k - 1 then Nfa.Interface.curSet (Arlib.Computation.Charged.foldl (Nfa.Program.layerStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j layers one zero θs) (List.range' i k) s).val q r else ∅), (Arlib.Computation.Charged.foldl (Nfa.Program.layerStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j layers one zero θs) (List.range' i k) s).val.stopped, Nfa.Interface.totalReal (Arlib.Computation.Charged.foldl (Nfa.Program.layerStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j layers one zero θs) (List.range' i k) s).val)) = (Nfa.Pseudocode.runLayers A σ P n st (List.range' i k)).map (fun st' => (st'.p (i + k - 1), st'.S (i + k - 1), st'.stopped, ((Nfa.Pseudocode.storedTotal A n P st' : ℕ) : ℝ))) := by
  classical
  induction k generalizing i s st with
  | zero =>
    simp only [List.range'_zero, List.flatMap_nil, Arlib.Computation.Charged.val_foldl_nil,
      Nfa.Pseudocode.runLayers, PMF.pure_map, Nfa.Run.tapeLaw, Nat.add_zero]
    rw [hproj]
  | succ k ih =>
    rw [show i + (k + 1) - 1 = i + 1 + k - 1 by omega]
    have hsplit : ∀ F : ℕ → List (Nfa.Model.Operations.Site Q),
        (List.range' i (k + 1)).flatMap F = F i ++ (List.range' (i + 1) k).flatMap F := by
      intro F; rw [List.range'_succ, List.flatMap_cons]
    rw [hsplit]
    simp only [List.range'_succ, Arlib.Computation.Charged.val_foldl_cons,
      Nfa.Pseudocode.runLayers, PMF.map_bind]
    rw [tapeLaw_eq_drawAll, drawAll_append', PMF.map_bind]
    have hbr := layerStep_bridge A σ P n j i hi (by omega) layers hlayers one zero θs hone hzero hθ s st
      hidx hrun hproj hnd hlen hcache hfresh
    rw [tapeLaw_eq_drawAll] at hbr
    have hfr : ∀ c ∈ (Nfa.Pseudocode.layerStep A σ P n st i).support,
        c = ({ p := Function.update st.p i (c.p i), S := Function.update st.S i (c.S i),
               stopped := c.stopped } : Nfa.Pseudocode.CoreState Q) := by
      intro c hc
      rw [Nfa.Analysis.layerStep_frame] at hc
      obtain ⟨c0, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hc
      simp
    refine pmf_bind_transfer _ _ _ _ hbr _ _ ?_ ?_
    · intro a ha b hb hab
      simp only [Prod.mk.injEq] at hab
      rw [hfr a ha, hfr b hb, hab.1, hab.2.1, hab.2.2.1]
    · intro t ht a ha hat
      have hprev : layers.getD (i - 1) [] = Nfa.Pseudocode.layerList A (i - 1) := hlayers _ (by omega)
      obtain ⟨h1, h2, h3, h4, h5⟩ := Nfa.layerStep_invariants A σ P
        (Nfa.Model.Operations.Tape.ofFun t) j layers one zero θs s i hi hprev hidx hrun hnd hlen
      rw [PMF.map_comp, ← ih (i + 1) (by omega) (by omega) _ a (by rw [Nat.add_sub_cancel]; exact h1)
        (by rw [Nat.add_sub_cancel]; exact h2) (by rw [Nat.add_sub_cancel]; exact hat.symm) h3
        (by rw [Nat.add_sub_cancel]; exact h4) h5 ?fresh, tapeLaw_eq_drawAll]
      case fresh =>
        intro ℓ hℓ q
        rw [hfr a ha]
        simp only [Function.update_of_ne (show ℓ ≠ i by omega)]
        exact hfresh ℓ (by omega) q
      refine congrArg₂ PMF.map ?_ rfl
      funext g2
      simp only [Function.comp_apply]
      rw [Nfa.layerStep_local A σ P j layers one zero θs s i hi hlen _ t ?loc1]
      case loc1 =>
        intro x hx1 hx2 hx3
        rw [if_pos ((mem_layerSites_iff P j i x).mpr ⟨hx1, hx2, hx3⟩)]
      rw [runLayers_local A σ P n j layers hlayers one zero θs _ g2 k (i + 1) _ (by omega) (by omega)
        (by rw [Nat.add_sub_cancel]; exact h1) (by rw [Nat.add_sub_cancel]; exact h2) h3
        (by rw [Nat.add_sub_cancel]; exact h4) ?loc2]
      case loc2 =>
        intro x hx1 hx2 hx3 _
        rw [if_neg (fun hm => by have := ((mem_layerSites_iff P j i x).mp hm).2.2; omega)]

/-- INTERNAL: the program's core state after the setup of `coreRun` (countNFA.4–6): `p ≡ 1`, `S^r(q_I) = {λ}` for `r < α`, total `α`, cache `{λ}`, layer `0`. -/
noncomputable def coreInit {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (P : Nfa.Params) : Nfa.Program.CoreState Q :=
  { prevP := fun _ => (Nfa.Model.Operations.Scalar.lit 1).val, prevS := fun _ => #[],
    curP := fun _ => (Nfa.Model.Operations.Scalar.lit 1).val,
    curS := Function.update (fun _ => #[]) A.qI (Arlib.Computation.Charged.foldl (fun (acc : Nfa.Program.Samples) (_ : ℕ) =>
      (do let T ← Nfa.Model.Operations.addWord [] []
          pure (acc.push T) : Arlib.Computation.Charged Nfa.Model.Operations.Op Nfa.Model.Operations.Cell Nfa.Program.Samples))
      (List.range P.α) #[]).val,
    layerIdx := 0,
    total := (Nfa.Model.Operations.Scalar.lit (P.α : ℚ)).val,
    cache := (Arlib.Computation.Roster.insert (κ := Nfa.Model.Operations.Op) (κₛ := Nfa.Model.Operations.Cell) ([] : List Bool) Arlib.Computation.Roster.empty).val,
    stopped := false }

/-- INTERNAL: the stored samples of the initial core state. -/
theorem coreInit_curS {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (P : Nfa.Params) (q : Q) (r : ℕ) :
    ((coreInit A P).curS q).getD r [] = if q = A.qI ∧ r < P.α then [[]] else [] := by
  by_cases hq : q = A.qI
  · subst hq
    simp only [coreInit, Function.update_self, Arlib.Computation.Charged.val_bind,
      Arlib.Computation.Charged.val_pure, cfoldl_val, Nfa.Interface.val_addWord, true_and]
    exact foldl_push_range_getD (fun _ => [[]]) P.α r []
  · simp [coreInit, hq]

/-- INTERNAL: the value of one core run, as the initial state folded through layers `1..n`, then `1/p(q_F)`. -/
theorem coreRun_val {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (P : Nfa.Params) (t : Nfa.Model.Operations.Tape Q) (n : ℕ) (layers : Array (List Q)) (j : ℕ) :
    (Nfa.Program.coreRun A σ P t n layers j).val
      = (Nfa.Model.Operations.Scalar.div (Nfa.Model.Operations.Scalar.lit 1).val
          (if (Arlib.Computation.Charged.foldl (Nfa.Program.layerStep A σ P t j layers (Nfa.Model.Operations.Scalar.lit 1).val (Nfa.Model.Operations.Scalar.lit 0).val (Nfa.Model.Operations.Scalar.lit (P.θ : ℚ)).val) (List.range' 1 n) (coreInit A P)).val.layerIdx = n
            then (Arlib.Computation.Charged.foldl (Nfa.Program.layerStep A σ P t j layers (Nfa.Model.Operations.Scalar.lit 1).val (Nfa.Model.Operations.Scalar.lit 0).val (Nfa.Model.Operations.Scalar.lit (P.θ : ℚ)).val) (List.range' 1 n) (coreInit A P)).val.curP A.qF
            else (Nfa.Model.Operations.Scalar.lit 1).val)).val := rfl

/-- INTERNAL: core run `j` reads the tape only at the sites of run `j`, repetition `< α`, word length in `1..n`. -/
theorem coreRun_local {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (P : Nfa.Params) (n j : ℕ)
    (f f' : Nfa.Model.Operations.Site Q → ℕ)
    (hff : ∀ x : Nfa.Model.Operations.Site Q, x.run = j → x.rep < P.α → 1 ≤ x.word.length → x.word.length < 1 + n → f x = f' x) :
    (Nfa.Program.coreRun A σ P (Nfa.Model.Operations.Tape.ofFun f) n (Nfa.Program.unroll A n).val j).val
      = (Nfa.Program.coreRun A σ P (Nfa.Model.Operations.Tape.ofFun f') n (Nfa.Program.unroll A n).val j).val := by
  rw [coreRun_val, coreRun_val, runLayers_local A σ P n j _ (fun ℓ hℓ => unroll_getD A n ℓ hℓ) _ _ _ f f' n 1
    (coreInit A P) le_rfl (by omega) (by simp [coreInit]) (by simp [coreInit]) ?hnd ?hlen hff]
  case hnd =>
    intro q r; rw [coreInit_curS]; split_ifs <;> simp
  case hlen =>
    intro _ q r w hw; rw [coreInit_curS] at hw; split_ifs at hw <;> simp_all

/-- One whole core trial j of the program (initialise, run layers 1..n, read off the answer) has the same law as the pseudocode's `coreRun`. -/
theorem coreRun_bridge {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (P : Nfa.Params) (n j : ℕ) : (Nfa.Run.tapeLaw ((List.range' 1 n).flatMap fun ℓ => (Finset.univ : Finset Q).toList.flatMap fun q => (List.range P.α).flatMap fun r => (none :: (Finset.univ : Finset Q).toList.map some).flatMap fun src => (Nfa.Run.words ℓ).map fun u => (⟨j, q, r, src, u⟩ : Nfa.Model.Operations.Site Q))).map (fun f => Nfa.Interface.answer (Nfa.Program.coreRun A σ P (Nfa.Model.Operations.Tape.ofFun f) n (Nfa.Program.unroll A n).val j)) = Nfa.Pseudocode.coreRun A σ P n := by
  classical
  have hlayers : ∀ ℓ ≤ n, (Nfa.Program.unroll A n).val.getD ℓ [] = Nfa.Pseudocode.layerList A ℓ :=
    fun ℓ hℓ => unroll_getD A n ℓ hℓ
  let one := (Nfa.Model.Operations.Scalar.lit 1).val
  let zero := (Nfa.Model.Operations.Scalar.lit 0).val
  let θs := (Nfa.Model.Operations.Scalar.lit (P.θ : ℚ)).val
  let s0 : Nfa.Program.CoreState Q := coreInit A P
  have hcurS : ∀ q r, (s0.curS q).getD r [] = if q = A.qI ∧ r < P.α then [[]] else [] := coreInit_curS A P
  have hqI : A.qI ∈ Nfa.Pseudocode.layerSet A 0 := by
    have h0 := layerList_zero A
    rw [Nfa.Pseudocode.layerList] at h0
    rw [← Finset.mem_sort (· ≤ ·), h0]; simp
  have hst : Nfa.Pseudocode.storedTotal A n P (Nfa.Pseudocode.initState A P) = P.α := by
    unfold Nfa.Pseudocode.storedTotal Nfa.Pseudocode.initState
    rw [Finset.sum_eq_single 0]
    · rw [Finset.sum_eq_single A.qI]
      · rw [Finset.sum_congr rfl (g := fun _ => 1) (fun x hx => by
          simp [Finset.mem_range.mp hx])]
        simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd hqI h
    · intro b _ hb; simp [hb]
    · intro h; simp at h
  have hcr : ∀ f, (Nfa.Program.coreRun A σ P (Nfa.Model.Operations.Tape.ofFun f) n (Nfa.Program.unroll A n).val j).val
      = (Nfa.Model.Operations.Scalar.div one
          (if (Arlib.Computation.Charged.foldl (Nfa.Program.layerStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j (Nfa.Program.unroll A n).val one zero θs) (List.range' 1 n) s0).val.layerIdx = n
            then (Arlib.Computation.Charged.foldl (Nfa.Program.layerStep A σ P (Nfa.Model.Operations.Tape.ofFun f) j (Nfa.Program.unroll A n).val one zero θs) (List.range' 1 n) s0).val.curP A.qF
            else one)).val := fun f => rfl
  have hb := runLayers_bridge A σ P n j 1 n le_rfl (by omega) _ hlayers one zero θs
    (by simp [one]) (by simp [zero]) (by simp [θs]) s0 (Nfa.Pseudocode.initState A P)
    (by simp [s0, coreInit]) (by simp [s0, coreInit]) ?hproj ?hnd ?hlen ?hcache ?hfresh
  case hproj =>
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_, rfl, ?_⟩
    · funext q
      simp [s0, coreInit, Nfa.Interface.curPReal, Nfa.Interface.real, one, Nfa.Pseudocode.initState]
    · funext q r
      rw [if_pos (by simp [s0, coreInit])]
      simp only [Nfa.Interface.curSet, Nfa.Interface.sampleSet, hcurS, Nfa.Pseudocode.initState]
      split_ifs <;> simp_all
    · rw [hst]
      simp [Nfa.Interface.totalReal, Nfa.Interface.real, s0, coreInit]
  case hnd =>
    intro q r; rw [hcurS]; split_ifs <;> simp
  case hlen =>
    intro _ q r w hw; rw [hcurS] at hw; split_ifs at hw <;> simp_all
  case hcache =>
    intro _ q r w hw; rw [hcurS] at hw
    split_ifs at hw
    · simp only [List.mem_singleton] at hw; subst hw
      simp [Nfa.Interface.cacheRows, s0, coreInit]
    · simp at hw
  case hfresh =>
    intro ℓ hℓ q
    refine ⟨rfl, fun r => ?_⟩
    simp only [Nfa.Pseudocode.initState]
    rw [if_neg (by omega)]
  rw [Nfa.Pseudocode.coreRun, Nfa.Pseudocode.coreLaw]
  have hsplit : (Nfa.Pseudocode.runLayers A σ P n (Nfa.Pseudocode.initState A P) (List.range' 1 n)).map (Nfa.Pseudocode.coreEstimate A n)
      = ((Nfa.Pseudocode.runLayers A σ P n (Nfa.Pseudocode.initState A P) (List.range' 1 n)).map
          (fun st' => (st'.p (1 + n - 1), st'.S (1 + n - 1), st'.stopped, ((Nfa.Pseudocode.storedTotal A n P st' : ℕ) : ℝ)))).map
          (fun x => 1 / x.1 A.qF) := by
    rw [PMF.map_comp]; congr 1; funext st'
    simp [Nfa.Pseudocode.coreEstimate]
  rw [hsplit, ← hb, PMF.map_comp]
  congr 1; funext f
  simp only [Function.comp_apply, Nfa.Interface.answer, hcr]
  rw [show 1 + n - 1 = n by omega]
  split_ifs <;> simp [Nfa.Interface.real, Nfa.Interface.curPReal, one]

/-- INTERNAL: a flat-map is duplicate-free when its blocks are, the index list is, and each element remembers its block through `key`. -/
private theorem nodup_flatMap_key {α β : Type} (l : List α) (g : α → List β) (key : β → α) (hl : l.Nodup)
    (hg : ∀ a ∈ l, (g a).Nodup) (hk : ∀ a ∈ l, ∀ x ∈ g a, key x = a) : (l.flatMap g).Nodup :=
  nodup_flatMap_of l g hl hg (fun a ha b hb x hxa hxb => (hk a ha x hxa).symm.trans (hk b hb x hxb))

/-- INTERNAL: the block of `Run.sites` belonging to core run `j`, in `Run.sites` order. -/
theorem mem_runBlock_iff {Q : Type} [Fintype Q] (P : Nfa.Params) (n j : ℕ) (x : Nfa.Model.Operations.Site Q) :
    x ∈ ((Finset.univ : Finset Q).toList.flatMap fun q => (List.range P.α).flatMap fun r => (none :: (Finset.univ : Finset Q).toList.map some).flatMap fun src => (List.range' 1 n).flatMap fun ℓ => (Nfa.Run.words ℓ).map fun u => (⟨j, q, r, src, u⟩ : Nfa.Model.Operations.Site Q)) ↔ x.run = j ∧ x.rep < P.α ∧ 1 ≤ x.word.length ∧ x.word.length < 1 + n := by
  obtain ⟨run, q, r, src, u⟩ := x
  simp only [List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons, Finset.mem_toList,
    Finset.mem_univ, true_and, words_mem_iff, List.mem_range'_1, Nfa.Model.Operations.Site.mk.injEq]
  constructor
  · rintro ⟨q', r', hr', src', -, ℓ, hℓ, u', hu', rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨rfl, hr', hu' ▸ hℓ.1, hu' ▸ hℓ.2⟩
  · rintro ⟨rfl, hr, h1, h2⟩
    refine ⟨q, r, hr, src, ?_, u.length, ⟨h1, h2⟩, u, rfl, rfl, rfl, rfl, rfl, rfl⟩
    cases src with
    | none => exact Or.inl rfl
    | some q'' => exact Or.inr ⟨q'', rfl⟩

/-- INTERNAL: the same block, in the layer-major order of `coreRun_bridge`. -/
theorem mem_runBlock'_iff {Q : Type} [Fintype Q] (P : Nfa.Params) (n j : ℕ) (x : Nfa.Model.Operations.Site Q) :
    x ∈ ((List.range' 1 n).flatMap fun ℓ => (Finset.univ : Finset Q).toList.flatMap fun q => (List.range P.α).flatMap fun r => (none :: (Finset.univ : Finset Q).toList.map some).flatMap fun src => (Nfa.Run.words ℓ).map fun u => (⟨j, q, r, src, u⟩ : Nfa.Model.Operations.Site Q)) ↔ x.run = j ∧ x.rep < P.α ∧ 1 ≤ x.word.length ∧ x.word.length < 1 + n := by
  obtain ⟨run, q, r, src, u⟩ := x
  simp only [List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons, Finset.mem_toList,
    Finset.mem_univ, true_and, words_mem_iff, List.mem_range'_1, Nfa.Model.Operations.Site.mk.injEq]
  constructor
  · rintro ⟨ℓ, hℓ, q', r', hr', src', -, u', hu', rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨rfl, hr', hu' ▸ hℓ.1, hu' ▸ hℓ.2⟩
  · rintro ⟨rfl, hr, h1, h2⟩
    refine ⟨u.length, ⟨h1, h2⟩, q, r, hr, src, ?_, u, rfl, rfl, rfl, rfl, rfl, rfl⟩
    cases src with
    | none => exact Or.inl rfl
    | some q'' => exact Or.inr ⟨q'', rfl⟩

/-- INTERNAL: the core-run block in `Run.sites` order is duplicate-free. -/
theorem runBlock_nodup {Q : Type} [Fintype Q] (P : Nfa.Params) (n j : ℕ) : ((Finset.univ : Finset Q).toList.flatMap fun q => (List.range P.α).flatMap fun r => (none :: (Finset.univ : Finset Q).toList.map some).flatMap fun src => (List.range' 1 n).flatMap fun ℓ => (Nfa.Run.words ℓ).map fun u => (⟨j, q, r, src, u⟩ : Nfa.Model.Operations.Site Q)).Nodup := by
  have hsrc : (none :: (Finset.univ : Finset Q).toList.map some).Nodup :=
    List.nodup_cons.mpr ⟨by simp, (Finset.nodup_toList _).map (Option.some_injective _)⟩
  refine nodup_flatMap_key _ _ Nfa.Model.Operations.Site.state (Finset.nodup_toList _) (fun q _ => ?_) ?_
  · refine nodup_flatMap_key _ _ Nfa.Model.Operations.Site.rep List.nodup_range (fun r _ => ?_) ?_
    · refine nodup_flatMap_key _ _ Nfa.Model.Operations.Site.source hsrc (fun src _ => ?_) ?_
      · refine nodup_flatMap_key _ _ (fun x => x.word.length) List.nodup_range' (fun ℓ _ => ?_) ?_
        · exact (words_nodup ℓ).map (fun u u' h => by simpa using h)
        · intro ℓ _ x hx
          obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
          exact (words_mem_iff ℓ u).mp hu
      · intro src _ x hx
        obtain ⟨ℓ, -, u, -, rfl⟩ := by simpa only [List.mem_flatMap, List.mem_map] using hx
        rfl
    · intro r _ x hx
      obtain ⟨src, -, ℓ, -, u, -, rfl⟩ := by simpa only [List.mem_flatMap, List.mem_map] using hx
      rfl
  · intro q _ x hx
    obtain ⟨r, -, src, -, ℓ, -, u, -, rfl⟩ := by simpa only [List.mem_flatMap, List.mem_map] using hx
    rfl

/-- INTERNAL: the core-run block in layer-major order is duplicate-free. -/
theorem runBlock'_nodup {Q : Type} [Fintype Q] (P : Nfa.Params) (n j : ℕ) : ((List.range' 1 n).flatMap fun ℓ => (Finset.univ : Finset Q).toList.flatMap fun q => (List.range P.α).flatMap fun r => (none :: (Finset.univ : Finset Q).toList.map some).flatMap fun src => (Nfa.Run.words ℓ).map fun u => (⟨j, q, r, src, u⟩ : Nfa.Model.Operations.Site Q)).Nodup := by
  refine nodup_flatMap_key _ _ (fun x => x.word.length) List.nodup_range' (fun ℓ _ => ?_) ?_
  · exact stateSites_flatMap_nodup P j ℓ _ (Finset.nodup_toList _)
  · intro ℓ _ x hx
    exact ((mem_flatMap_stateSites_iff P j ℓ _ x).mp hx).2.2.2

/-- INTERNAL: the value of the program's `countNFA`: `0` on an empty slice, otherwise the median of the `μ` core runs. -/
theorem countNFA_val {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (n : ℕ) (P : Nfa.Params) (t : Nfa.Model.Operations.Tape Q) :
    (Nfa.Program.countNFA A σ n P t).val
      = if (Nfa.Program.acceptsAtLength A (Nfa.Program.unroll A n).val n).val = true then
          (Nfa.Model.Operations.Scalar.median ((List.range P.μ).map fun j => (Nfa.Program.coreRun A σ P t n (Nfa.Program.unroll A n).val j).val)).val
        else (Nfa.Model.Operations.Scalar.lit 0).val := by
  unfold Nfa.Program.countNFA
  simp only [Arlib.Computation.Charged.val_bind, apply_ite Arlib.Computation.Charged.val, cfoldl_val,
    Arlib.Computation.Charged.val_pure, foldl_snoc_eq, List.nil_append]

/-- The program's answer, pushed forward along the tape law of all its sites, equals the pseudocode's `countNFA`: the emptiness check followed by the median of independent core trials. The median agreement is an Analysis-side helper. -/
theorem countNFA_bridge {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (n : ℕ) (P : Nfa.Params) : (Nfa.Run.tapeLaw (Nfa.Run.sites (Q := Q) n P)).map (fun f => Nfa.Interface.answer (Nfa.Program.countNFA A σ n P (Nfa.Model.Operations.Tape.ofFun f))) = Nfa.Pseudocode.countNFA A σ n P := by
  classical
  have hconst : ∀ {α β : Type} (p : PMF α) (b : β), p.map (fun _ => b) = PMF.pure b :=
    fun p b => PMF.map_const p b
  simp only [Nfa.Interface.answer, countNFA_val]
  unfold Nfa.Pseudocode.countNFA
  by_cases hne : Nfa.Pseudocode.nonemptySlice A n
  · have hacc : (Nfa.Program.acceptsAtLength A (Nfa.Program.unroll A n).val n).val = true :=
      (acceptsAtLength_iff A n).mpr hne
    simp only [hacc, if_true]
    rw [if_pos hne]
    simp only [Nfa.Analysis.scalarMedian_real_eq_medianOf]
    let Φ : ℕ → (Nfa.Model.Operations.Site Q → ℕ) → ℝ := fun j g =>
      Nfa.Interface.real (Nfa.Program.coreRun A σ P (Nfa.Model.Operations.Tape.ofFun g) n (Nfa.Program.unroll A n).val j).val
    let L : ℕ → List (Nfa.Model.Operations.Site Q) := fun j => ((Finset.univ : Finset Q).toList.flatMap fun q => (List.range P.α).flatMap fun r => (none :: (Finset.univ : Finset Q).toList.map some).flatMap fun src => (List.range' 1 n).flatMap fun ℓ => (Nfa.Run.words ℓ).map fun u => (⟨j, q, r, src, u⟩ : Nfa.Model.Operations.Site Q))
    have hsites : Nfa.Run.sites (Q := Q) n P = (List.range P.μ).flatMap L := rfl
    have hblocks := drawAll_blocks (fun _ => Nfa.Run.coinIndex) 0 (List.range P.μ) List.nodup_range L
      (fun r _ r' _ hrr' x hx hx' => hrr' (((mem_runBlock_iff P n r x).mp hx).1.symm.trans
        ((mem_runBlock_iff P n r' x).mp hx').1)) Φ
      (fun r g g' hgg => by
        simp only [Φ]
        rw [coreRun_local A σ P n r g g' (fun x h1 h2 h3 h4 => hgg x ((mem_runBlock_iff P n r x).mpr ⟨h1, h2, h3, h4⟩))])
      0
    have hlhs : (Nfa.Run.tapeLaw (Nfa.Run.sites (Q := Q) n P)).map (fun f =>
          Arlib.Probability.medianOf (fun b : Fin P.μ => Nfa.Interface.real (Nfa.Program.coreRun A σ P (Nfa.Model.Operations.Tape.ofFun f) n (Nfa.Program.unroll A n).val b).val))
        = ((Nfa.Pseudocode.drawAll (fun _ => Nfa.Run.coinIndex) 0 ((List.range P.μ).flatMap L)).map
            (fun g r => if r ∈ List.range P.μ then Φ r g else 0)).map
            (fun ests => Arlib.Probability.medianOf fun j : Fin P.μ => ests j) := by
      rw [PMF.map_comp, hsites, tapeLaw_eq_drawAll]
      refine congrArg₂ PMF.map ?_ rfl
      funext g
      simp only [Function.comp_apply, Φ]
      congr 1
      funext b
      rw [if_pos (List.mem_range.mpr b.2)]
    rw [hlhs, hblocks]
    congr 2
    funext j
    have hperm : ((Finset.univ : Finset Q).toList.flatMap fun q => (List.range P.α).flatMap fun r => (none :: (Finset.univ : Finset Q).toList.map some).flatMap fun src => (List.range' 1 n).flatMap fun ℓ => (Nfa.Run.words ℓ).map fun u => (⟨j, q, r, src, u⟩ : Nfa.Model.Operations.Site Q)).Perm ((List.range' 1 n).flatMap fun ℓ => (Finset.univ : Finset Q).toList.flatMap fun q => (List.range P.α).flatMap fun r => (none :: (Finset.univ : Finset Q).toList.map some).flatMap fun src => (Nfa.Run.words ℓ).map fun u => (⟨j, q, r, src, u⟩ : Nfa.Model.Operations.Site Q)) := by
      rw [List.perm_ext_iff_of_nodup (runBlock_nodup P n j) (runBlock'_nodup P n j)]
      intro x
      rw [mem_runBlock_iff, mem_runBlock'_iff]
    simp only [L, Φ]
    rw [drawAll_perm _ _ hperm (runBlock_nodup P n j), ← tapeLaw_eq_drawAll]
    exact coreRun_bridge A σ P n j
  · have hacc : ¬ (Nfa.Program.acceptsAtLength A (Nfa.Program.unroll A n).val n).val = true :=
      fun h => hne ((acceptsAtLength_iff A n).mp h)
    simp only [hacc, if_false, Bool.false_eq_true]
    rw [if_neg hne, hconst]
    simp [Nfa.Interface.real]

/-- Top rung: for every parameter block, the program `Nfa.Program.countNFA` has the pseudocode's output law, and so the measured output at (ε, δ) is exactly `Pseudocode.countOutput`. The analysis rewrites through the second conjunct. -/
theorem output_eq_countOutput {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (n : ℕ) (ε δ : ℝ) : (∀ (P : Nfa.Params), (Nfa.Run.tapeLaw (Nfa.Run.sites (Q := Q) n P)).map (fun f => Nfa.Interface.answer (Nfa.Program.countNFA A σ n P (Nfa.Model.Operations.Tape.ofFun f))) = Nfa.Pseudocode.countNFA A σ n P) ∧ Nfa.Run.output A σ n ε δ = Nfa.Pseudocode.countOutput A σ n ε δ := by
  refine ⟨fun P => countNFA_bridge A σ n P, ?_⟩
  rw [Nfa.Interface.output_eq, Nfa.Interface.run_eq, PMF.map_comp]
  exact countNFA_bridge A σ n (Nfa.params A n ε δ)

end Nfa

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r-coreRun · proved · `coreRun_bridge`, `runLayers_bridge`, `layerStep_bridge`, `countNFA_bridge`; file sorry-free. Two split-out child files (layer-step invariants, layer-step locality) were refused admission and folded back in here, since they need this file's `hatList` helpers. A whole-record unfold of `estimateAndSample` timed out in the kernel; generalising the ρ fold first (as `estimateAndSample_det` does) fixed it.
-/
