import Nfa.Analysis.FoldlSteps

/-!
# The cost and shape of `unroll`

`Nfa.Program.unroll A n` (countNFA.1) takes at most `2·n·m²` steps, `m = |Q|`: each
of its `n` rounds tests two labels for every (state, state of the last layer)
pair.  Its value holds at most `n + 1` layers, each a duplicate-free list of at
most `m` states (each is `[q_I]` or a sub-list of the `≺`-sorted state list).
-/

set_option autoImplicit false

namespace Nfa.Analysis

open Arlib.Computation (Charged)
open Nfa.Model.Operations

variable {Q : Type} [Fintype Q] [LinearOrder Q]

/-- INTERNAL: **`unroll` costs at most `2nm²` steps** and returns at most `n + 1` layers,
each duplicate-free of length at most `|Q|`.
TEXLINE: analysis.tex:40-55 -/
theorem unroll_cost (MM : ℕ → ℕ) (A : PaperNFA Q) (n : ℕ) :
    Charged.steps (rate MM (Fintype.card Q)) (Nfa.Program.unroll A n) ≤
      2 * n * Fintype.card Q ^ 2 ∧
    (Nfa.Program.unroll A n).val.size ≤ n + 1 ∧
    ∀ L ∈ (Nfa.Program.unroll A n).val.toList, L.Nodup ∧ L.length ≤ Fintype.card Q := by
  set m := Fintype.card Q
  have hm : 1 ≤ m := Fintype.card_pos_iff.2 ⟨A.qI⟩
  set states : List Q := (Finset.univ : Finset Q).sort (· ≤ ·) with hstates
  have hsn : states.Nodup := Finset.sort_nodup _ _
  have hsl : states.length = m := by simp [states, m]
  -- inner fold over states: value is a sublist of states, cost ≤ 2 * m * |last|
  have inner : ∀ (last : List Q) (l : List Q) (acc : List Q),
      Charged.steps (rate MM m) (Charged.foldl (fun (acc : List Q) (q : Q) => do
          let hit ← Charged.foldl (fun (hit : Bool) (q' : Q) =>
              Charged.foldl (fun (hit : Bool) (b : Bool) => do
                  let t ← transition A q' b q
                  pure (hit || t)) [false, true] hit) last false
          pure (if hit then acc ++ [q] else acc)) l acc) ≤ l.length * (2 * last.length) ∧
      ∃ l', l'.Sublist l ∧ (Charged.foldl (fun (acc : List Q) (q : Q) => do
          let hit ← Charged.foldl (fun (hit : Bool) (q' : Q) =>
              Charged.foldl (fun (hit : Bool) (b : Bool) => do
                  let t ← transition A q' b q
                  pure (hit || t)) [false, true] hit) last false
          pure (if hit then acc ++ [q] else acc)) l acc).val = acc ++ l' := by
    intro last l
    induction l with
    | nil => intro acc; exact ⟨by simp, [], by simp⟩
    | cons q l ih =>
        intro acc
        rw [steps_foldl_cons, Charged.steps_bind, Charged.steps_pure, Charged.val_foldl_cons]
        simp only [Charged.val_bind, Charged.val_pure]
        set hit := (Charged.foldl (fun (hit : Bool) (q' : Q) =>
              Charged.foldl (fun (hit : Bool) (b : Bool) => do
                  let t ← transition A q' b q
                  pure (hit || t)) [false, true] hit) last false : Charged Op Cell Bool)
        have hhit : Charged.steps (rate MM m) hit ≤ last.length * 2 := by
          refine (steps_foldl_le_sum (rate MM m) _ (fun _ => 2) last ?_ false).trans
            (by simp)
          intro b a _
          refine (steps_foldl_le_sum (rate MM m) _ (fun _ => 1) [false, true] ?_ b).trans
            (by simp)
          intro b' a' _
          simp [transition]
        obtain ⟨h1, l', hl', hv⟩ := ih (if hit.val then acc ++ [q] else acc)
        refine ⟨?_, ?_⟩
        · simp only [List.length_cons]; nlinarith
        · by_cases hh : hit.val
          · refine ⟨q :: l', hl'.cons_cons q, ?_⟩
            rw [hv]; simp [hh]
          · refine ⟨l', hl'.cons q, ?_⟩
            rw [hv]; simp [hh]
  have outer := foldl_inv_le (rate MM m) (fun (layers : Array (List Q)) (_ : ℕ) => do
      let last := layers.back?.getD []
      let next ← Charged.foldl (fun (acc : List Q) (q : Q) => do
          let hit ← Charged.foldl (fun (hit : Bool) (q' : Q) =>
              Charged.foldl (fun (hit : Bool) (b : Bool) => do
                  let t ← transition A q' b q
                  pure (hit || t)) [false, true] hit) last false
          pure (if hit then acc ++ [q] else acc)) states []
      pure (layers.push next))
    (fun layers => ∀ L ∈ layers.toList, L.Nodup ∧ L.length ≤ m) (fun layers => layers.size)
    (fun _ => 2 * m ^ 2) (fun _ => 1) (List.range n) ?_ #[[A.qI]] ?_
  · obtain ⟨hI, hk, hg⟩ := outer
    refine ⟨?_, ?_, hI⟩
    · simpa [Nfa.Program.unroll, mul_comm, mul_assoc] using hk
    · simpa [Nfa.Program.unroll, add_comm] using hg
  · intro layers _ _ hI
    have hlast : (layers.back?.getD []).length ≤ m := by
      cases h : layers.back? with
      | none => simp
      | some L =>
          have : L ∈ layers.toList := by
            rw [Array.back?_eq_some_iff] at h
            obtain ⟨ys, rfl⟩ := h
            simp
          simpa using (hI L this).2
    obtain ⟨hc, l', hl', hv⟩ := inner (layers.back?.getD []) states []
    refine ⟨?_, ?_, ?_⟩
    · simp only [Charged.val_bind, Charged.val_pure, hv, List.nil_append]
      intro L hL
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hL
      rcases hL with hL | rfl
      · exact hI L hL
      · exact ⟨hl'.nodup hsn, hl'.length_le.trans hsl.le⟩
    · simp only [Charged.steps_bind, Charged.steps_pure, add_zero]
      refine hc.trans ?_
      rw [hsl]; nlinarith
    · simp
  · intro L hL
    simp only [List.mem_singleton] at hL
    subst hL
    simpa using hm

end Nfa.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `unroll_cost`; size clause weakened from `= n + 1` to `≤ n + 1` (all that `coreRun_cost` uses)
-/
