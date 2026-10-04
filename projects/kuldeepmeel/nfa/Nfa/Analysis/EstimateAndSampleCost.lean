import Nfa.Analysis.FoldlSteps
import Nfa.Interface.Encoding

/-!
# The cost of one `estimateAndSample` call

One call of `Nfa.Program.estimateAndSample` (algorithm.tex:64-84) for a state `q`
with previous layer `prev` takes at most
`4|prev| + 14·Σ_{q' ∈ prev} |S(q')| + 3γ(β+1) + 2α + 12` steps in the currency
`rate MM m`: the predecessor scan, `ρ` and the ratios are linear in `|prev|`; the
normalize/union loop (eAS.2-3) reads every stored sample of every predecessor at
most once per label (two labels), at five unit operations per (word, label); the
block means are `γ(2β+1)` steps and their median `γ`; the final reduce (eAS.8)
reads each word of `hat S` once, and `|hat S| ≤ 2·Σ_{q' ∈ prev} |S(q')|`.  No
`witnessProduct` is performed, so the bound does not depend on `MM`.

It also records what the call does to the core state: it overwrites `p(q)`,
`S(q)` and the running total, adding exactly `|S(q)|` (summed over `r`) to the
total, and leaves every other field — in particular `prevS`, the cache and the
interrupt flag — untouched.
-/

set_option autoImplicit false

namespace Nfa.Analysis

open Arlib.Computation (Charged Roster)
open Nfa.Model.Operations

variable {Q : Type} [Fintype Q] [LinearOrder Q]

omit [LinearOrder Q] in
/-- INTERNAL: **the predecessor scan** costs two `Δ` lookups per state of the
previous layer; each predecessor carries at most two labels, and the predecessors
are drawn from `prev` without repetition beyond `prev`'s own, so any measure summed
over them is at most its sum over `prev`.
TEXLINE: algorithm.tex:64-84 -/
theorem predecessors_cost (MM : ℕ → ℕ) (A : PaperNFA Q) (prev : List Q) (q : Q)
    (h : Q → ℕ) :
    Charged.steps (rate MM (Fintype.card Q)) (Nfa.Program.predecessors A prev q) ≤
      2 * prev.length ∧
    (∀ e ∈ (Nfa.Program.predecessors A prev q).val, e.2.length ≤ 2) ∧
    ((Nfa.Program.predecessors A prev q).val.map fun e => h e.1).sum ≤
      (prev.map h).sum ∧
    (Nfa.Program.predecessors A prev q).val.length ≤ prev.length := by
  have hlab : ∀ q' : Q,
      Charged.steps (rate MM (Fintype.card Q)) (Charged.foldl (fun (ls : List Bool) (b : Bool) => do
          let t ← transition A q' b q
          pure (if t then ls ++ [b] else ls)) [false, true] []) ≤ 2 ∧
      (Charged.foldl (fun (ls : List Bool) (b : Bool) => do
          let t ← transition A q' b q
          pure (if t then ls ++ [b] else ls)) [false, true] []).val.length ≤ 2 := by
    intro q'
    have := foldl_inv_le (rate MM (Fintype.card Q)) (fun (ls : List Bool) (b : Bool) => do
          let t ← transition A q' b q
          pure (if t then ls ++ [b] else ls)) (fun _ => True) List.length (fun _ => 1)
          (fun _ => 1) [false, true] (by
            intro ls b _ _
            refine ⟨trivial, by simp [transition], ?_⟩
            simp only [Charged.val_bind, Charged.val_pure]
            split <;> simp) [] trivial
    simpa using And.intro this.2.1 this.2.2
  have key := fun (I : List (Q × List Bool) → Prop) (Φ : List (Q × List Bool) → ℕ) (g : Q → ℕ) =>
    foldl_inv_le (rate MM (Fintype.card Q)) (fun (acc : List (Q × List Bool)) (q' : Q) => do
      let labels ← Charged.foldl (fun (ls : List Bool) (b : Bool) => do
          let t ← transition A q' b q
          pure (if t then ls ++ [b] else ls)) [false, true] []
      pure (if labels.isEmpty then acc else acc ++ [(q', labels)])) I Φ (fun _ => 2) g prev
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := (key (fun _ => True) (fun _ => 0) (fun _ => 0) (by
      intro acc q' _ _
      refine ⟨trivial, ?_, by simp⟩
      simpa using (hlab q').1) [] trivial).2.1
    simpa [Nfa.Program.predecessors, mul_comm] using this
  · have := (key (fun acc => ∀ e ∈ acc, e.2.length ≤ 2) (fun _ => 0) (fun _ => 0) (by
      intro acc q' _ hacc
      refine ⟨?_, by simpa using (hlab q').1, by simp⟩
      simp only [Charged.val_bind, Charged.val_pure]
      split
      · exact hacc
      · intro e he
        simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact hacc e he
        · exact (hlab q').2) [] (by simp)).1
    simpa [Nfa.Program.predecessors] using this
  · have := (key (fun _ => True) (fun acc => (acc.map fun e => h e.1).sum) h (by
      intro acc q' _ _
      refine ⟨trivial, by simpa using (hlab q').1, ?_⟩
      simp only [Charged.val_bind, Charged.val_pure]
      split <;> simp) [] trivial).2.2
    simpa [Nfa.Program.predecessors] using this
  · have := (key (fun _ => True) List.length (fun _ => 1) (by
      intro acc q' _ _
      refine ⟨trivial, by simpa using (hlab q').1, ?_⟩
      simp only [Charged.val_bind, Charged.val_pure]
      split <;> simp) [] trivial).2.2
    simpa [Nfa.Program.predecessors] using this

/-- INTERNAL: two finite sums of naturals may be taken in either order.
TEXLINE: analysis.tex:40-55 -/
theorem list_sum_swap {α β : Type} (L1 : List α) (L2 : List β) (f : α → β → ℕ) :
    (L1.map fun a => (L2.map fun b => f a b).sum).sum =
      (L2.map fun b => (L1.map fun a => f a b).sum).sum := by
  induction L1 with
  | nil => simp
  | cons a l ih => simp [ih, List.sum_map_add]

/-- INTERNAL: reading the first `k` indices of a sample array visits at most
`samplesSize` words (the `List.range` form of `sum_getD_length_le`).
TEXLINE: analysis.tex:40-55 -/
theorem range_getD_le (X : Nfa.Program.Samples) (k : ℕ) :
    ((List.range k).map fun r => (X.getD r []).length).sum ≤ samplesSize X := by
  have := sum_getD_length_le X k
  have e : ((List.range k).map fun r => (X.getD r []).length).sum =
      ∑ r ∈ Finset.range k, (X.getD r []).length := by
    simp [Finset.sum, Finset.range, Multiset.range]
  omega

omit [Fintype Q] [LinearOrder Q] in
/-- INTERNAL: **the ratios `ρ/p(q_i)`** (eAS.2): one division per predecessor; the
labels are carried over, and any measure of the predecessors is not increased.
TEXLINE: algorithm.tex:64-84 -/
theorem normalized_cost (MM : ℕ → ℕ) (m : ℕ) (s : Nfa.Program.CoreState Q) (ρ : Scalar)
    (preds : List (Q × List Bool)) (h : Q → ℕ) (hp : ∀ e ∈ preds, e.2.length ≤ 2) :
    Charged.steps (rate MM m) (Charged.foldl
      (fun (acc : List (Q × List Bool × Scalar)) (e : Q × List Bool) => do
        let ratio ← Scalar.div ρ (s.prevP e.1)
        pure (acc ++ [(e.1, e.2, ratio)])) preds []) ≤ preds.length ∧
    (∀ e ∈ (Charged.foldl
      (fun (acc : List (Q × List Bool × Scalar)) (e : Q × List Bool) => do
        let ratio ← Scalar.div ρ (s.prevP e.1)
        pure (acc ++ [(e.1, e.2, ratio)])) preds []).val, e.2.1.length ≤ 2) ∧
    ((Charged.foldl
      (fun (acc : List (Q × List Bool × Scalar)) (e : Q × List Bool) => do
        let ratio ← Scalar.div ρ (s.prevP e.1)
        pure (acc ++ [(e.1, e.2, ratio)])) preds []).val.map fun e => h e.1).sum ≤
      (preds.map fun e => h e.1).sum := by
  have key := foldl_inv_le (rate MM m)
    (fun (acc : List (Q × List Bool × Scalar)) (e : Q × List Bool) => do
        let ratio ← Scalar.div ρ (s.prevP e.1)
        pure (acc ++ [(e.1, e.2, ratio)]))
    (fun acc => ∀ e ∈ acc, e.2.1.length ≤ 2) (fun acc => (acc.map fun e => h e.1).sum)
    (fun _ => 1) (fun e => h e.1) preds (by
      intro acc e he hacc
      refine ⟨?_, by simp [Scalar.div], by simp⟩
      intro e' he'
      simp only [Charged.val_bind, Charged.val_pure, List.mem_append, List.mem_singleton] at he'
      rcases he' with he' | rfl
      · exact hacc e' he'
      · exact hp e he) [] (by simp)
  obtain ⟨h1, h2, h3⟩ := key
  exact ⟨by simpa using h2, h1, by simpa using h3⟩


omit [Fintype Q] in
/-- INTERNAL: **normalize and union** (eAS.2-3): for each `r ∈ [α]`, at most five unit
operations per (stored word of a predecessor, label), so at most `10` per stored
word; and `hat S` holds at most two words per stored word.
TEXLINE: algorithm.tex:64-84 -/
theorem hatS_cost (MM : ℕ → ℕ) (m : ℕ) (A : PaperNFA Q) (σ : Selector A) (tape : Tape Q)
    (j : ℕ) (q : Q) (s : Nfa.Program.CoreState Q) (α : ℕ)
    (N : List (Q × List Bool × Scalar)) (hN : ∀ e ∈ N, e.2.1.length ≤ 2) :
    let F := Charged.foldl (fun (acc : Nfa.Program.Samples) (r : ℕ) => do
      let T ← Charged.foldl (fun (T : List (List Bool)) (e : Q × List Bool × Scalar) =>
          Charged.foldl (fun (T : List (List Bool)) (w : List Bool) =>
              Charged.foldl (fun (T : List (List Bool)) (b : Bool) => do
                  let u ← extend w b
                  let kept ← coin ⟨j, q, r, some e.1, u⟩ e.2.2 tape
                  if kept then do
                    let chosen ← isWitness σ s.cache q w b e.1
                    if chosen then addWord u T else pure T
                  else pure T) e.2.1 T)
            ((s.prevS e.1).getD r []) T) N []
      pure (acc.push T)) (List.range α) #[]
    Charged.steps (rate MM m) F ≤ 10 * (N.map fun e => samplesSize (s.prevS e.1)).sum ∧
      samplesSize F.val ≤ 2 * (N.map fun e => samplesSize (s.prevS e.1)).sum := by
  intro F
  -- one (word, label)
  have hbody : ∀ (r : ℕ) (e : Q × List Bool × Scalar) (w : List Bool) (T : List (List Bool))
      (b : Bool),
      Charged.steps (rate MM m) (do
                  let u ← extend w b
                  let kept ← coin ⟨j, q, r, some e.1, u⟩ e.2.2 tape
                  if kept then do
                    let chosen ← isWitness σ s.cache q w b e.1
                    if chosen then addWord u T else pure T
                  else pure T : Charged Op Cell (List (List Bool))) ≤ 5 ∧
      (do
                  let u ← extend w b
                  let kept ← coin ⟨j, q, r, some e.1, u⟩ e.2.2 tape
                  if kept then do
                    let chosen ← isWitness σ s.cache q w b e.1
                    if chosen then addWord u T else pure T
                  else pure T : Charged Op Cell (List (List Bool))).val.length ≤ T.length + 1 := by
    intro r e w T b
    have hw : Charged.steps (rate MM m) (isWitness σ s.cache q w b e.1) ≤ 2 := by
      unfold isWitness
      simp only [Charged.steps_bind]
      have : Charged.steps (rate MM m) (Roster.mem w s.cache : Charged Op Cell Bool) = 1 := by
        simp [Charged.steps, Roster.cost_mem]
      rw [this]
      split <;> simp
    have hc : ∀ (site : Site Q) (p : Scalar),
        Charged.steps (rate MM m) (coin site p tape) = 1 := by
      intro site p; simp [coin]
    have he : Charged.steps (rate MM m) (extend w b) = 1 := by simp [extend]
    simp only [Charged.steps_bind, Charged.val_bind, hc, he]
    split
    · simp only [Charged.steps_bind, Charged.val_bind]
      split
      · simp [addWord]; omega
      · simp; omega
    · simp
  -- the labels of one word
  have hb : ∀ (r : ℕ) (e : Q × List Bool × Scalar), e ∈ N → ∀ (w : List Bool) (T : List (List Bool)),
      Charged.steps (rate MM m) (Charged.foldl (fun (T : List (List Bool)) (b : Bool) => do
                  let u ← extend w b
                  let kept ← coin ⟨j, q, r, some e.1, u⟩ e.2.2 tape
                  if kept then do
                    let chosen ← isWitness σ s.cache q w b e.1
                    if chosen then addWord u T else pure T
                  else pure T) e.2.1 T) ≤ 10 ∧
      (Charged.foldl (fun (T : List (List Bool)) (b : Bool) => do
                  let u ← extend w b
                  let kept ← coin ⟨j, q, r, some e.1, u⟩ e.2.2 tape
                  if kept then do
                    let chosen ← isWitness σ s.cache q w b e.1
                    if chosen then addWord u T else pure T
                  else pure T) e.2.1 T).val.length ≤ T.length + 2 := by
    intro r e he w T
    have := foldl_inv_le (rate MM m) _ (fun _ => True) List.length (fun _ => 5) (fun _ => 1) e.2.1
      (fun T b _ _ => ⟨trivial, (hbody r e w T b).1, (hbody r e w T b).2⟩) T trivial
    simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_one] at this
    have h2 := hN e he
    exact ⟨by nlinarith [this.2.1], by omega⟩
  -- the words of one predecessor
  have hw : ∀ (r : ℕ) (e : Q × List Bool × Scalar), e ∈ N → ∀ (T : List (List Bool)),
      Charged.steps (rate MM m) (Charged.foldl (fun (T : List (List Bool)) (w : List Bool) =>
              Charged.foldl (fun (T : List (List Bool)) (b : Bool) => do
                  let u ← extend w b
                  let kept ← coin ⟨j, q, r, some e.1, u⟩ e.2.2 tape
                  if kept then do
                    let chosen ← isWitness σ s.cache q w b e.1
                    if chosen then addWord u T else pure T
                  else pure T) e.2.1 T)
            ((s.prevS e.1).getD r []) T) ≤ 10 * ((s.prevS e.1).getD r []).length ∧
      (Charged.foldl (fun (T : List (List Bool)) (w : List Bool) =>
              Charged.foldl (fun (T : List (List Bool)) (b : Bool) => do
                  let u ← extend w b
                  let kept ← coin ⟨j, q, r, some e.1, u⟩ e.2.2 tape
                  if kept then do
                    let chosen ← isWitness σ s.cache q w b e.1
                    if chosen then addWord u T else pure T
                  else pure T) e.2.1 T)
            ((s.prevS e.1).getD r []) T).val.length ≤
        T.length + 2 * ((s.prevS e.1).getD r []).length := by
    intro r e he T
    have := foldl_inv_le (rate MM m) _ (fun _ => True) List.length (fun _ => 10) (fun _ => 2)
      ((s.prevS e.1).getD r [])
      (fun T w _ _ => ⟨trivial, (hb r e he w T).1, (hb r e he w T).2⟩) T trivial
    simp only [List.map_const', List.sum_replicate, smul_eq_mul] at this
    exact ⟨by rw [mul_comm]; exact this.2.1, by rw [mul_comm 2]; exact this.2.2⟩
  -- one repetition
  have hr : ∀ (r : ℕ),
      Charged.steps (rate MM m) (Charged.foldl (fun (T : List (List Bool)) (e : Q × List Bool × Scalar) =>
          Charged.foldl (fun (T : List (List Bool)) (w : List Bool) =>
              Charged.foldl (fun (T : List (List Bool)) (b : Bool) => do
                  let u ← extend w b
                  let kept ← coin ⟨j, q, r, some e.1, u⟩ e.2.2 tape
                  if kept then do
                    let chosen ← isWitness σ s.cache q w b e.1
                    if chosen then addWord u T else pure T
                  else pure T) e.2.1 T)
            ((s.prevS e.1).getD r []) T) N []) ≤
        10 * (N.map fun e => ((s.prevS e.1).getD r []).length).sum ∧
      (Charged.foldl (fun (T : List (List Bool)) (e : Q × List Bool × Scalar) =>
          Charged.foldl (fun (T : List (List Bool)) (w : List Bool) =>
              Charged.foldl (fun (T : List (List Bool)) (b : Bool) => do
                  let u ← extend w b
                  let kept ← coin ⟨j, q, r, some e.1, u⟩ e.2.2 tape
                  if kept then do
                    let chosen ← isWitness σ s.cache q w b e.1
                    if chosen then addWord u T else pure T
                  else pure T) e.2.1 T)
            ((s.prevS e.1).getD r []) T) N []).val.length ≤
        2 * (N.map fun e => ((s.prevS e.1).getD r []).length).sum := by
    intro r
    have := foldl_inv_le (rate MM m) _ (fun _ => True) List.length
      (fun e => 10 * ((s.prevS e.1).getD r []).length)
      (fun e => 2 * ((s.prevS e.1).getD r []).length) N
      (fun T e he _ => ⟨trivial, (hw r e he T).1, (hw r e he T).2⟩) [] trivial
    rw [List.sum_map_mul_left, List.sum_map_mul_left] at this
    simpa using And.intro this.2.1 this.2.2
  have hall := foldl_inv_le (rate MM m) (fun (acc : Nfa.Program.Samples) (r : ℕ) => do
      let T ← Charged.foldl (fun (T : List (List Bool)) (e : Q × List Bool × Scalar) =>
          Charged.foldl (fun (T : List (List Bool)) (w : List Bool) =>
              Charged.foldl (fun (T : List (List Bool)) (b : Bool) => do
                  let u ← extend w b
                  let kept ← coin ⟨j, q, r, some e.1, u⟩ e.2.2 tape
                  if kept then do
                    let chosen ← isWitness σ s.cache q w b e.1
                    if chosen then addWord u T else pure T
                  else pure T) e.2.1 T)
            ((s.prevS e.1).getD r []) T) N []
      pure (acc.push T)) (fun _ => True) samplesSize
      (fun r => 10 * (N.map fun e => ((s.prevS e.1).getD r []).length).sum)
      (fun r => 2 * (N.map fun e => ((s.prevS e.1).getD r []).length).sum) (List.range α)
      (by
        intro acc r _ _
        refine ⟨trivial, ?_, ?_⟩
        · simpa using (hr r).1
        · simp only [Charged.val_bind, Charged.val_pure, samplesSize_push]
          have := (hr r).2
          omega) #[] trivial
  obtain ⟨-, h1, h2⟩ := hall
  rw [List.sum_map_mul_left, list_sum_swap] at h1 h2
  have hsw : ((N.map fun e => ((List.range α).map fun r => ((s.prevS e.1).getD r []).length).sum)).sum
      ≤ (N.map fun e => samplesSize (s.prevS e.1)).sum :=
    List.sum_le_sum (fun e _ => range_getD_le _ _)
  refine ⟨h1.trans (by omega), ?_⟩
  simp only [samplesSize_empty, zero_add] at h2
  exact h2.trans (by omega)

omit [Fintype Q] [LinearOrder Q] in
/-- INTERNAL: **the block means** (eAS.4): `γ` means of `β` sizes each, `γ(2β+1)`
steps, and `γ` values.
TEXLINE: algorithm.tex:64-84 -/
theorem Ys_cost (MM : ℕ → ℕ) (m : ℕ) (P : Params) (hatS : Nfa.Program.Samples)
    (zero βρ : Scalar) :
    Charged.steps (rate MM m) (Charged.foldl (fun (Ys : List Scalar) (b : ℕ) => do
      let sum ← Charged.foldl (fun (acc : Scalar) (r : ℕ) => do
          let c ← size (hatS.getD (P.β * b + r) [])
          Scalar.add acc c) (List.range P.β) zero
      let y ← Scalar.div sum βρ
      pure (Ys ++ [y])) (List.range P.γ) []) ≤ P.γ * (2 * P.β + 1) ∧
    (Charged.foldl (fun (Ys : List Scalar) (b : ℕ) => do
      let sum ← Charged.foldl (fun (acc : Scalar) (r : ℕ) => do
          let c ← size (hatS.getD (P.β * b + r) [])
          Scalar.add acc c) (List.range P.β) zero
      let y ← Scalar.div sum βρ
      pure (Ys ++ [y])) (List.range P.γ) []).val.length ≤ P.γ := by
  have hin : ∀ b : ℕ, Charged.steps (rate MM m) (Charged.foldl (fun (acc : Scalar) (r : ℕ) => do
          let c ← size (hatS.getD (P.β * b + r) [])
          Scalar.add acc c) (List.range P.β) zero) ≤ P.β * 2 := by
    intro b
    refine (Charged.steps_foldl_le (k := 2) (rate MM m) ?_ _ _).trans (by simp)
    intro acc r
    simp [size, Scalar.add]
  have := foldl_inv_le (rate MM m) (fun (Ys : List Scalar) (b : ℕ) => do
      let sum ← Charged.foldl (fun (acc : Scalar) (r : ℕ) => do
          let c ← size (hatS.getD (P.β * b + r) [])
          Scalar.add acc c) (List.range P.β) zero
      let y ← Scalar.div sum βρ
      pure (Ys ++ [y])) (fun _ => True) List.length (fun _ => 2 * P.β + 1) (fun _ => 1)
    (List.range P.γ) (by
      intro Ys b _ _
      refine ⟨trivial, ?_, by simp⟩
      simp only [Charged.steps_bind, Charged.steps_pure, add_zero]
      have := hin b
      have h2 : ∀ x : Scalar, Charged.steps (rate MM m) (Scalar.div x βρ) = 1 := by
        intro x; simp [Scalar.div]
      rw [h2]; omega) [] trivial
  simp only [List.map_const', List.length_range, List.sum_replicate, smul_eq_mul, mul_one,
    List.length_nil, zero_add] at this
  exact ⟨this.2.1, this.2.2⟩

omit [Fintype Q] [LinearOrder Q] in
/-- INTERNAL: **the final reduce** (eAS.8): two steps per word of `hat S` and two per
repetition; the total it returns is the starting total plus every word it keeps.
TEXLINE: algorithm.tex:64-84 -/
theorem out_cost (MM : ℕ → ℕ) (m : ℕ) (j : ℕ) (q : Q) (tape : Tape Q) (α : ℕ)
    (hatS : Nfa.Program.Samples) (ratio total : Scalar) :
    Charged.steps (rate MM m) (Charged.foldl (fun (acc : Nfa.Program.Samples × Scalar) (r : ℕ) => do
      let T ← Charged.foldl (fun (T : List (List Bool)) (u : List Bool) => do
          let kept ← coin ⟨j, q, r, none, u⟩ ratio tape
          if kept then addWord u T else pure T) (hatS.getD r []) []
      let c ← size T
      let tot ← Scalar.add acc.2 c
      pure (acc.1.push T, tot)) (List.range α) (#[], total)) ≤ 2 * samplesSize hatS + 2 * α ∧
    (Charged.foldl (fun (acc : Nfa.Program.Samples × Scalar) (r : ℕ) => do
      let T ← Charged.foldl (fun (T : List (List Bool)) (u : List Bool) => do
          let kept ← coin ⟨j, q, r, none, u⟩ ratio tape
          if kept then addWord u T else pure T) (hatS.getD r []) []
      let c ← size T
      let tot ← Scalar.add acc.2 c
      pure (acc.1.push T, tot)) (List.range α) (#[], total)).val.2.get =
      total.get + (samplesSize (Charged.foldl (fun (acc : Nfa.Program.Samples × Scalar) (r : ℕ) => do
      let T ← Charged.foldl (fun (T : List (List Bool)) (u : List Bool) => do
          let kept ← coin ⟨j, q, r, none, u⟩ ratio tape
          if kept then addWord u T else pure T) (hatS.getD r []) []
      let c ← size T
      let tot ← Scalar.add acc.2 c
      pure (acc.1.push T, tot)) (List.range α) (#[], total)).val.1 : ℚ) := by
  have hT : ∀ r : ℕ, Charged.steps (rate MM m) (Charged.foldl (fun (T : List (List Bool)) (u : List Bool) => do
          let kept ← coin ⟨j, q, r, none, u⟩ ratio tape
          if kept then addWord u T else pure T) (hatS.getD r []) []) ≤ (hatS.getD r []).length * 2 := by
    intro r
    refine Charged.steps_foldl_le (rate MM m) ?_ _ _
    intro T u
    have hc : ∀ (site : Site Q) (p : Scalar),
        Charged.steps (rate MM m) (coin site p tape) = 1 := by
      intro site p; simp [coin]
    simp only [Charged.steps_bind, hc]
    split <;> simp [addWord]
  have := foldl_inv_le (rate MM m) (fun (acc : Nfa.Program.Samples × Scalar) (r : ℕ) => do
      let T ← Charged.foldl (fun (T : List (List Bool)) (u : List Bool) => do
          let kept ← coin ⟨j, q, r, none, u⟩ ratio tape
          if kept then addWord u T else pure T) (hatS.getD r []) []
      let c ← size T
      let tot ← Scalar.add acc.2 c
      pure (acc.1.push T, tot))
    (fun acc => acc.2.get = total.get + (samplesSize acc.1 : ℚ)) (fun _ => 0)
    (fun r => 2 * (hatS.getD r []).length + 2) (fun _ => 0) (List.range α) (by
      intro acc r _ hacc
      refine ⟨?_, ?_, by simp⟩
      · simp only [Charged.val_bind, Charged.val_pure, Nfa.Interface.get_val_add,
          Nfa.Interface.get_val_size, samplesSize_push, hacc]
        push_cast; ring
      · simp only [Charged.steps_bind, Charged.steps_pure, add_zero]
        have := hT r
        have h1 : ∀ T, Charged.steps (rate MM m) (size T) = 1 := by intro T; simp [size]
        have h2 : ∀ x y : Scalar, Charged.steps (rate MM m) (Scalar.add x y) = 1 := by
          intro x y; simp [Scalar.add]
        rw [h1, h2]; omega) (#[], total) (by simp)
  obtain ⟨hI, hk, -⟩ := this
  refine ⟨hk.trans ?_, hI⟩
  rw [List.sum_map_add, List.sum_map_mul_left]
  have := range_getD_le hatS α
  simp only [List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  omega

-- The branch-uniform `simp only` lists below serve all four branches of the call
-- (empty / non-empty predecessor list × zero / non-zero median); not every lemma
-- fires in every branch.
set_option linter.unusedSimpArgs false in
/-- INTERNAL: **the cost of one `estimateAndSample` call**, and its effect on the
core state.  The cost is linear in the size of the previous layer, in the number of
samples stored for it, and in the parameters `α`, `β`, `γ`; the call writes `p(q)`,
`S(q)` and the total, the total growing by exactly `samplesSize S(q)`.
TEXLINE: analysis.tex:40-55 -/
theorem estimateAndSample_cost (MM : ℕ → ℕ) (A : PaperNFA Q) (σ : Selector A)
    (P : Params) (tape : Tape Q) (j : ℕ) (prev : List Q) (one zero : Scalar)
    (s : Nfa.Program.CoreState Q) (q : Q) :
    Charged.steps (rate MM (Fintype.card Q))
        (Nfa.Program.estimateAndSample A σ P tape j prev one zero s q) ≤
      4 * prev.length + 14 * (prev.map fun q' => samplesSize (s.prevS q')).sum +
        3 * P.γ * (P.β + 1) + 2 * P.α + 12 ∧
    ∃ (p : Scalar) (X : Nfa.Program.Samples) (tot : Scalar),
      (Nfa.Program.estimateAndSample A σ P tape j prev one zero s q).val =
        { s with curP := Function.update s.curP q p, curS := Function.update s.curS q X,
                 total := tot } ∧
      tot.get = s.total.get + (samplesSize X : ℚ) := by
  refine ⟨?_, ?_⟩
  · set m := Fintype.card Q
    obtain ⟨hp1, hp2, hp3, hp4⟩ := predecessors_cost MM A prev q (fun q' => samplesSize (s.prevS q'))
    unfold Nfa.Program.estimateAndSample
    simp only [Charged.steps_bind, Charged.steps_pure]
    generalize (Nfa.Program.predecessors A prev q).val = preds at hp2 hp3 hp4 ⊢
    have hγβ : P.γ * (2 * P.β + 1) + P.γ ≤ 3 * P.γ * (P.β + 1) := by nlinarith
    have hlit : ∀ a : ℚ, Charged.steps (rate MM m) (Scalar.lit a) = 1 := by
      intro a; simp [Scalar.lit]
    have hmul : ∀ x y : Scalar, Charged.steps (rate MM m) (Scalar.mul x y) = 1 := by
      intro x y; simp [Scalar.mul]
    have hdiv : ∀ x y : Scalar, Charged.steps (rate MM m) (Scalar.div x y) = 1 := by
      intro x y; simp [Scalar.div]
    have hmin : ∀ x y : Scalar, Charged.steps (rate MM m) (Scalar.min x y) = 1 := by
      intro x y; simp [Scalar.min]
    have hle : ∀ x y : Scalar, Charged.steps (rate MM m) (Scalar.le x y) = 1 := by
      intro x y; simp [Scalar.le]
    have hmed : ∀ xs : List Scalar, Charged.steps (rate MM m) (Scalar.median xs) ≤ xs.length := by
      intro xs
      unfold Scalar.median
      simp only [Charged.steps_bind, Charged.steps_pure, add_zero]
      refine (steps_foldl_le_sum (rate MM m) _ (fun _ => 1) xs ?_ ()).trans (by simp)
      intro b a _; simp
    have hrho : ∀ (L : List (Q × List Bool)) (x : Scalar), Charged.steps (rate MM m)
        (Charged.foldl (fun (m : Scalar) (e : Q × List Bool) => Scalar.min m (s.prevP e.1)) L x) ≤
          L.length := by
      intro L x
      refine (Charged.steps_foldl_le (k := 1) (rate MM m) ?_ L x).trans (by simp)
      intro b a; simp [Scalar.min]
    split
    · rw [Charged.steps_bind, Charged.steps_pure, zero_add, Charged.val_pure]
      have hN := normalized_cost MM m s one _ (fun q' => samplesSize (s.prevS q')) hp2
      generalize (Charged.foldl _ ([] : List (Q × List Bool)) ([] : List (Q × List Bool × Scalar))) = NN
        at hN ⊢
      obtain ⟨hN1, hN2, hN3⟩ := hN
      simp only [Charged.steps_bind, Charged.steps_pure, Charged.val_pure, hlit, hmul, hdiv, hmin,
        hle, add_zero, zero_add]
      generalize hG : (Charged.foldl (κ := Op) (κₛ := Cell) (β := Nfa.Program.Samples) _
        (List.range P.α) _) = HH
      have hH : Charged.steps (rate MM m) HH ≤
            10 * (NN.val.map fun e => samplesSize (s.prevS e.1)).sum ∧
          samplesSize HH.val ≤ 2 * (NN.val.map fun e => samplesSize (s.prevS e.1)).sum := by
        rw [← hG]; exact hatS_cost MM m A σ tape j q s P.α _ hN2
      generalize hGY : (Charged.foldl (κ := Op) (κₛ := Cell) (β := List Scalar) _
        (List.range P.γ) _) = YY
      have hY : Charged.steps (rate MM m) YY ≤ P.γ * (2 * P.β + 1) ∧ YY.val.length ≤ P.γ := by
        rw [← hGY]; exact Ys_cost MM m P HH.val zero _
      have hmd := hmed YY.val
      generalize (Scalar.median YY.val) = MD at hmd ⊢
      split
      all_goals
        simp only [Charged.steps_bind, Charged.steps_pure, Charged.val_pure, hlit, hmul, hdiv, hmin,
          hle, add_zero, zero_add]
        generalize hGO : (Charged.foldl (κ := Op) (κₛ := Cell)
          (β := Nfa.Program.Samples × Scalar) _ (List.range P.α) _) = OO
        have hO : Charged.steps (rate MM m) OO ≤ 2 * samplesSize HH.val + 2 * P.α := by
          rw [← hGO]; exact (out_cost MM m j q tape P.α HH.val _ s.total).1
        have hp1' : Charged.steps (rate MM m) (Nfa.Program.predecessors A prev q) ≤
            2 * prev.length := hp1
        have hsum := hN3.trans hp3
        generalize P.γ * (2 * P.β + 1) = g1 at hY hγβ
        generalize 3 * P.γ * (P.β + 1) = g2 at hγβ ⊢
        omega
    · rename_i q₁ snd rest
      rw [Charged.steps_bind]
      have hr := hrho rest (s.prevP q₁)
      generalize (Charged.foldl (fun (m : Scalar) (e : Q × List Bool) => Scalar.min m (s.prevP e.1))
        rest (s.prevP q₁)) = R at hr ⊢
      generalize R.val = ρ
      have hN := normalized_cost MM m s ρ _ (fun q' => samplesSize (s.prevS q')) hp2
      generalize (Charged.foldl _ ((q₁, snd) :: rest) ([] : List (Q × List Bool × Scalar))) = NN
        at hN ⊢
      obtain ⟨hN1, hN2, hN3⟩ := hN
      simp only [Charged.steps_bind, Charged.steps_pure, Charged.val_pure, hlit, hmul, hdiv, hmin,
        hle, add_zero, zero_add]
      generalize hG : (Charged.foldl (κ := Op) (κₛ := Cell) (β := Nfa.Program.Samples) _
        (List.range P.α) _) = HH
      have hH : Charged.steps (rate MM m) HH ≤
            10 * (NN.val.map fun e => samplesSize (s.prevS e.1)).sum ∧
          samplesSize HH.val ≤ 2 * (NN.val.map fun e => samplesSize (s.prevS e.1)).sum := by
        rw [← hG]; exact hatS_cost MM m A σ tape j q s P.α _ hN2
      generalize hGY : (Charged.foldl (κ := Op) (κₛ := Cell) (β := List Scalar) _
        (List.range P.γ) _) = YY
      have hY : Charged.steps (rate MM m) YY ≤ P.γ * (2 * P.β + 1) ∧ YY.val.length ≤ P.γ := by
        rw [← hGY]; exact Ys_cost MM m P HH.val zero _
      have hmd := hmed YY.val
      generalize (Scalar.median YY.val) = MD at hmd ⊢
      split
      all_goals
        simp only [Charged.steps_bind, Charged.steps_pure, Charged.val_pure, hlit, hmul, hdiv, hmin,
          hle, add_zero, zero_add]
        generalize hGO : (Charged.foldl (κ := Op) (κₛ := Cell)
          (β := Nfa.Program.Samples × Scalar) _ (List.range P.α) _) = OO
        have hO : Charged.steps (rate MM m) OO ≤ 2 * samplesSize HH.val + 2 * P.α := by
          rw [← hGO]; exact (out_cost MM m j q tape P.α HH.val _ s.total).1
        have hp1' : Charged.steps (rate MM m) (Nfa.Program.predecessors A prev q) ≤
            2 * prev.length := hp1
        simp only [List.length_cons] at hp4 hN1
        have hsum := hN3.trans hp3
        generalize P.γ * (2 * P.β + 1) = g1 at hY hγβ
        generalize 3 * P.γ * (P.β + 1) = g2 at hγβ ⊢
        omega
  · unfold Nfa.Program.estimateAndSample
    simp only [Charged.val_bind]
    split
    all_goals
      simp only [Charged.val_bind, Charged.val_pure]
      split
      all_goals
        simp only [Charged.val_bind, Charged.val_pure]
        exact ⟨_, _, _, rfl, (out_cost MM (Fintype.card Q) j q tape P.α _ _ s.total).2⟩

end Nfa.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `estimateAndSample_cost` via `predecessors_cost`, `normalized_cost`, `hatS_cost`, `Ys_cost`, `out_cost`
-/
