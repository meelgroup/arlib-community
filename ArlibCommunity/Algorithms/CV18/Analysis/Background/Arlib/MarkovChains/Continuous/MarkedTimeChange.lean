/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.TimeChange

/-!
# Time change driven by explicit proper-proposal marks

For the Gaussian Metropolis ball walk, a *proper* step means that the proposal lies in the
body.  Such a step is proper even when the Metropolis filter rejects it and the position does
not change.  Consequently the position-only clock `properCount` from `TimeChange.lean` cannot
express the Gaussian speedy-walk time change.

This file supplies the pathwise layer with the correct semantics.  A Boolean sequence `mark`
records whether each proposal is proper: `mark i` describes the transition from time `i` to
time `i + 1`.  The clock, hitting times, and sampled chain are defined from these marks, not
from equality of consecutive states.

The main identity is `markedChain_markedCount`.  It assumes only that an unmarked transition
holds its state:

`mark i = false -> state (i + 1) = state i`.

Marked transitions are deliberately allowed to hold as well.  This is exactly what is needed
for an in-body proposal rejected by the Gaussian Metropolis filter.
-/

namespace Arlib.MarkovChains

open MeasureTheory

/-! ## 1. The marked counting process -/

/-- The number of marked transitions among the first `t` transitions.  `mark i` describes
the transition from time `i` to time `i + 1`. -/
def markedCount (mark : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | t + 1 => markedCount mark t + if mark t then 1 else 0

@[simp] theorem markedCount_zero (mark : ℕ → Bool) : markedCount mark 0 = 0 := rfl

theorem markedCount_succ_of_true {mark : ℕ → Bool} {t : ℕ} (h : mark t = true) :
    markedCount mark (t + 1) = markedCount mark t + 1 := by
  simp [markedCount, h]

theorem markedCount_succ_of_false {mark : ℕ → Bool} {t : ℕ} (h : mark t = false) :
    markedCount mark (t + 1) = markedCount mark t := by
  simp [markedCount, h]

theorem markedCount_succ_eq_or (mark : ℕ → Bool) (t : ℕ) :
    markedCount mark (t + 1) = markedCount mark t ∨
      markedCount mark (t + 1) = markedCount mark t + 1 := by
  cases h : mark t
  · exact Or.inl (markedCount_succ_of_false h)
  · exact Or.inr (markedCount_succ_of_true h)

theorem markedCount_le_succ (mark : ℕ → Bool) (t : ℕ) :
    markedCount mark t ≤ markedCount mark (t + 1) := by
  rcases markedCount_succ_eq_or mark t with h | h <;> omega

theorem markedCount_succ_le (mark : ℕ → Bool) (t : ℕ) :
    markedCount mark (t + 1) ≤ markedCount mark t + 1 := by
  rcases markedCount_succ_eq_or mark t with h | h <;> omega

theorem markedCount_mono (mark : ℕ → Bool) : Monotone (markedCount mark) :=
  monotone_nat_of_le_succ (markedCount_le_succ mark)

theorem markedCount_le_self (mark : ℕ → Bool) (t : ℕ) : markedCount mark t ≤ t := by
  induction t with
  | zero => simp
  | succ t ih => exact (markedCount_succ_le mark t).trans (Nat.succ_le_succ ih)

/-- The marked clock reads only marks strictly before `t`. -/
theorem markedCount_congr {mark mark' : ℕ → Bool} {t : ℕ}
    (h : ∀ i < t, mark i = mark' i) : markedCount mark t = markedCount mark' t := by
  induction t with
  | zero => simp
  | succ t ih =>
      change markedCount mark t + (if mark t then 1 else 0) =
        markedCount mark' t + (if mark' t then 1 else 0)
      rw [ih (fun i hi => h i (hi.trans_le (Nat.le_succ t))), h t (Nat.lt_succ_self t)]

/-! ## 2. Marked hitting times -/

/-- The first time by which `k` marked transitions have occurred.

As for `jumpTime`, this uses `0` as a junk value if the `k`-th mark never occurs.  Lemmas that
interpret it as a hitting time therefore carry an existence hypothesis. -/
noncomputable def markedTime (mark : ℕ → Bool) (k : ℕ) : ℕ :=
  sInf {t | k ≤ markedCount mark t}

theorem markedTime_le {mark : ℕ → Bool} {k t : ℕ} (h : k ≤ markedCount mark t) :
    markedTime mark k ≤ t :=
  Nat.sInf_le (s := {t | k ≤ markedCount mark t}) h

theorem markedCount_lt_of_lt_markedTime {mark : ℕ → Bool} {k j : ℕ}
    (h : j < markedTime mark k) : markedCount mark j < k := by
  have hj : j ∉ {t | k ≤ markedCount mark t} :=
    Nat.notMem_of_lt_sInf (s := {t | k ≤ markedCount mark t}) h
  simpa [Set.mem_setOf_eq] using hj

theorem le_markedCount_markedTime {mark : ℕ → Bool} {k : ℕ}
    (h : ∃ t, k ≤ markedCount mark t) : k ≤ markedCount mark (markedTime mark k) :=
  Nat.sInf_mem (s := {t | k ≤ markedCount mark t}) h

@[simp] theorem markedTime_zero (mark : ℕ → Bool) : markedTime mark 0 = 0 :=
  Nat.le_zero.1 (markedTime_le (by simp))

theorem markedTime_eq_zero_of_not_exists {mark : ℕ → Bool} {k : ℕ}
    (h : ¬ ∃ t, k ≤ markedCount mark t) : markedTime mark k = 0 := by
  have hempty : {t | k ≤ markedCount mark t} = (∅ : Set ℕ) := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun ht => h ⟨t, ht⟩
  rw [markedTime, hempty, Nat.sInf_empty]

/-- Exactly `k` marks have occurred at the `k`-th marked time. -/
theorem markedCount_markedTime {mark : ℕ → Bool} {k : ℕ}
    (h : ∃ t, k ≤ markedCount mark t) : markedCount mark (markedTime mark k) = k := by
  have hmem := le_markedCount_markedTime h
  rcases Nat.eq_zero_or_pos (markedTime mark k) with hz | hpos
  · rw [hz] at hmem ⊢
    simp only [markedCount_zero] at hmem ⊢
    omega
  · obtain ⟨j, hj⟩ : ∃ j, markedTime mark k = j + 1 :=
      ⟨markedTime mark k - 1, by omega⟩
    have hlt : markedCount mark j < k := markedCount_lt_of_lt_markedTime (by omega)
    have hle : markedCount mark (j + 1) ≤ markedCount mark j + 1 :=
      markedCount_succ_le mark j
    rw [hj] at hmem ⊢
    omega

theorem le_markedTime {mark : ℕ → Bool} {k : ℕ}
    (h : ∃ t, k ≤ markedCount mark t) : k ≤ markedTime mark k := by
  have hcount := markedCount_markedTime h
  have hle := markedCount_le_self mark (markedTime mark k)
  omega

theorem markedExists_of_succ {mark : ℕ → Bool} {k : ℕ}
    (h : ∃ t, k + 1 ≤ markedCount mark t) : ∃ t, k ≤ markedCount mark t := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, by omega⟩

theorem markedTime_lt_markedTime_succ {mark : ℕ → Bool} {k : ℕ}
    (h : ∃ t, k + 1 ≤ markedCount mark t) :
    markedTime mark k < markedTime mark (k + 1) := by
  have h1 : markedCount mark (markedTime mark (k + 1)) = k + 1 :=
    markedCount_markedTime h
  have h0 : markedCount mark (markedTime mark k) = k :=
    markedCount_markedTime (markedExists_of_succ h)
  have hle : markedTime mark k ≤ markedTime mark (k + 1) := markedTime_le (by omega)
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · rw [heq] at h0
    omega

/-- The transition landing at the positive `k`-th marked time is marked. -/
theorem marked_at_markedTime_succ {mark : ℕ → Bool} {k : ℕ}
    (h : ∃ t, k + 1 ≤ markedCount mark t) :
    mark (markedTime mark (k + 1) - 1) = true := by
  have hpos : 0 < markedTime mark (k + 1) :=
    lt_of_lt_of_le (Nat.zero_lt_succ k) (le_markedTime h)
  obtain ⟨j, hj⟩ : ∃ j, markedTime mark (k + 1) = j + 1 :=
    ⟨markedTime mark (k + 1) - 1, by omega⟩
  have hbefore : markedCount mark j < k + 1 :=
    markedCount_lt_of_lt_markedTime (by omega)
  have hat : markedCount mark (j + 1) = k + 1 := by
    rw [← hj]
    exact markedCount_markedTime h
  cases hm : mark j
  · rw [markedCount_succ_of_false hm] at hat
    omega
  · simpa [hj] using hm

/-! ## 3. The marked chain and pathwise time change -/

variable {Om : Type*}

/-- The state observed at the `k`-th marked time. -/
noncomputable def markedChain (state : ℕ → Om) (mark : ℕ → Bool) (k : ℕ) : Om :=
  state (markedTime mark k)

@[simp] theorem markedChain_zero (state : ℕ → Om) (mark : ℕ → Bool) :
    markedChain state mark 0 = state 0 := by
  rw [markedChain, markedTime_zero]

theorem markedChain_apply (state : ℕ → Om) (mark : ℕ → Bool) (k : ℕ) :
    markedChain state mark k = state (markedTime mark k) := rfl

/-- If the marked count does not change on an interval, neither does the state, provided every
unmarked transition holds.  Marked transitions may hold or move. -/
theorem eq_of_markedCount_eq {state : ℕ → Om} {mark : ℕ → Bool}
    (hhold : ∀ i, mark i = false → state (i + 1) = state i)
    {a b : ℕ} (hab : a ≤ b) (hcount : markedCount mark a = markedCount mark b) :
    state a = state b := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
      have hmono : markedCount mark b ≤ markedCount mark (b + 1) := markedCount_le_succ mark b
      have hab' : markedCount mark a ≤ markedCount mark b := markedCount_mono mark hab
      have hb : markedCount mark a = markedCount mark b :=
        le_antisymm hab' (by rw [hcount]; exact hmono)
      have hm : mark b = false := by
        cases hm : mark b
        · rfl
        · have hinc := markedCount_succ_of_true hm
          have hsame : markedCount mark (b + 1) = markedCount mark b := by
            rw [← hcount, hb]
          omega
      rw [hhold b hm]
      exact ih hb

/-- The marked time-change identity.  It remains valid when a marked Metropolis proposal is
rejected and hence leaves the state unchanged. -/
theorem markedChain_markedCount (state : ℕ → Om) (mark : ℕ → Bool)
    (hhold : ∀ i, mark i = false → state (i + 1) = state i) (t : ℕ) :
    markedChain state mark (markedCount mark t) = state t := by
  have hle : markedTime mark (markedCount mark t) ≤ t := markedTime_le le_rfl
  have heq : markedCount mark (markedTime mark (markedCount mark t)) = markedCount mark t :=
    markedCount_markedTime ⟨t, le_rfl⟩
  exact eq_of_markedCount_eq hhold hle heq

/-- Marked times telescope into the lengths of the marked sojourns. -/
theorem markedTime_eq_sum_sojourn {mark : ℕ → Bool} {k : ℕ}
    (h : ∃ t, k ≤ markedCount mark t) :
    markedTime mark k =
      ∑ j ∈ Finset.range k, (markedTime mark (j + 1) - markedTime mark j) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk : ∃ t, k ≤ markedCount mark t := markedExists_of_succ h
      have hlt : markedTime mark k < markedTime mark (k + 1) :=
        markedTime_lt_markedTime_succ h
      rw [Finset.sum_range_succ, ← ih hk]
      omega

/-! ## 4. Measurability -/

section Measurability

/-- The explicit mark event is measurable without any measurable-equality assumption on the
state space. -/
theorem measurableSet_markedStep (i : ℕ) :
    MeasurableSet {mark : ℕ → Bool | mark i = true} := by
  have h : {mark : ℕ → Bool | mark i = true} = (fun mark : ℕ → Bool => mark i) ⁻¹' {true} := rfl
  rw [h]
  exact (measurable_pi_apply i) (measurableSet_singleton true)

theorem markedCount_succ_eq_add_indicator (mark : ℕ → Bool) (t : ℕ) :
    markedCount mark (t + 1) = markedCount mark t +
      {mark' : ℕ → Bool | mark' t = true}.indicator (fun _ => 1) mark := by
  cases h : mark t
  · rw [markedCount_succ_of_false h, Set.indicator_of_notMem (by simpa using h), add_zero]
  · rw [markedCount_succ_of_true h, Set.indicator_of_mem (by simpa using h)]

theorem measurable_markedCount (t : ℕ) :
    Measurable fun mark : ℕ → Bool => markedCount mark t := by
  induction t with
  | zero => simp
  | succ t ih =>
      simp only [markedCount_succ_eq_add_indicator]
      exact ih.add (measurable_const.indicator (measurableSet_markedStep t))

theorem measurableSet_le_markedCount (k t : ℕ) :
    MeasurableSet {mark : ℕ → Bool | k ≤ markedCount mark t} :=
  (measurable_markedCount t) (MeasurableSet.of_discrete (s := {c : ℕ | k ≤ c}))

/-- The marked hitting times are measurable functions of the mark sequence. -/
theorem measurable_markedTime (k : ℕ) :
    Measurable fun mark : ℕ → Bool => markedTime mark k := by
  have hup : ∀ mark : ℕ → Bool, ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ →
      k₁ ∈ {t | k ≤ markedCount mark t} → k₂ ∈ {t | k ≤ markedCount mark t} := by
    intro mark k₁ k₂ hk hmem
    exact le_trans hmem (markedCount_mono mark hk)
  refine measurable_to_countable' fun m => ?_
  match m with
  | 0 =>
      have hset : (fun mark : ℕ → Bool => markedTime mark k) ⁻¹' {0} =
          {mark : ℕ → Bool | k ≤ markedCount mark 0} ∪
            ⋂ t : ℕ, {mark : ℕ → Bool | k ≤ markedCount mark t}ᶜ := by
        ext mark
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_iInter, Set.mem_compl_iff, markedTime]
        rw [Nat.sInf_eq_zero]
        constructor
        · intro h
          rcases h with h | h
          · exact Or.inl h
          · exact Or.inr fun t ht => (Set.eq_empty_iff_forall_notMem.1 h t) ht
        · intro h
          rcases h with h | h
          · exact Or.inl h
          · exact Or.inr (Set.eq_empty_iff_forall_notMem.2 fun t ht => h t ht)
      rw [hset]
      exact (measurableSet_le_markedCount k 0).union
        (MeasurableSet.iInter fun t => (measurableSet_le_markedCount k t).compl)
  | j + 1 =>
      have hset : (fun mark : ℕ → Bool => markedTime mark k) ⁻¹' {j + 1} =
          {mark : ℕ → Bool | k ≤ markedCount mark (j + 1)} ∩
            {mark : ℕ → Bool | k ≤ markedCount mark j}ᶜ := by
        ext mark
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_setOf_eq,
          Set.mem_compl_iff, markedTime]
        exact Nat.sInf_upward_closed_eq_succ_iff (hup mark) j
      rw [hset]
      exact (measurableSet_le_markedCount k (j + 1)).inter
        (measurableSet_le_markedCount k j).compl

variable [MeasurableSpace Om]

/-- The marked chain is measurable jointly in the state path and mark path. -/
theorem measurable_markedChain (k : ℕ) :
    Measurable fun p : (ℕ → Om) × (ℕ → Bool) => markedChain p.1 p.2 k := by
  have h : (fun p : (ℕ → Om) × (ℕ → Bool) => markedChain p.1 p.2 k) =
      (fun q : ℕ × (ℕ → Om) => q.2 q.1) ∘
        fun p : (ℕ → Om) × (ℕ → Bool) => (markedTime p.2 k, p.1) := rfl
  rw [h]
  exact (measurable_from_prod_countable_right fun m => measurable_pi_apply m).comp
    (((measurable_markedTime k).comp measurable_snd).prodMk measurable_fst)

end Measurability

end Arlib.MarkovChains

#print axioms Arlib.MarkovChains.markedCount_markedTime
#print axioms Arlib.MarkovChains.marked_at_markedTime_succ
#print axioms Arlib.MarkovChains.markedChain_markedCount
#print axioms Arlib.MarkovChains.measurable_markedTime
#print axioms Arlib.MarkovChains.measurable_markedChain
