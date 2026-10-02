import Esa22Copy.Model.Prior
import Esa22Copy.Model.Prelude
import Esa22Copy.Model.Run
import Esa22Copy.Meta.ModelClosure
import Arlib.Prelude
import Esa22Copy.Interface.Encoding
import Esa22Copy.Interface.Pseudocode
import Esa22Copy.Interface.ProgramModel

/-!
# The space bound of Algorithm 1

`f0Estimator_space_proof`: on every reachable run, the sample `X` never holds more
than `thresh ε δ A.length` cells, at any point of the run including inside a step
(esa22-final.tex:507: "the size of the set of samples kept by the algorithm is always
`≤ thresh`").

The argument is the paper's one sentence, made into an invariant on the program
state: `|X| ≤ thr`, and `|X| < thr` while ⊥ has not been output.  One step from such
a state erases (cannot rise), may insert (rises to at most `thr`), and if `|X| = thr`
thins (cannot rise) and either drops below `thr` or records ⊥ — so its excursion is
at most `thr - |X|` and the invariant is restored (`step_space_inv`).  A fold of such
steps peaks at most `thr` (`foldl_step_space`), and the final read-out holds nothing
(`estimator_space_peak`).  The bound holds for every tape, so `ε, δ` enter only
through the side condition `0 < thr` on a non-empty stream: with `thr = 0` the first
pick (always accepted at level 0) would hold one cell.
-/

set_option autoImplicit false

namespace Esa22Copy.Analysis

open Esa22Copy.Model Arlib.Computation

/-- INTERNAL: the roster count after an insertion, in `Finset` terms.
TEXLINE: esa22-final.tex:430 -/
theorem roster_card_val_insert {n : ℕ} (a : Fin n) (X : Roster (Fin n)) :
    ((Roster.insert (κ := Operations.Op) (κₛ := Operations.Cell) a X).val).card
      = (insert a X.toFinset).card := by
  rw [← Roster.card_toFinset, Roster.toFinset_insert]

/-- INTERNAL: the roster count after an erasure, in `Finset` terms.
TEXLINE: esa22-final.tex:429 -/
theorem roster_card_val_erase {n : ℕ} (a : Fin n) (X : Roster (Fin n)) :
    ((Roster.erase (κ := Operations.Op) (κₛ := Operations.Cell) a X).val).card
      = (X.toFinset.erase a).card := by
  rw [← Roster.card_toFinset, Roster.toFinset_erase]

/-- INTERNAL: one step of Algorithm 1 from a state with `|X| ≤ thr` (and `|X| < thr`
while running) peaks at most `thr` in absolute terms, its net is exactly the change in
`|X|`, and it restores the invariant.
TEXLINE: esa22-final.tex:422-445 -/
theorem step_space_inv {n L : ℕ} (thr : ℕ) (s : Program.State n) (a : Fin n)
    (d : Program.Draw n L) (hc : s.X.card ≤ thr)
    (hrun : s.bot.get.isNone = true → s.X.card < thr) :
    let p := Program.step thr s (a, d)
    (s.X.card : ℤ) + p.space.peak Cell.cell ≤ thr ∧
      p.space.net Cell.cell = (p.val.X.card : ℤ) - s.X.card ∧
      p.val.X.card ≤ thr ∧ (p.val.bot.get.isNone = true → p.val.X.card < thr) := by
  intro p
  by_cases hr : s.bot.get.isNone = true
  swap
  · have hr' : s.bot.get.isNone = false := by
      cases h : s.bot.get.isNone <;> simp_all
    simp [p, Program.step, hr']
    exact hc
  have hc := hrun hr
  have hkp : ∀ (y : Fin n) (k : Cell),
      (Coins.flip (κ := Operations.Op) (κₛ := Operations.Cell) y d.thin).space.peak k ≤ 0 := by
    intro y k; simp
  have hks : ∀ (y : Fin n),
      (Coins.flip (κ := Operations.Op) (κₛ := Operations.Cell) y d.thin).space = 1 := by
    intro y; simp
  have he : (s.X.toFinset.erase a).card ≤ s.X.card := by
    rw [← Roster.card_toFinset]; exact Finset.card_erase_le
  by_cases hp : Interface.pickAccepts s.rate.levelOf d.pick = true
  · set X1 := (Roster.erase (κ := Operations.Op) (κₛ := Operations.Cell) a s.X).val with hX1
    set X2 := (Roster.insert (κ := Operations.Op) (κₛ := Operations.Cell) a X1).val with hX2
    have h1 : X1.card = (s.X.toFinset.erase a).card := roster_card_val_erase a s.X
    have h2 : X2.card = (insert a X1.toFinset).card := roster_card_val_insert a X1
    have h2' : (insert a X1.toFinset).card ≤ X1.card + 1 := by
      rw [← Roster.card_toFinset]; exact Finset.card_insert_le _ _
    have h2'' : X1.card ≤ (insert a X1.toFinset).card := by
      rw [← Roster.card_toFinset]; exact Finset.card_le_card (Finset.subset_insert _ _)
    by_cases hf : X2.card = thr
    · set X3 := (Roster.filterErase
        (fun y => Coins.flip (κ := Operations.Op) (κₛ := Operations.Cell) y d.thin) X2).val
        with hX3
      have h3 : X3.card ≤ X2.card := by
        have := Roster.space_net_filterErase_nonpos
          (fun y => Coins.flip (κ := Operations.Op) (κₛ := Operations.Cell) y d.thin) hkp X2
          Cell.cell
        rw [Roster.space_net_filterErase _ hks] at this
        simp at this
        omega
      by_cases hs : X3.card = thr
      · simp [p, Program.step, hr, hp, hf, hs, ← hX1, ← hX2, ← hX3,
          Roster.space_net_filterErase _ hks, Roster.space_peak_filterErase _ hkp]
        omega
      · simp [p, Program.step, hr, hp, hf, hs, ← hX1, ← hX2, ← hX3,
          Roster.space_net_filterErase _ hks, Roster.space_peak_filterErase _ hkp]
        omega
    · simp [p, Program.step, hr, hp, hf, ← hX1, ← hX2]
      omega
  · set X1 := (Roster.erase (κ := Operations.Op) (κₛ := Operations.Cell) a s.X).val with hX1
    have h1 : X1.card = (s.X.toFinset.erase a).card := roster_card_val_erase a s.X
    by_cases hf : X1.card = thr
    · omega
    · simp [p, Program.step, hr, hp, hf, ← hX1]
      omega

/-- INTERNAL: the loop of Algorithm 1 (lines 2-10), from any state satisfying the
invariant, never holds more than `thr` cells.
TEXLINE: esa22-final.tex:507 -/
theorem foldl_step_space {n L : ℕ} (thr : ℕ) :
    ∀ (l : List (Fin n × Program.Draw n L)) (s : Program.State n), s.X.card ≤ thr →
      (s.bot.get.isNone = true → s.X.card < thr) →
      (s.X.card : ℤ) + (Charged.foldl (Program.step thr) l s).space.peak Cell.cell ≤ thr := by
  intro l
  induction l with
  | nil => intro s hc _; simpa using hc
  | cons ad l ih =>
      intro s hc hrun
      obtain ⟨a, d⟩ := ad
      obtain ⟨hpk, hnet, hc', hrun'⟩ := step_space_inv thr s a d hc hrun
      have hrest := ih _ hc' hrun'
      rw [Charged.space_foldl_cons, Profile.peak_mul]
      omega

/-- INTERNAL: every run of Algorithm 1 with threshold `thr` holds at most `thr` cells,
provided `thr > 0` or the stream is empty.
TEXLINE: esa22-final.tex:507 -/
theorem estimator_space_peak {n L : ℕ} (thr : ℕ) (A : List (Fin n))
    (tape : List (Program.Draw n L)) (hthr : 0 < thr ∨ A = []) :
    (Program.estimator thr A tape).space.peak Cell.cell ≤ thr := by
  have hfold : (Charged.foldl (Program.step thr) (A.zip tape) Program.init).space.peak
      Cell.cell ≤ thr := by
    rcases hthr with hthr | rfl
    · have := foldl_step_space thr (A.zip tape) (Program.init (n := n))
        (by simp [Program.init]) (fun _ => by simpa [Program.init] using hthr)
      simpa [Program.init] using this
    · simp
  set F := Charged.foldl (Program.step thr) (A.zip tape) Program.init with hF
  have hnp := F.space.net_le_peak Cell.cell
  unfold Program.estimator
  rw [← hF, Charged.space_bind, Profile.peak_mul]
  by_cases hb : F.val.bot.get.isNone = true
  · simp [hb]
    omega
  · have hb' : F.val.bot.get.isNone = false := by
      cases h : F.val.bot.get.isNone <;> simp_all
    simp [hb']
    omega

/-- Proof-side owner for `Esa22Copy.f0Estimator_space`; its statement is fixed by the proof charter.
PAPER: esa22-final.tex:507 -/
-- in namespace Esa22Copy.Analysis; open Esa22Copy Esa22Copy.Model Arlib.Computation
theorem f0Estimator_space_proof (hprior : Prior) {n : ℕ} (A : List (Fin n)) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) : worstSpace (Arlib.Computation.Cell.cell : Operations.Cell) 0 (run A ε δ) ≤ (thresh ε δ A.length : ℕ∞) := by
  have hthr : 0 < thresh ε δ A.length ∨ A = [] := by
    by_cases h : A = []
    · exact Or.inr h
    left
    have hm : (1 : ℝ) ≤ A.length := by
      exact_mod_cast List.length_pos_iff.mpr h
    have hx : 1 < 8 * (A.length : ℝ) / δ := by
      rw [one_lt_div hδ0]; linarith
    unfold thresh
    apply Nat.ceil_pos.mpr
    exact mul_pos (div_pos (by norm_num) (pow_pos hε0 2)) (Real.logb_pos (by norm_num) hx)
  apply worstSpace_le
  intro p hp
  unfold run at hp
  rw [PMF.support_map] at hp
  obtain ⟨tape, -, rfl⟩ := hp
  have := estimator_space_peak (thresh ε δ A.length) A tape hthr
  simpa using this

end Esa22Copy.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `f0Estimator_space_proof` via the `|X| ≤ thr` / `|X| < thr`-while-running invariant; axioms propext, Classical.choice, Quot.sound
-/
