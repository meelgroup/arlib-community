import Esa22Copy.Model.Program
import Esa22Copy.Interface.Pseudocode
import Esa22Copy.Interface.Encoding
import Esa22Copy.Model.Prior
import Esa22Copy.Model.Prelude
import Esa22Copy.Model.Operations
import Esa22Copy.Model.Run

/-!
# The program and the model are the same algorithm

`Esa22Copy.Model.Program` is what the paper's claims are about: a charged
computation whose state is sealed and whose cost is an operator applied to it.
`Esa22Copy.Interface.Pseudocode` is the same algorithm as mathematics for the
answer/output object the correctness theorem measures. Time and space stay over
`Esa22Copy.Model.Program`; this file is only the transport for correctness.

It is a ladder. Each theorem below is proved from the ones above it, and
`output_eq_outputLaw` is the top: it is the one lemma the analysis rewrites
through, and the only one anything outside this file should need.

Every rung is proved.
-/

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · every theorem in this file (`init_view_eq` through `output_eq_outputLaw`)
  closed, no `sorry` left; `#print axioms Esa22Copy.output_eq_outputLaw` reports only
  `propext, Classical.choice, Quot.sound`.
-/

set_option autoImplicit false

namespace Esa22Copy

/-- The program's initial state, read through the interface, is the pseudocode's initial state (p = 1, X = ∅, running). -/
theorem init_view_eq {n : ℕ} : ({ X := Esa22Copy.Interface.sample (Esa22Copy.Program.init : Esa22Copy.Program.State n), level := Esa22Copy.Interface.level (Esa22Copy.Program.init : Esa22Copy.Program.State n), running := Esa22Copy.Interface.running (Esa22Copy.Program.init : Esa22Copy.Program.State n) } : Esa22Copy.Interface.Pseudocode.State n) = Esa22Copy.Interface.Pseudocode.init := by
  simp [Esa22Copy.Interface.Pseudocode.init]

open Arlib.Computation in
/-- Fixing one draw (level bits and halving coins) makes a single program step match the pseudocode loop body exactly: drop, pick with probability 2^-level, then throw away, halve and check when full. -/
theorem stepState_draw_eq {n L : ℕ} (thr : ℕ) (s : Esa22Copy.Program.State n) (a : Fin n) (bits : Fin L → Bool) (heads : Finset (Fin n)) : ({ X := Esa22Copy.Interface.sample (Esa22Copy.Interface.stepState thr s (a, (⟨Arlib.Computation.Block.ofFun bits, Arlib.Computation.Coins.ofFinset heads⟩ : Esa22Copy.Program.Draw n L))), level := Esa22Copy.Interface.level (Esa22Copy.Interface.stepState thr s (a, (⟨Arlib.Computation.Block.ofFun bits, Arlib.Computation.Coins.ofFinset heads⟩ : Esa22Copy.Program.Draw n L))), running := Esa22Copy.Interface.running (Esa22Copy.Interface.stepState thr s (a, (⟨Arlib.Computation.Block.ofFun bits, Arlib.Computation.Coins.ofFinset heads⟩ : Esa22Copy.Program.Draw n L))) } : Esa22Copy.Interface.Pseudocode.State n) = (if Esa22Copy.Interface.running s then (fun (v : Esa22Copy.Interface.Pseudocode.State n) => if Esa22Copy.Interface.Pseudocode.full thr v then Esa22Copy.Interface.Pseudocode.check thr (Esa22Copy.Interface.Pseudocode.halve { v with X := v.X.filter (· ∈ heads) }) else v) ((fun (u : Esa22Copy.Interface.Pseudocode.State n) => if Esa22Copy.Interface.Pseudocode.firstOnes u.level bits then { u with X := insert a u.X } else u) (Esa22Copy.Interface.Pseudocode.drop a ({ X := Esa22Copy.Interface.sample s, level := Esa22Copy.Interface.level s, running := Esa22Copy.Interface.running s } : Esa22Copy.Interface.Pseudocode.State n))) else ({ X := Esa22Copy.Interface.sample s, level := Esa22Copy.Interface.level s, running := Esa22Copy.Interface.running s } : Esa22Copy.Interface.Pseudocode.State n)) := by
  have hre : (Slot.isEmpty s.bot : Charged Esa22Copy.Model.Operations.Op
      Esa22Copy.Model.Operations.Cell Bool).val = Esa22Copy.Interface.running s := rfl
  have hfe : ∀ (X : Roster (Fin n)),
      (Roster.filterErase (κ := Esa22Copy.Model.Operations.Op)
          (κₛ := Esa22Copy.Model.Operations.Cell)
          (fun y => Coins.flip y (Coins.ofFinset heads)) X).val.toFinset
        = X.toFinset.filter (· ∈ heads) := by
    intro X
    rw [Roster.toFinset_filterErase]
    congr 1
    ext x
    rw [Coins.val_flip, Coins.heads'_ofFinset]
    by_cases h : x ∈ heads <;> simp [h]
  simp only [Esa22Copy.Interface.stepState, Esa22Copy.Program.step, Charged.val_bind, hre]
  rcases Bool.eq_false_or_eq_true (Esa22Copy.Interface.running s) with hrun | hrun <;>
    simp only [hrun, if_true, Esa22Copy.Interface.sample,
      Esa22Copy.Interface.level, Esa22Copy.Interface.Pseudocode.drop]
  · have hpa : (Sampler.accept (Block.ofFun bits) s.rate : Charged Esa22Copy.Model.Operations.Op
        Esa22Copy.Model.Operations.Cell Bool).val
        = Esa22Copy.Interface.Pseudocode.firstOnes s.rate.levelOf bits := rfl
    simp only [Charged.val_bind, hpa]
    rcases Bool.eq_false_or_eq_true (Esa22Copy.Interface.Pseudocode.firstOnes s.rate.levelOf bits)
      with hpick | hpick <;>
      simp [hpick, Roster.toFinset_insert, Roster.toFinset_erase, ← Roster.card_toFinset,
        Esa22Copy.Interface.Pseudocode.full]
    · have hb : s.bot.get = none := by
        simpa [Esa22Copy.Interface.running] using hrun
      by_cases hfull : (s.X.toFinset.erase a).card + 1 = thr
      · simp only [hfull, if_true, Charged.val_bind,
          hfe, ← Roster.card_toFinset, Roster.val_cardEq]
        by_cases hstuck :
            ((insert a (s.X.toFinset.erase a)).filter (· ∈ heads)).card = thr <;>
          simp [hstuck, Slot.val_fill, hfe, Esa22Copy.Interface.Pseudocode.halve,
            Esa22Copy.Interface.Pseudocode.check, Esa22Copy.Interface.Pseudocode.full,
            Esa22Copy.Interface.running, hb]
      · simp [hfull, hb, Esa22Copy.Interface.running]
    · have hb : s.bot.get = none := by
        simpa [Esa22Copy.Interface.running] using hrun
      by_cases hfull : (s.X.toFinset.erase a).card = thr
      · simp only [hfull, if_true, Charged.val_bind,
          hfe, ← Roster.card_toFinset, Roster.val_cardEq]
        by_cases hstuck :
            ((s.X.toFinset.erase a).filter (· ∈ heads)).card = thr <;>
          simp [hstuck, Slot.val_fill, hfe, Esa22Copy.Interface.Pseudocode.halve,
            Esa22Copy.Interface.Pseudocode.check, Esa22Copy.Interface.Pseudocode.full,
            Esa22Copy.Interface.running, hb]
      · simp [hfull, hb, Esa22Copy.Interface.running]
  · simp [hrun]

open Arlib.Computation in
/-- Pushing the per-step draw law through one program step gives the pseudocode's one-step PMF; this follows from the pointwise draw equation after splitting drawLaw into independent bits and coins. -/
theorem stepState_law_eq {n L : ℕ} (thr : ℕ) (s : Esa22Copy.Program.State n) (a : Fin n) : (Esa22Copy.drawLaw n L).map (fun d => ({ X := Esa22Copy.Interface.sample (Esa22Copy.Interface.stepState thr s (a, d)), level := Esa22Copy.Interface.level (Esa22Copy.Interface.stepState thr s (a, d)), running := Esa22Copy.Interface.running (Esa22Copy.Interface.stepState thr s (a, d)) } : Esa22Copy.Interface.Pseudocode.State n)) = Esa22Copy.Interface.Pseudocode.step L thr ({ X := Esa22Copy.Interface.sample s, level := Esa22Copy.Interface.level s, running := Esa22Copy.Interface.running s } : Esa22Copy.Interface.Pseudocode.State n) a := by
  have hthrow : ∀ (v : Esa22Copy.Interface.Pseudocode.State n),
      ((PMF.uniformOfFintype (Finset (Fin n))).bind fun heads =>
          PMF.pure (if Esa22Copy.Interface.Pseudocode.full thr v then
              Esa22Copy.Interface.Pseudocode.check thr
                (Esa22Copy.Interface.Pseudocode.halve { v with X := v.X.filter (· ∈ heads) })
            else v))
        = if Esa22Copy.Interface.Pseudocode.full thr v then
            (PMF.uniformOfFintype (Finset (Fin n))).bind fun heads =>
              PMF.pure (Esa22Copy.Interface.Pseudocode.check thr
                (Esa22Copy.Interface.Pseudocode.halve { v with X := v.X.filter (· ∈ heads) }))
          else PMF.pure v := by
    intro v
    by_cases hv : Esa22Copy.Interface.Pseudocode.full thr v <;> simp [hv, PMF.bind_const]
  simp only [Esa22Copy.drawLaw, ← PMF.bind_pure_comp, PMF.bind_bind, PMF.pure_bind,
    Function.comp_apply]
  simp only [Esa22Copy.stepState_draw_eq]
  rcases Bool.eq_false_or_eq_true (Esa22Copy.Interface.running s) with hr | hr
  · simp only [hr, if_true, Esa22Copy.Interface.Pseudocode.step,
      Esa22Copy.Interface.Pseudocode.pick, Esa22Copy.Interface.Pseudocode.throw,
      ← PMF.bind_pure_comp, PMF.bind_bind, PMF.pure_bind, Function.comp_apply]
    congr 1
    funext bits
    rcases Bool.eq_false_or_eq_true
        (Esa22Copy.Interface.Pseudocode.firstOnes
          (Esa22Copy.Interface.Pseudocode.drop a
            { X := Esa22Copy.Interface.sample s, level := Esa22Copy.Interface.level s,
              running := Esa22Copy.Interface.running s }).level bits) with hf | hf <;>
      simp only [hf, if_true, if_false, hthrow]
  · simp [hr, Esa22Copy.Interface.Pseudocode.step, PMF.bind_const]

open Arlib.Computation in
/-- Induction on the stream: a fold over an i.i.d. tape has the same law as the pseudocode's sequential bind loop. -/
theorem foldState_law_eq {n L : ℕ} (thr : ℕ) (l : List (Fin n)) (s : Esa22Copy.Program.State n) : (Esa22Copy.tapeLaw n L l.length).map (fun tape => ({ X := Esa22Copy.Interface.sample (Esa22Copy.Interface.foldState thr (l.zip tape) s), level := Esa22Copy.Interface.level (Esa22Copy.Interface.foldState thr (l.zip tape) s), running := Esa22Copy.Interface.running (Esa22Copy.Interface.foldState thr (l.zip tape) s) } : Esa22Copy.Interface.Pseudocode.State n)) = Esa22Copy.Interface.Pseudocode.loop L thr l ({ X := Esa22Copy.Interface.sample s, level := Esa22Copy.Interface.level s, running := Esa22Copy.Interface.running s } : Esa22Copy.Interface.Pseudocode.State n) := by
  induction l generalizing s with
  | nil =>
    simp [Esa22Copy.tapeLaw, Esa22Copy.Interface.Pseudocode.loop, PMF.pure_map]
  | cons a l' ih =>
    simp only [List.length_cons, Esa22Copy.tapeLaw, PMF.map_bind,
      Esa22Copy.Interface.Pseudocode.loop]
    rw [← Esa22Copy.stepState_law_eq thr s a, PMF.bind_map]
    congr 1
    funext d
    rw [PMF.map_comp]
    simp only [Function.comp_apply]
    exact ih (Esa22Copy.Interface.stepState thr s (a, d))

/-- The final program state, viewed through the interface, has the pseudocode's final-state law: the fold law started from init. -/
theorem finalState_law_eq {n L : ℕ} (thr : ℕ) (A : List (Fin n)) : (Esa22Copy.tapeLaw n L A.length).map (fun tape => ({ X := Esa22Copy.Interface.sample (Esa22Copy.Interface.finalState thr A tape), level := Esa22Copy.Interface.level (Esa22Copy.Interface.finalState thr A tape), running := Esa22Copy.Interface.running (Esa22Copy.Interface.finalState thr A tape) } : Esa22Copy.Interface.Pseudocode.State n)) = Esa22Copy.Interface.Pseudocode.stateLaw L thr A := by
  have h := Esa22Copy.foldState_law_eq (L := L) thr A (Esa22Copy.Program.init (n := n))
  rw [Esa22Copy.init_view_eq] at h
  exact h

open Arlib.Computation in
/-- The value the charged program returns is the answer read off its final state; cost accounting does not affect the value. -/
theorem estimator_val_eq {n L : ℕ} (thr : ℕ) (A : List (Fin n)) (tape : List (Esa22Copy.Program.Draw n L)) : Arlib.Computation.Charged.val (Esa22Copy.Program.estimator thr A tape) = Esa22Copy.Interface.answerOf (Esa22Copy.Interface.finalState thr A tape) := by
  have hfs : (Charged.foldl (Esa22Copy.Program.step thr) (A.zip tape) Esa22Copy.Program.init).val
      = Esa22Copy.Interface.finalState thr A tape := rfl
  simp only [Esa22Copy.Program.estimator, Esa22Copy.Interface.answerOf, hfs,
    Charged.val_bind]
  by_cases h : (Esa22Copy.Interface.finalState thr A tape).bot.get = none <;>
    simp [h, Esa22Copy.Interface.running, Esa22Copy.Interface.level]

/-- Reading the answer off a program state (⊥ if halted, else |X|·2^level) agrees with the pseudocode's answer on its view. -/
theorem answerOf_eq_answer {n : ℕ} (s : Esa22Copy.Program.State n) : Esa22Copy.Interface.answerOf s = Esa22Copy.Interface.Pseudocode.answer ({ X := Esa22Copy.Interface.sample s, level := Esa22Copy.Interface.level s, running := Esa22Copy.Interface.running s } : Esa22Copy.Interface.Pseudocode.State n) := by
  simp [Esa22Copy.Interface.answerOf, Esa22Copy.Interface.Pseudocode.answer,
    Esa22Copy.Interface.sample, Esa22Copy.Interface.level, Esa22Copy.Interface.running,
    Arlib.Computation.Roster.card_toFinset]

/-- The program's output law over a random tape equals the pseudocode's answer law: map the final-state law through answer. -/
theorem estimator_law_eq {n L : ℕ} (thr : ℕ) (A : List (Fin n)) : (Esa22Copy.tapeLaw n L A.length).map (fun tape => Arlib.Computation.Charged.val (Esa22Copy.Program.estimator thr A tape)) = Esa22Copy.Interface.Pseudocode.answerLaw L thr A := by
  rw [Esa22Copy.Interface.Pseudocode.answerLaw, ← Esa22Copy.finalState_law_eq, PMF.map_comp]
  congr 1
  funext tape
  simp only [Function.comp_apply]
  rw [Esa22Copy.estimator_val_eq, Esa22Copy.answerOf_eq_answer]

/-- Capstone bridge: the program estimator's law equals the pseudocode answer law for every parameter choice, so the run's output equals the pseudocode output law at the paper's thresh and level width. Analysis rewrites through `.2`. -/
theorem output_eq_outputLaw {n : ℕ} (A : List (Fin n)) (ε δ : ℝ) : (∀ (L thr : ℕ), (Esa22Copy.tapeLaw n L A.length).map (fun tape => Arlib.Computation.Charged.val (Esa22Copy.Program.estimator thr A tape)) = Esa22Copy.Interface.Pseudocode.answerLaw L thr A) ∧ Esa22Copy.output A ε δ = Esa22Copy.Interface.Pseudocode.outputLaw A ε δ := by
  refine ⟨fun L thr => Esa22Copy.estimator_law_eq thr A, ?_⟩
  show ((Esa22Copy.tapeLaw n (A.length + 1) A.length).map
      (Esa22Copy.Program.estimator (thresh ε δ A.length) A)).map Arlib.Computation.Charged.val
      = Esa22Copy.Interface.Pseudocode.outputLaw A ε δ
  rw [PMF.map_comp]
  exact Esa22Copy.estimator_law_eq (thresh ε δ A.length) A

end Esa22Copy
