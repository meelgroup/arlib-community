/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.TapeLaw
import ArlibCommunity.Algorithms.CV18.Analysis.ModelSupport

/-!
# Measurability of a tape program's run

`TapeProgram.tapeLaw_map_exec` needs the result of a run to be a measurable function of
the tape.  `MeasFam member f` says that a family `f a` of tape programs runs measurably
in its argument, its budget and its tape together.  It is closed under the ways the
algorithm is built: results computed by measurable maps, sequencing, membership calls,
draws, and case splits on measurable conditions.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace ArlibCommunity.Algorithms.CV18

open ArlibCommunity.Algorithms.CV18.Model.Operations

namespace TapeProgram

variable {n : ℕ} (member : AmbientSpace n → Bool)
variable {A A' β γ : Type} [MeasurableSpace A] [MeasurableSpace A'] [MeasurableSpace β]
  [MeasurableSpace γ]

/-- **A family of tape programs runs measurably**: the run `execB member (f a) b t` is a
measurable function of the argument `a`, the budget `b` and the tape `t` together. -/
def MeasFam (f : A → TapeProgram n β) : Prop :=
  Measurable fun p : A × ℕ × Tape n => execB member (f p.1) p.2.1 p.2.2

variable {member}

theorem MeasFam.comp {f : A → TapeProgram n β} (hf : MeasFam member f) {φ : A' → A}
    (hφ : Measurable φ) : MeasFam member fun a => f (φ a) :=
  Measurable.comp hf ((hφ.comp measurable_fst).prodMk measurable_snd)

theorem MeasFam.congr {f g : A → TapeProgram n β} (hf : MeasFam member f) (h : ∀ a, f a = g a) :
    MeasFam member g := by
  have : f = g := funext h
  exact this ▸ hf

theorem MeasFam.pure {g : A → β} (hg : Measurable g) :
    MeasFam member fun a => TapeProgram.pure (n := n) (g a) :=
  (measurable_some.comp (hg.comp measurable_fst)).prodMk measurable_snd

/-- Sequencing. -/
theorem MeasFam.bind [Inhabited β] {f : A → TapeProgram n β} {h : A × β → TapeProgram n γ}
    (hf : MeasFam member f) (hh : MeasFam member h) :
    MeasFam member fun a => (f a).bind fun x => h (a, x) := by
  -- the continuation, as a function of the argument and the first run's outcome
  let Φ : (A × ℕ × Tape n) × Option β → Option γ × ℕ × Tape n := fun p =>
    match p.2 with
    | none => (none, p.1.2.1, p.1.2.2)
    | some x => execB member (h (p.1.1, x)) p.1.2.1 p.1.2.2
  have hΦ : Measurable Φ :=
    Measurable.optionCases (α := β) (β := Option γ × ℕ × Tape n) (γ := A × ℕ × Tape n)
      (default : β) (noneValue := fun q => (none, q.2.1, q.2.2))
      (someValue := fun q => execB member (h (q.1.1, q.2)) q.1.2.1 q.1.2.2)
      (measurable_const.prodMk (measurable_snd.fst.prodMk measurable_snd.snd))
      (Measurable.comp hh ((measurable_fst.fst.prodMk measurable_snd).prodMk
        (measurable_fst.snd.fst.prodMk measurable_fst.snd.snd)))
  have hrun : Measurable fun p : A × ℕ × Tape n =>
      ((p.1, (execB member (f p.1) p.2.1 p.2.2).2), (execB member (f p.1) p.2.1 p.2.2).1) :=
    (measurable_fst.prodMk hf.snd).prodMk hf.fst
  have heq : (fun p : A × ℕ × Tape n => execB member ((f p.1).bind fun x => h (p.1, x))
      p.2.1 p.2.2) = Φ ∘ fun p : A × ℕ × Tape n =>
        ((p.1, (execB member (f p.1) p.2.1 p.2.2).2), (execB member (f p.1) p.2.1 p.2.2).1) := by
    funext p
    rw [execB_bind]
    simp only [Function.comp_apply, Φ]
    rcases execB member (f p.1) p.2.1 p.2.2 with ⟨_ | x, b', t'⟩ <;> rfl
  unfold MeasFam
  rw [heq]
  exact hΦ.comp hrun

/-- A membership call at a measurably chosen point. -/
theorem MeasFam.query (hm : Measurable member) {x : A → AmbientSpace n} (hx : Measurable x)
    {k : A × Bool → TapeProgram n β} (hk : MeasFam member k) :
    MeasFam member fun a => TapeProgram.query (x a) fun ans => k (a, ans) := by
  have h0 : Measurable fun p : A × ℕ × Tape n => ((none : Option β), (0 : ℕ), p.2.2) :=
    measurable_const.prodMk (measurable_const.prodMk measurable_snd.snd)
  have h1 : Measurable fun p : A × ℕ × Tape n =>
      execB member (k (p.1, member (x p.1))) (p.2.1 - 1) p.2.2 :=
    Measurable.comp hk ((measurable_fst.prodMk (hm.comp (hx.comp measurable_fst))).prodMk
      ((measurable_snd.fst.sub_const 1).prodMk measurable_snd.snd))
  have heq : (fun p : A × ℕ × Tape n =>
      execB member (TapeProgram.query (x p.1) fun ans => k (p.1, ans)) p.2.1 p.2.2) =
      fun p => if p.2.1 ∈ ({0} : Set ℕ) then ((none : Option β), (0 : ℕ), p.2.2)
        else execB member (k (p.1, member (x p.1))) (p.2.1 - 1) p.2.2 := by
    funext p
    rcases p with ⟨a, _ | b, t⟩ <;> rfl
  unfold MeasFam
  rw [heq]
  exact Measurable.ite (measurable_snd.fst (measurableSet_singleton 0)) h0 h1

/-- Reading a component `π` of the next round. -/
private theorem MeasFam.read {X : Type} [MeasurableSpace X] (π : Round n → X)
    (hπ : Measurable π) {k : A × X → TapeProgram n β} (hk : MeasFam member k)
    {f : A → TapeProgram n β}
    (hf : ∀ a b t, execB member (f a) b t = execB member (k (a, π (t 0))) b t.tail) :
    MeasFam member f := by
  have heq : (fun p : A × ℕ × Tape n => execB member (f p.1) p.2.1 p.2.2) =
      fun p => execB member (k (p.1, π (p.2.2 0))) p.2.1 p.2.2.tail := by
    funext p
    exact hf _ _ _
  unfold MeasFam
  rw [heq]
  exact Measurable.comp hk ((measurable_fst.prodMk (hπ.comp ((measurable_pi_apply 0).comp
    measurable_snd.snd))).prodMk (measurable_snd.fst.prodMk
      (measurable_tape_tail.comp measurable_snd.snd)))

/-- A uniform point of the unit ball. -/
theorem MeasFam.ball {k : A × AmbientSpace n → TapeProgram n β} (hk : MeasFam member k) :
    MeasFam member fun a => TapeProgram.ball fun u => k (a, u) :=
  MeasFam.read (fun r => r.1) measurable_fst hk fun _ _ _ => rfl

/-- A standard Gaussian vector. -/
theorem MeasFam.gaussian {k : A × AmbientSpace n → TapeProgram n β} (hk : MeasFam member k) :
    MeasFam member fun a => TapeProgram.gaussian fun g => k (a, g) :=
  MeasFam.read (fun r => r.2.1) (measurable_fst.comp measurable_snd) hk fun _ _ _ => rfl

/-- A uniform number in `[0, 1]`. -/
theorem MeasFam.unit {k : A × ℝ → TapeProgram n β} (hk : MeasFam member k) :
    MeasFam member fun a => TapeProgram.unit fun v => k (a, v) :=
  MeasFam.read (fun r => r.2.2) (measurable_snd.comp measurable_snd) hk fun _ _ _ => rfl

/-- A case split on a measurable condition. -/
theorem MeasFam.ite {P : A → Prop} [DecidablePred P] (hP : MeasurableSet {a | P a})
    {f g : A → TapeProgram n β} (hf : MeasFam member f) (hg : MeasFam member g) :
    MeasFam member fun a => if P a then f a else g a := by
  have heq : (fun p : A × ℕ × Tape n =>
      execB member (if P p.1 then f p.1 else g p.1) p.2.1 p.2.2) =
      fun p => if p.1 ∈ {a | P a} then execB member (f p.1) p.2.1 p.2.2
        else execB member (g p.1) p.2.1 p.2.2 := by
    funext p
    by_cases h : P p.1 <;> simp [h]
  unfold MeasFam
  rw [heq]
  exact Measurable.ite (measurable_fst hP) (f := fun p : A × ℕ × Tape n =>
    execB member (f p.1) p.2.1 p.2.2) hf hg

/-- A case split on an optional value. -/
theorem MeasFam.option [Inhabited β] {f : A → TapeProgram n γ}
    {g : A × β → TapeProgram n γ} (hf : MeasFam member f) (hg : MeasFam member g) :
    MeasFam member fun p : A × Option β =>
      match p.2 with
      | none => f p.1
      | some x => g (p.1, x) := by
  let Φ : (A × ℕ × Tape n) × Option β → Option γ × ℕ × Tape n := fun p =>
    match p.2 with
    | none => execB member (f p.1.1) p.1.2.1 p.1.2.2
    | some x => execB member (g (p.1.1, x)) p.1.2.1 p.1.2.2
  have hΦ : Measurable Φ :=
    Measurable.optionCases (α := β) (β := Option γ × ℕ × Tape n) (γ := A × ℕ × Tape n)
      (default : β) (noneValue := fun q => execB member (f q.1) q.2.1 q.2.2)
      (someValue := fun q => execB member (g (q.1.1, q.2)) q.1.2.1 q.1.2.2) hf
      (Measurable.comp hg ((measurable_fst.fst.prodMk measurable_snd).prodMk
        (measurable_fst.snd.fst.prodMk measurable_fst.snd.snd)))
  have heq : (fun p : (A × Option β) × ℕ × Tape n =>
      execB member (match p.1.2 with
        | none => f p.1.1
        | some x => g (p.1.1, x)) p.2.1 p.2.2) =
      Φ ∘ fun p : (A × Option β) × ℕ × Tape n => ((p.1.1, p.2), p.1.2) := by
    funext p
    rcases p with ⟨⟨a, _ | x⟩, b, t⟩ <;> rfl
  unfold MeasFam
  rw [heq]
  exact hΦ.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)

/-- A case split on a flag. -/
theorem MeasFam.bool {f g : A → TapeProgram n β} (hf : MeasFam member f)
    (hg : MeasFam member g) :
    MeasFam member fun p : A × Bool => if p.2 = true then f p.1 else g p.1 :=
  MeasFam.ite (measurable_snd (measurableSet_singleton true))
    (hf.comp measurable_fst) (hg.comp measurable_fst)

end TapeProgram

end ArlibCommunity.Algorithms.CV18
