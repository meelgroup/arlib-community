/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.TapeLaw

/-!
# Measurability of a tape program's run

`MeasFam member f` says that a family `f a` of tape programs runs measurably in its
argument and the tape together.  It is closed under the ways the sampler is built:
results computed by measurable maps, sequencing, membership calls at measurable points,
draws, and case splits on measurable conditions.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace ArlibCommunity.Algorithms.HitAndRun

open ArlibCommunity.Algorithms.HitAndRun.Model.Operations

namespace TapeProgram

variable {n : ℕ} (member : State n → Bool)
variable {A A' β γ : Type} [MeasurableSpace A] [MeasurableSpace A'] [MeasurableSpace β]
  [MeasurableSpace γ]

/-- **A family of tape programs runs measurably**: `exec member (f a) t` is a measurable
function of the argument `a` and the tape `t` together. -/
def MeasFam (f : A → TapeProgram n β) : Prop :=
  Measurable fun q : A × Tape n => exec member (f q.1) q.2

variable {member}

theorem MeasFam.comp {f : A → TapeProgram n β} (hf : MeasFam member f) {φ : A' → A}
    (hφ : Measurable φ) : MeasFam member fun a => f (φ a) :=
  Measurable.comp hf ((hφ.comp measurable_fst).prodMk measurable_snd)

theorem MeasFam.congr {f g : A → TapeProgram n β} (hf : MeasFam member f)
    (h : ∀ a, f a = g a) : MeasFam member g := by
  have : f = g := funext h
  exact this ▸ hf

theorem MeasFam.pure {g : A → β} (hg : Measurable g) :
    MeasFam member fun a => TapeProgram.pure (n := n) (g a) :=
  (hg.comp measurable_fst).prodMk measurable_snd

/-- Sequencing. -/
theorem MeasFam.bind {f : A → TapeProgram n β} {h : A × β → TapeProgram n γ}
    (hf : MeasFam member f) (hh : MeasFam member h) :
    MeasFam member fun a => (f a).bind fun x => h (a, x) := by
  have heq : (fun q : A × Tape n => exec member ((f q.1).bind fun x => h (q.1, x)) q.2) =
      (fun q : (A × β) × Tape n => exec member (h q.1) q.2) ∘
        fun q : A × Tape n => ((q.1, (exec member (f q.1) q.2).1), (exec member (f q.1) q.2).2) := by
    funext q
    exact exec_bind member _ _ _
  unfold MeasFam
  rw [heq]
  exact Measurable.comp hh ((measurable_fst.prodMk hf.fst).prodMk hf.snd)

theorem MeasFam.bind' {f : A → TapeProgram n β} {h : A → β → TapeProgram n γ}
    (hf : MeasFam member f) (hh : MeasFam member fun q : A × β => h q.1 q.2) :
    MeasFam member fun a => f a >>= h a :=
  MeasFam.bind hf hh

/-- A membership call at a measurably chosen point. -/
theorem MeasFam.query (hm : Measurable member) {x : A → State n} (hx : Measurable x)
    {k : A × Bool → TapeProgram n β} (hk : MeasFam member k) :
    MeasFam member fun a => TapeProgram.query (x a) fun ans => k (a, ans) :=
  Measurable.comp hk ((measurable_fst.prodMk (hm.comp (hx.comp measurable_fst))).prodMk
    measurable_snd)

theorem MeasFam.bindIsMember (hm : Measurable member) {x : A → State n} (hx : Measurable x)
    {k : A → Bool → TapeProgram n β} (hk : MeasFam member fun q : A × Bool => k q.1 q.2) :
    MeasFam member fun a => TapeProgram.isMember (x a) >>= k a :=
  MeasFam.congr (MeasFam.query hm hx hk) fun _ => rfl

/-- Reading a component `π` of the next round. -/
private theorem MeasFam.read {X : Type} [MeasurableSpace X] (π : Round n → X)
    (hπ : Measurable π) {k : A × X → TapeProgram n β} (hk : MeasFam member k)
    {f : A → TapeProgram n β}
    (hf : ∀ a t, exec member (f a) t = exec member (k (a, π (t 0))) t.tail) :
    MeasFam member f := by
  have heq : (fun q : A × Tape n => exec member (f q.1) q.2) =
      fun q => exec member (k (q.1, π (q.2 0))) q.2.tail := by
    funext q
    exact hf _ _
  unfold MeasFam
  rw [heq]
  exact Measurable.comp hk ((measurable_fst.prodMk (hπ.comp ((measurable_pi_apply 0).comp
    measurable_snd))).prodMk (measurable_tape_tail.comp measurable_snd))

/-- A standard Gaussian vector. -/
theorem MeasFam.gaussian {k : A × State n → TapeProgram n β} (hk : MeasFam member k) :
    MeasFam member fun a => TapeProgram.gaussian fun g => k (a, g) :=
  MeasFam.read (fun r => r.1) measurable_fst hk fun _ _ => rfl

theorem MeasFam.bindGaussian {k : A → State n → TapeProgram n β}
    (hk : MeasFam member fun q : A × State n => k q.1 q.2) :
    MeasFam member fun a => TapeProgram.gaussianVector >>= k a :=
  MeasFam.congr (MeasFam.gaussian hk) fun _ => rfl

/-- A uniform number in `[0, 1]`. -/
theorem MeasFam.unit {k : A × ℝ → TapeProgram n β} (hk : MeasFam member k) :
    MeasFam member fun a => TapeProgram.unit fun v => k (a, v) :=
  MeasFam.read (fun r => r.2) measurable_snd hk fun _ _ => rfl

theorem MeasFam.bindUnit {k : A → ℝ → TapeProgram n β}
    (hk : MeasFam member fun q : A × ℝ => k q.1 q.2) :
    MeasFam member fun a => TapeProgram.unitNumber >>= k a :=
  MeasFam.congr (MeasFam.unit hk) fun _ => rfl

/-- A case split on a measurable condition. -/
theorem MeasFam.ite {P : A → Prop} [DecidablePred P] (hP : MeasurableSet {a | P a})
    {f g : A → TapeProgram n β} (hf : MeasFam member f) (hg : MeasFam member g) :
    MeasFam member fun a => if P a then f a else g a := by
  have heq : (fun q : A × Tape n => exec member (if P q.1 then f q.1 else g q.1) q.2) =
      fun q => if q.1 ∈ {a | P a} then exec member (f q.1) q.2
        else exec member (g q.1) q.2 := by
    funext q
    by_cases h : P q.1 <;> simp [h]
  unfold MeasFam
  rw [heq]
  exact Measurable.ite (measurable_fst hP) (f := fun q : A × Tape n =>
    exec member (f q.1) q.2) hf hg

/-- A family indexed by a countable discrete parameter runs measurably if each slice
does. -/
theorem MeasFam.of_slices {K : Type} [MeasurableSpace K] [Countable K]
    [MeasurableSingletonClass K] {f : K × A → TapeProgram n β}
    (h : ∀ k, MeasFam member fun a => f (k, a)) : MeasFam member f := by
  have hg : Measurable fun q : (A × Tape n) × K => exec member (f (q.2, q.1.1)) q.1.2 :=
    measurable_from_prod_countable_left fun k => h k
  exact hg.comp ((measurable_fst.snd.prodMk measurable_snd).prodMk measurable_fst.fst)

end TapeProgram

end ArlibCommunity.Algorithms.HitAndRun
