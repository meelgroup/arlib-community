/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.TrajTransfer

/-!
# The path-level time change: jump times, the counting process, and `ω t = Y (N t)`

`Arlib/MarkovChains/Continuous/TrajTransfer.lean` records, in its "What is not proved", item 1:

> **The time change itself is not proved.**  Nothing here constructs the jump chain
> `Y₀, Y₁, …` of accepted positions from a ball-walk path, nor the counting process `N t`, nor
> the identity `ω_t = Y_{N t}`. […] Assembling them into a path-level time change requires
> measurability of the successive jump times, which no file in this library has.

This file constructs all three and proves the identity, and it proves the measurability that
was named as the obstruction.  It also proves — and this is the point of the exercise — the
*first* genuinely trajectory-level cost statement: the expected number of ball-walk steps until
a proper step is made, read off a single path as its **first jump time**, is exactly
`(ell K δ x)⁻¹`.  Everything the repository proved before was a bound on a sum of per-step
conditional expectations.

**What is still missing is stated precisely in "What is not proved" below, and it is not this
file's construction: it is the strong Markov property for `Kernel.trajMeasure`, which Mathlib
does not have.**

## Main results

**The pathwise layer** (§§1–3; an arbitrary type `Om`, no measurable structure at all).

* `Arlib.MarkovChains.properCount` — the counting process `N t`: the number of *proper* steps
  (steps at which the path actually moves) among the first `t` steps of a path.  Honesty
  lemmas: `properCount_succ_of_ne` (a move adds exactly one), `properCount_succ_of_eq` (a hold
  adds nothing), `properCount_le_self` (`N t ≤ t`), `properCount_mono`.
* `Arlib.MarkovChains.jumpTime` — the jump times `T₀ < T₁ < ⋯`, `T k` being the first time by
  which `k` proper steps have been made.  Honesty lemmas: `properCount_jumpTime`
  (`N (T k) = k` exactly), `jumpTime_lt_jumpTime_succ` (strictly increasing),
  `le_jumpTime` (`k ≤ T k`), `jumpTime_zero`.
* `Arlib.MarkovChains.jumpChain` — the jump chain `Y k = ω (T k)`, the position after the
  `k`-th proper step.  Honesty lemma: `jumpChain_succ_ne` — consecutive values really differ,
  so this chain does jump.
* `Arlib.MarkovChains.jumpChain_properCount` — **the time change**, `ω t = Y (N t)`, for
  **every** path and every `t`, with no hypothesis of any kind.  Its content is
  `eq_of_properCount_eq`: a path is constant on any interval on which the counting process is.
* `Arlib.MarkovChains.jumpTime_eq_sum_sojourn` — `T k = ∑_{j<k} (T (j+1) − T j)`: the number
  of steps needed to realise `k` proper steps is the sum of the `k` sojourn lengths.
* `Arlib.MarkovChains.tsum_indicator_holdsUntil_eq_jumpTime_one` — the tail sum
  `∑ₖ 1[ω has not left x by time k]`, which is the integrand `TrajTransfer.lean` and
  `WastedSteps.lean` use for the exit time, **is** `jumpTime ω 1`, pointwise on every path
  that starts at `x` and eventually moves.  `tsum_indicator_holdsUntil_eq_top` covers the
  remaining paths (the tail sum is `⊤` there), so the two together cover every path.

**Measurability** (§4; `[MeasurableEq Om]`, Mathlib's "the diagonal is measurable", an
instance for every `StandardBorelSpace` and in particular for `EuclideanSpace ℝ (Fin n)`).
This is the item `TrajTransfer.lean` names as missing.

* `Arlib.MarkovChains.measurableSet_properStep` — "the path moved at step `i`" is an event.
* `Arlib.MarkovChains.measurable_properCount` — the counting process is measurable.
* `Arlib.MarkovChains.measurable_jumpTime` — **the jump times are measurable**.
* `Arlib.MarkovChains.measurable_jumpChain` — the jump chain is measurable (evaluation at a
  random index).
* `Arlib.MarkovChains.measurableSet_comap_frestrictLe_le_properCount` — the counting process is
  **adapted**: `{ω | k ≤ N m}` is `σ(ω₀, …, ω_m)`-measurable.  Since that event is `{T k ≤ m}`,
  this is the statement that the jump times are stopping times for the canonical filtration of
  the trajectory space.

**The ball walk** (§5).

* `Arlib.MarkovChains.pathMeasure_ballWalk_properStep` — the pathwise notion of a proper step
  is the ball walk's own notion of an accepted step: started at `x`, the probability that the
  first step is proper is exactly `ell K δ x`.
* `Arlib.MarkovChains.pathMeasure_ballWalk_never_moves` — if `ell K δ x ≠ 0` the paths that
  never move are null.
* `Arlib.MarkovChains.lintegral_jumpTime_one_pathMeasure_ballWalk` — **the headline**:

      ∫⁻ ω, (jumpTime ω 1) d(pathMeasure (ballWalk K δ) (dirac x))  =  (ell K δ x)⁻¹.

  Cousins–Vempala's "for any point `x`, the expected number of steps until a proper step is
  made is `1/ℓ(x)`" (`1409.6011/vol3_journal.tex:931`) with *the number of steps read off the
  trajectory*, not written as a tail sum of survival indicators.  Costs `MeasurableSet K`,
  `[NeZero n]` and `ell K δ x ≠ 0`; the last is not removable (at a stuck `x` the left side is
  `0` and the right side is `⊤`).

**Linearity of expectation** (§6).

* `Arlib.MarkovChains.lintegral_jumpTime_eq_sum_sojourn` — for any law `μ` on paths under
  which the path a.s. makes `t` proper steps,
  `E[T t] = ∑_{j<t} E[T (j+1) − T j]`.  This is the *shape* of Cousins–Vempala's
  linearity-of-expectation step (`vol3_journal.tex:937`); see "What is not proved" for the two
  reasons it is not yet that step.

**Non-vacuity** (§7).

* `Arlib.MarkovChains.exists_timeChange_path_witness` — two explicit paths, one with every step
  proper and one with exactly one proper step ever, on which `properCount`, `jumpTime` and
  `jumpChain` take proved non-trivial values, on which the time change holds (including *past*
  the last jump), and for which the linearity identity holds with **both sides equal to `t`**.
  It also exhibits the junk value: `jumpTime ω' 2 = 0`.
* `Arlib.MarkovChains.exists_timeChange_ballWalk_witness` — the unit ball with any `δ > 1` and
  its centre: `ell` is proved **strictly between `0` and `1`**, so the walk genuinely both
  moves and holds; the never-moving paths are null; and the mean first jump time is exactly
  `δⁿ`, **strictly greater than `1` and finite**.

## What is not proved

Read this before quoting anything above.

1. **The sojourn expectations are not identified with `∫ (ell K δ)⁻¹ dQ_j`.**
   `lintegral_jumpTime_eq_sum_sojourn` decomposes `E[T t]` into `t` sojourn expectations
   `E[T (j+1) − T j]`, and `lintegral_jumpTime_one_pathMeasure_ballWalk` evaluates the case
   `j = 0` from a deterministic start.  Evaluating the `j`-th summand needs the law of the
   ball-walk path *after* the stopping time `T j` given the past, i.e. the **strong Markov
   property** for `ProbabilityTheory.Kernel.trajMeasure`.  **Mathlib does not have it**: as of
   Mathlib v4.32 a search for `StrongMarkov` finds nothing anywhere in the library, and
   `Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean` contains no shift lemma and no
   stopping-time lemma at all — its strongest statements are at *deterministic* times
   (`traj_map_frestrictLe`, `partialTraj_compProd_traj`, `condDistrib_trajMeasure`,
   `condExp_traj`).  The missing lemma, precisely, is
   `(trajMeasure μ₀ κ).map (fun ω i => ω (τ ω + i)) = ... ` conditionally on `ℱ_τ` for a
   stopping time `τ` — equivalently a `Kernel.traj`-level Markov property at `τ`.  It would be
   needed **twice**: once here and once for item 3.
2. **The almost-sure hypothesis of `lintegral_jumpTime_eq_sum_sojourn` is not discharged for
   the ball walk.**  `hae : ∀ᵐ ω ∂μ, ∃ s, t ≤ properCount ω s` says the walk a.s. makes `t`
   proper steps.  For `t = 1` from a Dirac start this file proves it
   (`pathMeasure_ballWalk_never_moves`).  For `t ≥ 2` it needs "the walk a.s. does not get
   stuck forever", which is a Borel–Cantelli argument *along the trajectory*: it needs
   `P(the path holds for r consecutive steps from time m) ≤ (1 − c)^r` for a uniform
   `c ≤ ell K δ`, which in turn needs the conditional structure of the path at every time —
   `condDistrib_pathMeasure_ballWalk` — iterated.  That induction is not done here.
3. **The jump chain's law is not identified with the speedy walk.**  Nothing here proves
   `(pathMeasure (ballWalk K δ) μ).map (jumpChain · k) = iterate (speedyWalk K δ) μ k`, which
   is the other half of "the ball walk is the speedy walk time-changed".  Even the case
   `k = 1` from a Dirac start (`Y₁ ∼ speedyWalk K δ x`) is not proved, and iterating past it
   needs the same missing strong Markov property as item 1.
4. **Consequently `WastedSteps.lean`'s capstone is not restated as a trajectory statement.**
   `WastedSteps.lean`'s "What is *not* claimed", item 1, says its bound is a sum of per-step
   conditional expectations, not a functional of one trajectory.  That is still true.  What
   changed is the *summand*: it can now be read as an expected first jump time of a real path
   (`lintegral_jumpTime_one_pathMeasure_ballWalk`) rather than as a tail sum of survival
   indicators, and the decomposition the sum is supposed to represent is now a proved pathwise
   identity (`jumpTime_eq_sum_sojourn`).  The remaining gap is items 1–3, and only those.

## Conventions and the semantic-`def` audit

`CLAUDE.md` §11 asks for every `def` whose name promises a semantic identity to carry a
proving lemma.  This file introduces exactly three `def`s and no `structure`, `class` or named
`Prop`:

* `properCount` — "the number of proper steps": `properCount_succ_of_ne` and
  `properCount_succ_of_eq` prove it counts exactly the steps at which the path moves, and
  `pathMeasure_ballWalk_properStep` proves that for the ball walk this coincides with the
  walk's own acceptance probability `ell K δ x`.
* `jumpTime` — "the `k`-th jump time": `properCount_jumpTime` proves that exactly `k` proper
  steps have been made at it, `jumpTime_lt_jumpTime_succ` that these times increase strictly,
  and `tsum_indicator_holdsUntil_eq_jumpTime_one` that `jumpTime ω 1` is the exit time the rest
  of the repository integrates.
* `jumpChain` — "the jump chain": `jumpChain_succ_ne` proves it jumps at every index and
  `jumpChain_properCount` proves the time change `ω t = Y (N t)`.

**The junk value, stated once.**  `jumpTime ω k` is `Nat.sInf {t | k ≤ properCount ω t}`, and
`Nat.sInf ∅ = 0`, so on a path that never makes `k` proper steps `jumpTime ω k = 0`
(`jumpTime_eq_zero_of_not_exists`).  Every lemma that reads `jumpTime ω k` as a jump time
carries `∃ t, k ≤ properCount ω t`, and the ball-walk lemmas carry `ell K δ x ≠ 0`, which
makes the exceptional set null.  This is also why the adaptedness statement
`measurableSet_comap_frestrictLe_le_properCount` is phrased as the *event* `{k ≤ N m}` rather
than as `{jumpTime · k ≤ m}`: the latter also contains the never-jumping paths and is not an
`ℱ_m`-event.  The honest stopping time is the `ℕ∞`-valued one — which is also the type
`MeasureTheory.IsStoppingTime` takes — and `{k ≤ N m}` is exactly its `{T k ≤ m}`.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ## 1. Proper steps and the counting process, pathwise -/

section PathCombinatorics

variable {Om : Type*}

open scoped Classical in
/-- **The number of proper steps a path makes in its first `t` steps.**

A *proper* step of a path is one at which the path actually moves: the step from time `i` to
time `i + 1` is proper when `ω (i + 1) ≠ ω i`.  For the ball walk this is exactly the event
that the proposal was accepted — `pathMeasure_ballWalk_properStep` below proves that its
probability is exactly the local conductance `ell K δ x`, which is the ball walk's proper-step
probability by definition.

`properCount ω t` is Cousins–Vempala's counting process `N t`. -/
noncomputable def properCount (ω : ℕ → Om) : ℕ → ℕ
  | 0 => 0
  | (t + 1) => properCount ω t + (if ω (t + 1) = ω t then 0 else 1)

@[simp] theorem properCount_zero (ω : ℕ → Om) : properCount ω 0 = 0 := rfl

/-- A step that does not move does not increase the count. -/
theorem properCount_succ_of_eq {ω : ℕ → Om} {t : ℕ} (h : ω (t + 1) = ω t) :
    properCount ω (t + 1) = properCount ω t := by
  classical
  simp [properCount, h]

/-- A step that moves increases the count by exactly one. -/
theorem properCount_succ_of_ne {ω : ℕ → Om} {t : ℕ} (h : ω (t + 1) ≠ ω t) :
    properCount ω (t + 1) = properCount ω t + 1 := by
  classical
  simp [properCount, h]

theorem properCount_succ_eq_or (ω : ℕ → Om) (t : ℕ) :
    properCount ω (t + 1) = properCount ω t ∨
      properCount ω (t + 1) = properCount ω t + 1 := by
  by_cases h : ω (t + 1) = ω t
  · exact Or.inl (properCount_succ_of_eq h)
  · exact Or.inr (properCount_succ_of_ne h)

theorem properCount_le_succ (ω : ℕ → Om) (t : ℕ) :
    properCount ω t ≤ properCount ω (t + 1) := by
  rcases properCount_succ_eq_or ω t with h | h <;> omega

theorem properCount_succ_le (ω : ℕ → Om) (t : ℕ) :
    properCount ω (t + 1) ≤ properCount ω t + 1 := by
  rcases properCount_succ_eq_or ω t with h | h <;> omega

theorem properCount_mono (ω : ℕ → Om) : Monotone (properCount ω) :=
  monotone_nat_of_le_succ (properCount_le_succ ω)

/-- **A path cannot make more proper steps than it takes steps.** -/
theorem properCount_le_self (ω : ℕ → Om) (t : ℕ) : properCount ω t ≤ t := by
  induction t with
  | zero => simp
  | succ t ih => exact (properCount_succ_le ω t).trans (Nat.succ_le_succ ih)

/-- **The counting process reads only the coordinates it counts.**  `properCount ω t` depends
on `ω 0, …, ω t` only.  This is the pathwise content of "the counting process is adapted";
its `σ`-algebra form is `measurableSet_comap_frestrictLe_le_properCount`. -/
theorem properCount_congr {ω ω' : ℕ → Om} {t : ℕ} (h : ∀ i ≤ t, ω i = ω' i) :
    properCount ω t = properCount ω' t := by
  induction t with
  | zero => simp
  | succ t ih =>
      have ht : ∀ i ≤ t, ω i = ω' i := fun i hi => h i (hi.trans (Nat.le_succ t))
      have h1 : ω (t + 1) = ω' (t + 1) := h (t + 1) le_rfl
      have h2 : ω t = ω' t := h t (Nat.le_succ t)
      by_cases hs : ω (t + 1) = ω t
      · rw [properCount_succ_of_eq hs, properCount_succ_of_eq (by rw [← h1, ← h2]; exact hs),
          ih ht]
      · rw [properCount_succ_of_ne hs, properCount_succ_of_ne (by rw [← h1, ← h2]; exact hs),
          ih ht]

/-- **The crux of the time change, pathwise: a path is constant between proper steps.**

If no proper step occurs between times `a` and `b` — that is, if the counting process takes
the same value at both — then the path itself takes the same value at both.  This is what
makes `ω t = Y (N t)` true. -/
theorem eq_of_properCount_eq {ω : ℕ → Om} {a b : ℕ} (hab : a ≤ b)
    (h : properCount ω a = properCount ω b) : ω a = ω b := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
      have hmono : properCount ω b ≤ properCount ω (b + 1) := properCount_le_succ ω b
      have hab' : properCount ω a ≤ properCount ω b := properCount_mono ω hab
      have hb : properCount ω a = properCount ω b := le_antisymm hab' (by rw [h]; exact hmono)
      have hstep : ω (b + 1) = ω b := by
        by_contra hne
        rw [properCount_succ_of_ne hne] at h
        omega
      rw [hstep]
      exact ih hb

/-! ## 2. The jump times -/

/-- **The `k`-th jump time of a path**: the first time by which `k` proper steps have been
made.  `jumpTime ω 0 = 0`, and `jumpTime ω (k + 1)` is the time index at which the `(k+1)`-st
proper step lands.

*The junk value.*  If the path never makes `k` proper steps the defining set is empty and
`Nat.sInf` returns `0`; `jumpTime_eq_zero_of_not_exists` records this.  Every statement below
that reads `jumpTime ω k` as "the `k`-th jump time" carries the hypothesis
`∃ t, k ≤ properCount ω t` that rules the junk value out.  What the junk value costs is
recorded in the module docstring: it is why the *event* form
`measurableSet_comap_frestrictLe_le_properCount` — and not `jumpTime` itself — is the
stopping-time statement. -/
noncomputable def jumpTime (ω : ℕ → Om) (k : ℕ) : ℕ := sInf {t | k ≤ properCount ω t}

theorem jumpTime_le {ω : ℕ → Om} {k t : ℕ} (h : k ≤ properCount ω t) : jumpTime ω k ≤ t :=
  Nat.sInf_le (s := {t | k ≤ properCount ω t}) h

/-- **Before the `k`-th jump time, fewer than `k` proper steps have been made.** -/
theorem properCount_lt_of_lt_jumpTime {ω : ℕ → Om} {k j : ℕ} (h : j < jumpTime ω k) :
    properCount ω j < k := by
  have hj : j ∉ {t | k ≤ properCount ω t} :=
    Nat.notMem_of_lt_sInf (s := {t | k ≤ properCount ω t}) h
  simpa [Set.mem_setOf_eq] using hj

/-- **At the `k`-th jump time, at least `k` proper steps have been made.**  Needs the `k`-th
jump to exist. -/
theorem le_properCount_jumpTime {ω : ℕ → Om} {k : ℕ} (h : ∃ t, k ≤ properCount ω t) :
    k ≤ properCount ω (jumpTime ω k) :=
  Nat.sInf_mem (s := {t | k ≤ properCount ω t}) h

@[simp] theorem jumpTime_zero (ω : ℕ → Om) : jumpTime ω 0 = 0 :=
  Nat.le_zero.1 (jumpTime_le (by simp))

theorem jumpTime_eq_zero_of_not_exists {ω : ℕ → Om} {k : ℕ}
    (h : ¬ ∃ t, k ≤ properCount ω t) : jumpTime ω k = 0 := by
  have : {t | k ≤ properCount ω t} = (∅ : Set ℕ) := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun ht => h ⟨t, ht⟩
  rw [jumpTime, this, Nat.sInf_empty]

/-- **At its `k`-th jump time a path has made exactly `k` proper steps.**  This is the lemma
that makes the name `jumpTime` honest. -/
theorem properCount_jumpTime {ω : ℕ → Om} {k : ℕ} (h : ∃ t, k ≤ properCount ω t) :
    properCount ω (jumpTime ω k) = k := by
  have hmem : k ≤ properCount ω (jumpTime ω k) := le_properCount_jumpTime h
  rcases Nat.eq_zero_or_pos (jumpTime ω k) with hz | hpos
  · rw [hz] at hmem ⊢
    simp only [properCount_zero] at hmem ⊢
    omega
  · obtain ⟨j, hj⟩ : ∃ j, jumpTime ω k = j + 1 := ⟨jumpTime ω k - 1, by omega⟩
    have hlt : properCount ω j < k := properCount_lt_of_lt_jumpTime (by omega)
    have hle : properCount ω (j + 1) ≤ properCount ω j + 1 := properCount_succ_le ω j
    rw [hj] at hmem ⊢
    omega

/-- **`k` proper steps take at least `k` steps.** -/
theorem le_jumpTime {ω : ℕ → Om} {k : ℕ} (h : ∃ t, k ≤ properCount ω t) : k ≤ jumpTime ω k := by
  have := properCount_jumpTime h
  have hle := properCount_le_self ω (jumpTime ω k)
  omega

theorem exists_of_succ {ω : ℕ → Om} {k : ℕ} (h : ∃ t, k + 1 ≤ properCount ω t) :
    ∃ t, k ≤ properCount ω t := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, by omega⟩

/-- **The jump times are strictly increasing** (as far as the path makes jumps). -/
theorem jumpTime_lt_jumpTime_succ {ω : ℕ → Om} {k : ℕ} (h : ∃ t, k + 1 ≤ properCount ω t) :
    jumpTime ω k < jumpTime ω (k + 1) := by
  have h1 : properCount ω (jumpTime ω (k + 1)) = k + 1 := properCount_jumpTime h
  have h0 : properCount ω (jumpTime ω k) = k := properCount_jumpTime (exists_of_succ h)
  have hle : jumpTime ω k ≤ jumpTime ω (k + 1) := jumpTime_le (by omega)
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · rw [heq] at h0; omega

/-! ## 3. The jump chain and the time change -/

/-- **The jump chain of a path**: `jumpChain ω k` is the position of the path after its `k`-th
proper step.  `jumpChain ω 0 = ω 0`, and `jumpChain_succ_ne` proves that consecutive values
really are different, i.e. that this chain does jump. -/
noncomputable def jumpChain (ω : ℕ → Om) (k : ℕ) : Om := ω (jumpTime ω k)

@[simp] theorem jumpChain_zero (ω : ℕ → Om) : jumpChain ω 0 = ω 0 := by
  rw [jumpChain, jumpTime_zero]

theorem jumpChain_apply (ω : ℕ → Om) (k : ℕ) : jumpChain ω k = ω (jumpTime ω k) := rfl

/-- **The jump chain genuinely jumps**: consecutive positions of the jump chain differ. -/
theorem jumpChain_succ_ne {ω : ℕ → Om} {k : ℕ} (h : ∃ t, k + 1 ≤ properCount ω t) :
    jumpChain ω (k + 1) ≠ jumpChain ω k := by
  have hlt : jumpTime ω k < jumpTime ω (k + 1) := jumpTime_lt_jumpTime_succ h
  obtain ⟨j, hj⟩ : ∃ j, jumpTime ω (k + 1) = j + 1 := ⟨jumpTime ω (k + 1) - 1, by omega⟩
  have h1 : properCount ω (j + 1) = k + 1 := by rw [← hj]; exact properCount_jumpTime h
  have h0 : properCount ω (jumpTime ω k) = k := properCount_jumpTime (exists_of_succ h)
  have hjk : jumpTime ω k ≤ j := by omega
  have hnot : properCount ω j < k + 1 := properCount_lt_of_lt_jumpTime (by omega)
  have hmono : properCount ω (jumpTime ω k) ≤ properCount ω j := properCount_mono ω hjk
  have hjcount : properCount ω j = k := by omega
  have hstep : ω (j + 1) ≠ ω j := by
    intro hcon
    rw [properCount_succ_of_eq hcon, hjcount] at h1
    omega
  have hconst : ω (jumpTime ω k) = ω j := eq_of_properCount_eq hjk (by rw [h0, hjcount])
  rw [jumpChain_apply, jumpChain_apply, hj, hconst]
  exact hstep

/-- **The path-level time change**: `ω t = Y (N t)`.

At every time `t`, the position of the path equals the position of its jump chain at index
`properCount ω t` — the number of proper steps made so far.  This holds for **every** path,
with no hypothesis whatsoever: it is the pointwise identity that Cousins–Vempala treat as
definitional when they pass from the speedy walk to the ball walk. -/
theorem jumpChain_properCount (ω : ℕ → Om) (t : ℕ) :
    jumpChain ω (properCount ω t) = ω t := by
  have hle : jumpTime ω (properCount ω t) ≤ t := jumpTime_le le_rfl
  have heq : properCount ω (jumpTime ω (properCount ω t)) = properCount ω t :=
    properCount_jumpTime ⟨t, le_rfl⟩
  exact eq_of_properCount_eq hle heq

/-- **The jump time decomposes into sojourn lengths.**  The number of steps a path takes to
make `k` proper steps is the sum of the lengths of its first `k` sojourns.  This is the
pathwise skeleton of Cousins–Vempala's "by linearity of expectation" step; see the module
docstring for exactly what is still needed to take expectations of it. -/
theorem jumpTime_eq_sum_sojourn {ω : ℕ → Om} {k : ℕ} (h : ∃ t, k ≤ properCount ω t) :
    jumpTime ω k = ∑ j ∈ Finset.range k, (jumpTime ω (j + 1) - jumpTime ω j) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk : ∃ t, k ≤ properCount ω t := exists_of_succ h
      have hlt : jumpTime ω k < jumpTime ω (k + 1) := jumpTime_lt_jumpTime_succ h
      rw [Finset.sum_range_succ, ← ih hk]
      omega

/-- **The path has not moved off `ω 0` before its first jump.** -/
theorem eq_zero_of_lt_jumpTime_one {ω : ℕ → Om} {i : ℕ} (h : i < jumpTime ω 1) :
    ω i = ω 0 := by
  have h0 : properCount ω i = 0 := by
    have := properCount_lt_of_lt_jumpTime h
    omega
  exact (eq_of_properCount_eq (Nat.zero_le i) (by rw [properCount_zero, h0])).symm

/-- **The path has moved off `ω 0` at its first jump.** -/
theorem ne_of_jumpTime_one {ω : ℕ → Om} (h : ∃ t, 1 ≤ properCount ω t) :
    ω (jumpTime ω 1) ≠ ω 0 := by
  have hne := jumpChain_succ_ne (k := 0) (by simpa using h)
  rw [jumpChain_apply, jumpChain_zero] at hne
  simpa using hne

/-- **The first jump time *is* the exit time, pointwise on paths.**

`TrajTransfer.lean` computes the mean of the exit time of the ball walk from `x` in its
tail-sum form `∑ₖ 1[ω has not left x by time k]`, and `WastedSteps.lean` integrates exactly
that expression.  This lemma identifies that expression, on every path that starts at `x` and
eventually moves, with `jumpTime ω 1` — the honest first jump time of the path.

No measure and no measurable structure is involved: this is an identity between two functions
of a single path. -/
theorem tsum_indicator_holdsUntil_eq_jumpTime_one {ω : ℕ → Om} {x : Om} (hx : ω 0 = x)
    (h : ∃ t, 1 ≤ properCount ω t) :
    (∑' k : ℕ, {ω' : ℕ → Om | ∀ i ≤ k, ω' i = x}.indicator (1 : (ℕ → Om) → ℝ≥0∞) ω)
      = (jumpTime ω 1 : ℝ≥0∞) := by
  have hmem : ∀ k : ℕ, (ω ∈ {ω' : ℕ → Om | ∀ i ≤ k, ω' i = x}) ↔ k < jumpTime ω 1 := by
    intro k
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hk
      by_contra hcon
      exact ne_of_jumpTime_one h ((hk _ (not_lt.1 hcon)).trans hx.symm)
    · intro hk i hi
      rw [eq_zero_of_lt_jumpTime_one (lt_of_le_of_lt hi hk), hx]
  rw [tsum_eq_sum (s := Finset.range (jumpTime ω 1)) fun k hk => ?_]
  · rw [Finset.sum_congr rfl fun k hk => Set.indicator_of_mem
      ((hmem k).2 (Finset.mem_range.1 hk)) _]
    simp
  · exact Set.indicator_of_notMem (fun hcon =>
      hk (Finset.mem_range.2 ((hmem k).1 hcon))) _

/-- **A path that never moves has infinite exit time**, so the tail sum
`WastedSteps.lean` integrates is `⊤` exactly on the paths where `jumpTime ω 1` is a junk
value.  Together with `tsum_indicator_holdsUntil_eq_jumpTime_one` this covers every path. -/
theorem tsum_indicator_holdsUntil_eq_top {ω : ℕ → Om} {x : Om} (hx : ω 0 = x)
    (h : ¬ ∃ t, 1 ≤ properCount ω t) :
    (∑' k : ℕ, {ω' : ℕ → Om | ∀ i ≤ k, ω' i = x}.indicator (1 : (ℕ → Om) → ℝ≥0∞) ω) = ⊤ := by
  have h' : ∀ t, properCount ω t = 0 := fun t => by
    by_contra hc
    exact h ⟨t, by omega⟩
  have hall : ∀ k : ℕ, ω ∈ {ω' : ℕ → Om | ∀ i ≤ k, ω' i = x} := by
    intro k i _
    have h0 : properCount ω i = 0 := h' i
    rw [← hx]
    exact (eq_of_properCount_eq (Nat.zero_le i) (by rw [properCount_zero, h0])).symm
  have : ∀ k : ℕ, {ω' : ℕ → Om | ∀ i ≤ k, ω' i = x}.indicator
      (1 : (ℕ → Om) → ℝ≥0∞) ω = 1 := fun k => by
    rw [Set.indicator_of_mem (hall k)]; rfl
  simp_rw [this]
  exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero

end PathCombinatorics

/-! ## 4. Measurability: the crux

`TrajTransfer.lean`'s "What is not proved", item 1, names the obstruction:

> Assembling them into a path-level time change requires measurability of the successive jump
> times, which no file in this library has.

This section supplies it.  The hypothesis is `[MeasurableEq Om]` — Mathlib's class asserting
that the diagonal of `Om × Om` is measurable, which is what makes "the path moved at step `i`"
an event at all.  It is an instance for every `StandardBorelSpace`, in particular for
`EuclideanSpace ℝ (Fin n)`, and it implies `MeasurableSingletonClass`. -/

section Measurability

variable {Om : Type*} [MeasurableSpace Om] [MeasurableEq Om]

/-- **"The path moves at step `i`" is an event.** -/
theorem measurableSet_properStep (i : ℕ) :
    MeasurableSet {ω : ℕ → Om | ω (i + 1) ≠ ω i} := by
  have h : {ω : ℕ → Om | ω (i + 1) ≠ ω i} = {ω : ℕ → Om | ω (i + 1) = ω i}ᶜ := by
    ext ω; simp
  rw [h]
  exact (measurableSet_eq_fun (measurable_pi_apply (i + 1)) (measurable_pi_apply i)).compl

omit [MeasurableSpace Om] [MeasurableEq Om] in
/-- The counting process, as a sum of indicators of the proper-step events. -/
theorem properCount_succ_eq_add_indicator (ω : ℕ → Om) (t : ℕ) :
    properCount ω (t + 1)
      = properCount ω t + {ω' : ℕ → Om | ω' (t + 1) ≠ ω' t}.indicator (fun _ => 1) ω := by
  by_cases h : ω (t + 1) = ω t
  · rw [properCount_succ_of_eq h, Set.indicator_of_notMem (by simpa using h), add_zero]
  · rw [properCount_succ_of_ne h, Set.indicator_of_mem h]

/-- **The counting process is measurable.** -/
theorem measurable_properCount (t : ℕ) : Measurable fun ω : ℕ → Om => properCount ω t := by
  induction t with
  | zero => simp
  | succ t ih =>
      simp only [properCount_succ_eq_add_indicator]
      exact ih.add (measurable_const.indicator (measurableSet_properStep t))

/-- "At least `k` proper steps have been made by time `t`" is an event. -/
theorem measurableSet_le_properCount (k t : ℕ) :
    MeasurableSet {ω : ℕ → Om | k ≤ properCount ω t} :=
  (measurable_properCount t) (MeasurableSet.of_discrete (s := {c : ℕ | k ≤ c}))

/-- **The jump times are measurable.**  This is the result `TrajTransfer.lean` records as
missing.

The proof is the fibre computation for `Nat.sInf`: the defining set
`{t | k ≤ properCount ω t}` is upward closed, so `Nat.sInf_upward_closed_eq_succ_iff` turns
`jumpTime ω k = j + 1` into the intersection of two events, and `Nat.sInf_eq_zero` turns
`jumpTime ω k = 0` into a union of an event with the (countably described) event that the
path never makes `k` proper steps. -/
theorem measurable_jumpTime (k : ℕ) : Measurable fun ω : ℕ → Om => jumpTime ω k := by
  have hup : ∀ ω : ℕ → Om, ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ →
      k₁ ∈ {t | k ≤ properCount ω t} → k₂ ∈ {t | k ≤ properCount ω t} := by
    intro ω k₁ k₂ hk hmem
    exact le_trans hmem (properCount_mono ω hk)
  refine measurable_to_countable' fun m => ?_
  match m with
  | 0 =>
      have hset : (fun ω : ℕ → Om => jumpTime ω k) ⁻¹' {0}
          = {ω : ℕ → Om | k ≤ properCount ω 0} ∪
            ⋂ t : ℕ, {ω : ℕ → Om | k ≤ properCount ω t}ᶜ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_iInter, Set.mem_compl_iff, jumpTime]
        rw [Nat.sInf_eq_zero]
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr fun t ht => (Set.eq_empty_iff_forall_notMem.1 h t) ht
        · rintro (h | h)
          · exact Or.inl h
          · refine Or.inr (Set.eq_empty_iff_forall_notMem.2 fun t ht => h t ht)
      rw [hset]
      exact (measurableSet_le_properCount k 0).union
        (MeasurableSet.iInter fun t => (measurableSet_le_properCount k t).compl)
  | (j + 1) =>
      have hset : (fun ω : ℕ → Om => jumpTime ω k) ⁻¹' {j + 1}
          = {ω : ℕ → Om | k ≤ properCount ω (j + 1)} ∩
            {ω : ℕ → Om | k ≤ properCount ω j}ᶜ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_setOf_eq,
          Set.mem_compl_iff, jumpTime]
        exact Nat.sInf_upward_closed_eq_succ_iff (hup ω) j
      rw [hset]
      exact (measurableSet_le_properCount k (j + 1)).inter
        (measurableSet_le_properCount k j).compl

/-- **The jump chain is measurable.**  Evaluation of the path at the *random* index
`jumpTime ω k`; measurable because the index is measurable and takes countably many values. -/
theorem measurable_jumpChain (k : ℕ) : Measurable fun ω : ℕ → Om => jumpChain ω k := by
  have h : (fun ω : ℕ → Om => jumpChain ω k)
      = (fun p : ℕ × (ℕ → Om) => p.2 p.1) ∘ fun ω : ℕ → Om => (jumpTime ω k, ω) := rfl
  rw [h]
  exact (measurable_from_prod_countable_right fun m => measurable_pi_apply m).comp
    ((measurable_jumpTime k).prodMk measurable_id)

/-- **The counting process is adapted, and the jump times are stopping times.**

The event "at least `k` proper steps have been made by time `m`" is measurable with respect to
`σ(ω₀, …, ω_m)` — the `σ`-algebra `Kernel.traj`'s filtration is built from
(`MeasurableSpace.comap (Preorder.frestrictLe m)`).  Since that event *is* `{T_k ≤ m}` for the
`k`-th jump time, this is the statement that the jump times are stopping times for the
canonical filtration of the trajectory space.

It is stated in event form rather than as `jumpTime ω k ≤ m` because of the junk value: on
paths that never make `k` proper steps `jumpTime ω k = 0`, and `{jumpTime · k ≤ m}` then also
contains those paths, which is not an `ℱ_m`-event.  The event form is the honest one — it is
`{T_k ≤ m}` for the `ℕ∞`-valued jump time. -/
theorem measurableSet_comap_frestrictLe_le_properCount (k m : ℕ) :
    MeasurableSet[MeasurableSpace.comap (Preorder.frestrictLe (π := fun _ : ℕ => Om) m)
        inferInstance]
      {ω : ℕ → Om | k ≤ properCount ω m} := by
  -- extend a history `(ω₀, …, ω_m)` to a path by freezing it at time `m`
  set e : ((_i : ↥(Finset.Iic m)) → Om) → (ℕ → Om) :=
    fun h i => h ⟨min i m, Finset.mem_Iic.2 (min_le_right _ _)⟩ with he
  have hemeas : Measurable e :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hcoord : ∀ ω : ℕ → Om, ∀ i ≤ m, e (Preorder.frestrictLe m ω) i = ω i := by
    intro ω i hi
    simp only [he, Preorder.frestrictLe_apply, Nat.min_eq_left hi]
  refine ⟨{h | k ≤ properCount (e h) m}, ?_, ?_⟩
  · exact (((measurable_properCount m).comp hemeas)) (MeasurableSet.of_discrete (s := {c | k ≤ c}))
  · ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [properCount_congr (fun i hi => (hcoord ω i hi).symm)]

end Measurability

/-! ## 5. The ball walk: the pathwise proper step is the accepted step

Sections 1–4 are about arbitrary paths.  This section connects them to the ball walk, and in
particular checks that "the path moved" — the pathwise notion of a proper step used above — is
the ball walk's own notion of an accepted step: its probability at `x` is exactly the local
conductance `ell K δ x`. -/

section BallWalk

variable {n : ℕ}

/-- **The probability that the ball walk's first step is proper is exactly `ell K δ x`.**

The pathwise definition of a proper step — the path moved — is therefore the ball walk's own
notion of an accepted step, whose probability is `ell K δ x` by
`ballWalk_apply_compl_singleton`.  Assumes `MeasurableSet K` and `[NeZero n]`, both inherited
from that lemma. -/
theorem pathMeasure_ballWalk_properStep [NeZero n] {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    pathMeasure (ballWalk K δ) (Measure.dirac x)
        {ω : ℕ → EuclideanSpace ℝ (Fin n) | ω 1 ≠ ω 0} = ell K δ x := by
  set mu := pathMeasure (ballWalk K δ) (Measure.dirac x) with hmu
  -- the walk starts at `x`, almost surely
  have hzero : mu {ω : ℕ → EuclideanSpace ℝ (Fin n) | ω 0 ≠ x} = 0 := by
    have h : mu {ω : ℕ → EuclideanSpace ℝ (Fin n) | ω 0 ≠ x}
        = (mu.map fun ω => ω 0) ({x}ᶜ : Set (EuclideanSpace ℝ (Fin n))) := by
      rw [Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton x).compl]
      rfl
    rw [h, hmu, map_eval_pathMeasure_zero]
    simp
  -- the law at time one is `ballWalk K δ x`
  have hone : mu {ω : ℕ → EuclideanSpace ℝ (Fin n) | ω 1 ≠ x} = ell K δ x := by
    have h : mu {ω : ℕ → EuclideanSpace ℝ (Fin n) | ω 1 ≠ x}
        = (mu.map fun ω => ω 1) ({x}ᶜ : Set (EuclideanSpace ℝ (Fin n))) := by
      rw [Measure.map_apply (measurable_pi_apply 1) (measurableSet_singleton x).compl]
      rfl
    rw [h, hmu, show (1 : ℕ) = 0 + 1 from rfl, map_eval_pathMeasure_succ,
      map_eval_pathMeasure_zero, Measure.dirac_bind (Kernel.measurable _),
      ballWalk_apply_compl_singleton hK]
  -- the two events differ only inside the null event `ω 0 ≠ x`
  refine hone ▸ measure_congr ?_
  refine measure_symmDiff_eq_zero_iff.1 (measure_mono_null (fun ω hω => ?_) hzero)
  simp only [Set.mem_symmDiff, Set.mem_setOf_eq] at hω
  simp only [Set.mem_setOf_eq]
  intro hcon
  rcases hω with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact h1 (by rw [not_not.1 h2, hcon])

/-- **The paths that never move are null**, as soon as the local conductance at the start is
non-zero.  This is what makes the junk value of `jumpTime` invisible to the ball walk's law.

Assumes `MeasurableSet K`, `[NeZero n]` and `ell K δ x ≠ 0`.  All three are necessary: at a
stuck `x` the ball walk really never moves and this set has full measure. -/
theorem pathMeasure_ballWalk_never_moves [NeZero n] {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ : ℝ) (x : EuclideanSpace ℝ (Fin n)) (hell : ell K δ x ≠ 0) :
    pathMeasure (ballWalk K δ) (Measure.dirac x)
      (⋂ k : ℕ, {ω : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω i = x}) = 0 := by
  set mu := pathMeasure (ballWalk K δ) (Measure.dirac x) with hmu
  set Z := ⋂ k : ℕ, {ω : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω i = x} with hZ
  by_contra hne
  have hle : ∀ k : ℕ, mu Z ≤ mu {ω : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω i = x} :=
    fun k => measure_mono (Set.iInter_subset _ k)
  have hsum : ∑' _k : ℕ, mu Z ≤ (ell K δ x)⁻¹ := by
    calc ∑' _k : ℕ, mu Z
        ≤ ∑' k : ℕ, mu {ω : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω i = x} :=
          ENNReal.tsum_le_tsum hle
      _ = (ell K δ x)⁻¹ := tsum_pathMeasure_ballWalk_dirac_holdsUntil hK δ x
  rw [ENNReal.tsum_const_eq_top_of_ne_zero hne] at hsum
  exact (ENNReal.inv_ne_top.2 hell) (top_le_iff.1 hsum)

/-- **The mean first jump time of the ball walk at `x` is exactly `(ell K δ x)⁻¹`.**

This is `lintegral_exitTime_pathMeasure_ballWalk` (`TrajTransfer.lean`) with the tail-sum
expression replaced by the *first jump time of the path* — a single, honest functional of the
trajectory rather than a sum of survival indicators.  It is the statement
"from `x`, the expected number of ball-walk steps until a proper step is made is `1/ℓ(x)`"
(`vol3_journal.tex:931`) with "number of steps until a proper step is made" *defined on the
path*.

Assumes `MeasurableSet K`, `[NeZero n]` and `ell K δ x ≠ 0`.  The last hypothesis is not
removable and is not a technicality: at a stuck `x` the walk never moves, `jumpTime ω 1` is
the junk value `0` on every path, so the left side is `0` while the right side is `⊤`. -/
theorem lintegral_jumpTime_one_pathMeasure_ballWalk [NeZero n]
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (δ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (hell : ell K δ x ≠ 0) :
    ∫⁻ ω, (jumpTime ω 1 : ℝ≥0∞) ∂(pathMeasure (ballWalk K δ) (Measure.dirac x))
      = (ell K δ x)⁻¹ := by
  set mu := pathMeasure (ballWalk K δ) (Measure.dirac x) with hmu
  have hzero : mu {ω : ℕ → EuclideanSpace ℝ (Fin n) | ω 0 ≠ x} = 0 := by
    have h : mu {ω : ℕ → EuclideanSpace ℝ (Fin n) | ω 0 ≠ x}
        = (mu.map fun ω => ω 0) ({x}ᶜ : Set (EuclideanSpace ℝ (Fin n))) := by
      rw [Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton x).compl]
      rfl
    rw [h, hmu, map_eval_pathMeasure_zero]
    simp
  have hae0 : ∀ᵐ ω ∂mu, ω 0 = x := by
    rw [ae_iff]
    exact hzero
  have haeZ : ∀ᵐ ω ∂mu, ω ∉ ⋂ k : ℕ, {ω' : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω' i = x} :=
    measure_eq_zero_iff_ae_notMem.1 (pathMeasure_ballWalk_never_moves hK δ x hell)
  have hcongr : ∀ᵐ ω ∂mu, (jumpTime ω 1 : ℝ≥0∞)
      = ∑' k : ℕ, {ω' : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω' i = x}.indicator
          (1 : (ℕ → EuclideanSpace ℝ (Fin n)) → ℝ≥0∞) ω := by
    filter_upwards [hae0, haeZ] with ω h0 hZ
    have hex : ∃ t, 1 ≤ properCount ω t := by
      by_contra hcon
      refine hZ (Set.mem_iInter.2 fun k => ?_)
      have h' : ∀ t, properCount ω t = 0 := fun t => by
        by_contra hc
        exact hcon ⟨t, by omega⟩
      intro i _
      rw [← h0]
      exact (eq_of_properCount_eq (Nat.zero_le i) (by rw [properCount_zero, h' i])).symm
    exact (tsum_indicator_holdsUntil_eq_jumpTime_one h0 hex).symm
  rw [lintegral_congr_ae hcongr, hmu, lintegral_exitTime_pathMeasure_ballWalk hK δ x]

end BallWalk

/-! ## 6. Linearity of expectation, at path level

Cousins–Vempala's last sentence — "if the speedy walk took `t` steps, then by linearity of
expectation, the expected number of steps for the ball walk is at most `Mt/λ`"
(`vol3_journal.tex:937`) — is the statement that the number of ball-walk steps needed to
realise `t` proper steps splits as a sum of `t` sojourn lengths and that expectation
distributes over that sum.  The splitting is `jumpTime_eq_sum_sojourn`, pathwise; this section
integrates it.  What is **not** here is the identification of the `j`-th summand with
`∫ (ell)⁻¹ dQ_j`; see the module docstring. -/

section Expectation

variable {Om : Type*} [MeasurableSpace Om] [MeasurableEq Om]

/-- "The path eventually makes `t` proper steps" is an event. -/
theorem measurableSet_exists_le_properCount (t : ℕ) :
    MeasurableSet {ω : ℕ → Om | ∃ s, t ≤ properCount ω s} := by
  have h : {ω : ℕ → Om | ∃ s, t ≤ properCount ω s}
      = ⋃ s : ℕ, {ω : ℕ → Om | t ≤ properCount ω s} := by
    ext ω; simp
  rw [h]
  exact MeasurableSet.iUnion fun s => measurableSet_le_properCount t s

/-- The `j`-th sojourn length `T_{j+1} - T_j` is measurable. -/
theorem measurable_sojourn (j : ℕ) :
    Measurable fun ω : ℕ → Om => ((jumpTime ω (j + 1) - jumpTime ω j : ℕ) : ℝ≥0∞) := by
  have h1 : Measurable fun ω : ℕ → Om => (jumpTime ω (j + 1) - jumpTime ω j : ℕ) :=
    (Measurable.of_discrete (f := fun p : ℕ × ℕ => p.1 - p.2)).comp
      ((measurable_jumpTime (j + 1)).prodMk (measurable_jumpTime j))
  exact (Measurable.of_discrete (f := fun c : ℕ => (c : ℝ≥0∞))).comp h1

/-- **Linearity of expectation for the time change.**  For any law `μ` on paths under which
the path almost surely makes `t` proper steps, the expected number of steps needed to realise
those `t` proper steps is the sum of the `t` expected sojourn lengths:

    E[T_t] = ∑_{j<t} E[T_{j+1} - T_j].

Both sides are honest functionals of the path, and no property of `μ` beyond the stated
almost-sure hypothesis is used — `μ` need not be a probability measure, a trajectory measure,
or Markov.

This is the shape of Cousins–Vempala's linearity-of-expectation step.  Turning the `j`-th
summand into `∫ (ell K δ)⁻¹ dQ_j` — the form `WastedSteps.lean` bounds — is a *different*
statement, and it is the one that is still missing: see the module docstring. -/
theorem lintegral_jumpTime_eq_sum_sojourn (μ : Measure (ℕ → Om)) {t : ℕ}
    (hae : ∀ᵐ ω ∂μ, ∃ s, t ≤ properCount ω s) :
    ∫⁻ ω, (jumpTime ω t : ℝ≥0∞) ∂μ
      = ∑ j ∈ Finset.range t, ∫⁻ ω, ((jumpTime ω (j + 1) - jumpTime ω j : ℕ) : ℝ≥0∞) ∂μ := by
  rw [← lintegral_finsetSum _ fun j _ => measurable_sojourn j]
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with ω h
  rw [jumpTime_eq_sum_sojourn h, Nat.cast_sum]

end Expectation

/-! ## 7. Non-vacuity

`CLAUDE.md` §11: definitions and theorems that are never non-degenerately instantiated
certify nothing.  Two witnesses: one for the pathwise layer (§§1–3, 6) and one for the ball
walk (§5). -/

section Witness

/-- **The pathwise witness.**  For every `t`, the path `ω i = i` in `ℕ → ℕ` — every step
proper — and the path `ω' i = min i 1` — exactly one proper step, ever — satisfy:

* `properCount` is *not* identically zero: it is `t` along `ω` and `min t 1` along `ω'`;
* `jumpTime` is *not* identically zero: it is `k` along `ω`, and `1` at `k = 1` along `ω'`;
* the junk value is real and is exactly where the docstring says it is: `jumpTime ω' 2 = 0`,
  because `ω'` never makes two proper steps;
* the time change `jumpChain ω (properCount ω t) = ω t` holds along both paths — along `ω'`
  it holds *past* the last jump, which is the case the identity is for;
* the jump chain genuinely moves along `ω`;
* the linearity identity `lintegral_jumpTime_eq_sum_sojourn` holds for the law `dirac ω`, with
  **both sides equal to `t`** — non-zero for `t ≥ 1`, and finite. -/
theorem exists_timeChange_path_witness (t : ℕ) :
    ∃ ω ω' : ℕ → ℕ,
      (∀ s, properCount ω s = s) ∧
      (∀ k, jumpTime ω k = k) ∧
      (∀ k, jumpChain ω k = k) ∧
      (∀ s, properCount ω' s = min s 1) ∧
      jumpTime ω' 1 = 1 ∧ jumpTime ω' 2 = 0 ∧
      (∀ s, jumpChain ω (properCount ω s) = ω s) ∧
      (∀ s, jumpChain ω' (properCount ω' s) = ω' s) ∧
      (∀ k, jumpChain ω (k + 1) ≠ jumpChain ω k) ∧
      (∀ᵐ ω'' ∂(Measure.dirac ω), ∃ s, t ≤ properCount ω'' s) ∧
      ∫⁻ ω'', (jumpTime ω'' t : ℝ≥0∞) ∂(Measure.dirac ω) = (t : ℝ≥0∞) ∧
      ∑ j ∈ Finset.range t,
          ∫⁻ ω'', ((jumpTime ω'' (j + 1) - jumpTime ω'' j : ℕ) : ℝ≥0∞) ∂(Measure.dirac ω)
        = (t : ℝ≥0∞) := by
  have hN : ∀ s, properCount (fun i : ℕ => i) s = s := by
    intro s
    induction s with
    | zero => simp
    | succ s ih => rw [properCount_succ_of_ne (by omega), ih]
  have hT : ∀ k, jumpTime (fun i : ℕ => i) k = k := fun k =>
    le_antisymm (jumpTime_le (by rw [hN])) (le_jumpTime ⟨k, by rw [hN]⟩)
  have hY : ∀ k, jumpChain (fun i : ℕ => i) k = k := fun k => by
    rw [jumpChain_apply, hT]
  have hN' : ∀ s, properCount (fun i : ℕ => min i 1) s = min s 1 := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
        by_cases hs : s = 0
        · subst hs
          rw [properCount_succ_of_ne (by omega), ih]
          omega
        · rw [properCount_succ_of_eq (by omega), ih]
          omega
  have hmeasT : Measurable fun ω : ℕ → ℕ => (jumpTime ω t : ℝ≥0∞) :=
    (Measurable.of_discrete (f := fun c : ℕ => (c : ℝ≥0∞))).comp (measurable_jumpTime t)
  refine ⟨fun i => i, fun i => min i 1, hN, hT, hY, hN', ?_, ?_,
    fun s => jumpChain_properCount _ s, fun s => jumpChain_properCount _ s,
    fun k => jumpChain_succ_ne ⟨k + 1, by rw [hN]⟩, ?_, ?_, ?_⟩
  · exact le_antisymm (jumpTime_le (by rw [hN']; omega))
      (le_jumpTime ⟨1, by rw [hN']; omega⟩)
  · refine jumpTime_eq_zero_of_not_exists ?_
    rintro ⟨s, hs⟩
    rw [hN'] at hs
    omega
  · exact (ae_dirac_iff (measurableSet_exists_le_properCount t)).2 ⟨t, by rw [hN]⟩
  · rw [lintegral_dirac' _ hmeasT, hT]
  · rw [Finset.sum_congr rfl fun j _ => lintegral_dirac' _ (measurable_sojourn j)]
    simp only [hT]
    simp

/-- **The ball-walk witness.**  For every dimension `n ≥ 1` and every step `δ > 1`, the unit
ball and its centre satisfy every hypothesis of §5 with every conclusion non-degenerate:

* `ell K δ x = (δⁿ)⁻¹`, which is **strictly between `0` and `1`** — so the walk genuinely
  sometimes moves and genuinely sometimes holds, and the hypothesis `ell K δ x ≠ 0` of
  `lintegral_jumpTime_one_pathMeasure_ballWalk` is satisfied and not vacuous;
* the probability that the walk's first step is proper is exactly that number
  (`pathMeasure_ballWalk_properStep`), so the pathwise notion of a proper step used throughout
  this file has, for the ball walk, exactly the ball walk's own acceptance probability;
* the paths that never move are null;
* the mean first jump time is exactly `δⁿ`, **strictly greater than `1` and finite** — a real
  number of ball-walk steps, not `0` and not `⊤`. -/
theorem exists_timeChange_ballWalk_witness {n : ℕ} [NeZero n] {δ : ℝ} (hδ : 1 < δ) :
    ∃ (K : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)),
      MeasurableSet K ∧ volume K ≠ 0 ∧ volume K ≠ ⊤ ∧
      ell K δ x = (ENNReal.ofReal (δ ^ n))⁻¹ ∧
      0 < ell K δ x ∧ ell K δ x < 1 ∧
      pathMeasure (ballWalk K δ) (Measure.dirac x)
          {ω : ℕ → EuclideanSpace ℝ (Fin n) | ω 1 ≠ ω 0} = ell K δ x ∧
      pathMeasure (ballWalk K δ) (Measure.dirac x)
          (⋂ k : ℕ, {ω : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω i = x}) = 0 ∧
      ∫⁻ ω, (jumpTime ω 1 : ℝ≥0∞) ∂(pathMeasure (ballWalk K δ) (Measure.dirac x))
        = ENNReal.ofReal (δ ^ n) ∧
      1 < ENNReal.ofReal (δ ^ n) ∧ ENNReal.ofReal (δ ^ n) ≠ ⊤ := by
  have hn : n ≠ 0 := NeZero.ne n
  have hpow : (1 : ℝ) < δ ^ n := one_lt_pow₀ hδ hn
  have hE : (1 : ℝ≥0∞) < ENNReal.ofReal (δ ^ n) := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hpow
  have hell : ell (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ 0
      = (ENNReal.ofReal (δ ^ n))⁻¹ := ell_unitBall_zero_of_one_le hδ.le
  have hell0 : (0 : ℝ≥0∞) < ell (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ 0 := by
    rw [hell]
    exact ENNReal.inv_pos.2 ENNReal.ofReal_ne_top
  refine ⟨Metric.ball 0 1, 0, measurableSet_ball, volume_unitBall_ne_zero,
    volume_unitBall_ne_top, hell, hell0, ?_, ?_, ?_, ?_, hE, ENNReal.ofReal_ne_top⟩
  · rw [hell]
    exact ENNReal.inv_lt_one.2 hE
  · exact pathMeasure_ballWalk_properStep measurableSet_ball δ 0
  · exact pathMeasure_ballWalk_never_moves measurableSet_ball δ 0 hell0.ne'
  · rw [lintegral_jumpTime_one_pathMeasure_ballWalk measurableSet_ball δ 0 hell0.ne', hell,
      inv_inv]

end Witness

/-! ## Axiom audit

Every theorem of this file, re-checked at elaboration time.  Each must print a subset of
`[propext, Classical.choice, Quot.sound]`; anything else — in particular `sorryAx` — means the
file is not finished. -/

section AxiomCheck

#print axioms properCount_zero
#print axioms properCount_succ_of_eq
#print axioms properCount_succ_of_ne
#print axioms properCount_succ_eq_or
#print axioms properCount_le_succ
#print axioms properCount_succ_le
#print axioms properCount_mono
#print axioms properCount_le_self
#print axioms properCount_congr
#print axioms eq_of_properCount_eq
#print axioms jumpTime_le
#print axioms properCount_lt_of_lt_jumpTime
#print axioms le_properCount_jumpTime
#print axioms jumpTime_zero
#print axioms jumpTime_eq_zero_of_not_exists
#print axioms properCount_jumpTime
#print axioms le_jumpTime
#print axioms exists_of_succ
#print axioms jumpTime_lt_jumpTime_succ
#print axioms jumpChain_zero
#print axioms jumpChain_apply
#print axioms jumpChain_succ_ne
#print axioms jumpChain_properCount
#print axioms jumpTime_eq_sum_sojourn
#print axioms eq_zero_of_lt_jumpTime_one
#print axioms ne_of_jumpTime_one
#print axioms tsum_indicator_holdsUntil_eq_jumpTime_one
#print axioms tsum_indicator_holdsUntil_eq_top
#print axioms measurableSet_properStep
#print axioms properCount_succ_eq_add_indicator
#print axioms measurable_properCount
#print axioms measurableSet_le_properCount
#print axioms measurable_jumpTime
#print axioms measurable_jumpChain
#print axioms measurableSet_comap_frestrictLe_le_properCount
#print axioms pathMeasure_ballWalk_properStep
#print axioms pathMeasure_ballWalk_never_moves
#print axioms lintegral_jumpTime_one_pathMeasure_ballWalk
#print axioms measurableSet_exists_le_properCount
#print axioms measurable_sojourn
#print axioms lintegral_jumpTime_eq_sum_sojourn
#print axioms exists_timeChange_path_witness
#print axioms exists_timeChange_ballWalk_witness

end AxiomCheck

end Arlib.MarkovChains
