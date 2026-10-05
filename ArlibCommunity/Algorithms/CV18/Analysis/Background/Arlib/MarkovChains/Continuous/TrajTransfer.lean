/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.HoldingTime
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# The holding-time transfer at trajectory level

`Arlib/MarkovChains/Continuous/HoldingTime.lean` proves the holding-time correspondence
between the ball walk and the speedy walk at the level of **one step** and of **measures**:
`ballWalk_eq_ell_smul_speedyWalk_add` (one step is a two-point mixture) and
`ellMeasure_withDensity_inv_ell` (reweighting by `(ell)⁻¹` returns Lebesgue measure on `K`
exactly).  Its own "What is not proved", item 2, records what was missing: a construction of
the chain on a **single trajectory space**, so that statements about the *whole path* — the
sequence of holding times, the law at every time simultaneously — are statements about
genuine events rather than about a family of unrelated marginals.

This file supplies that.  It is **infinite-horizon**: the underlying object is
`ProbabilityTheory.Kernel.trajMeasure`, i.e. Mathlib's Ionescu–Tulcea construction
(`Mathlib.Probability.Kernel.IonescuTulcea.Traj`, available since well before Mathlib
v4.32), so `pathMeasure P mu` is a probability measure on `ℕ → Om` and every result below
constrains infinitely many coordinates of one sample point.  Nothing here is a
finite-horizon substitute.

## Main results

**A time-homogeneous chain on one trajectory space.**

* `Arlib.MarkovChains.chainKernel` — a single Markov kernel `P`, presented as the
  history-dependent kernel family Ionescu–Tulcea consumes (it reads only the last
  coordinate).
* `Arlib.MarkovChains.pathMeasure` — the law of the whole trajectory `(ω₀, ω₁, …)` of the
  chain with step kernel `P` started from `mu`.  A probability measure on `ℕ → Om`.
* `Arlib.MarkovChains.map_eval_pathMeasure_zero`,
  `Arlib.MarkovChains.map_eval_pathMeasure_succ` — its time marginals: `mu` at time `0`, and
  one application of `P` per step.

**Exact identification of the target.**

* `Arlib.MarkovChains.map_eval_pathMeasure_of_invariant` — if `mu` is `P`-invariant then
  *every* coordinate of the infinite trajectory has law exactly `mu`.
* `Arlib.MarkovChains.map_eval_pathMeasure_ballWalk_uniformOn` — the ball-walk instance:
  started from `Arlib.uniformOn volume K`, the ball-walk path has law exactly
  `Arlib.uniformOn volume K` at every time.  **No total-variation term appears.**
  *Range of validity*: this is a statement about the chain **started at stationarity**.  It
  does not say, and this file does not prove, that a chain started elsewhere converges; that
  is a mixing statement and needs a conductance bound (see "What is not proved").

**The trajectory-level factorisation.**

* `Arlib.MarkovChains.condDistrib_pathMeasure` — a regular conditional distribution of the
  position at time `a + 1` given the *entire history* `(ω₀, …, ω_a)` is `P` at `ω_a`.
  Costs `[StandardBorelSpace Om]` and `[Nonempty Om]`, which is what makes a regular
  conditional distribution exist; both hold for `EuclideanSpace ℝ (Fin n)`.
* `Arlib.MarkovChains.condDistrib_pathMeasure_ballWalk` — **the holding-time factorisation
  at trajectory level**: almost surely, conditionally on the whole past, the ball walk's next
  position is distributed as
  `ell K δ (ω_a) • speedyWalk K δ (ω_a) + (1 - ell K δ (ω_a)) • dirac (ω_a)`.
  This is `ballWalk_eq_ell_smul_speedyWalk_add` lifted from one step to the law of the path.
  *Range of validity*: `MeasurableSet K` and `IsProbabilityMeasure mu`; no positivity of `δ`,
  no convexity, no bound on `vol K`.

**The holding time itself.**

* `Arlib.MarkovChains.pathMeasure_dirac_holdsUntil` — for any Markov kernel `P` on a space
  with measurable singletons, started at `x`,
  `P(ω is still at x at every time 0,…,k) = (P x {x}) ^ k`.
* `Arlib.MarkovChains.pathMeasure_ballWalk_dirac_holdsUntil` — the ball-walk instance:
  that probability is `(1 - ell K δ x) ^ k`, i.e. **the holding time is `Geometric(ell K δ x)`**.
  *Cost*: `[NeZero n]`, inherited from `ballWalk_apply_compl_singleton` and not removable —
  in `EuclideanSpace ℝ (Fin 0)` the space is a single atom and the identity is false.
* `Arlib.MarkovChains.tsum_pathMeasure_ballWalk_dirac_holdsUntil` and
  `Arlib.MarkovChains.lintegral_exitTime_pathMeasure_ballWalk` — **the mean holding time is
  exactly `(ell K δ x)⁻¹`**, the second stated as an honest `∫⁻` of the exit time
  `inf {i | ωᵢ ≠ x}` (written as its sum of survival indicators).  This is the missing
  identification behind `HoldingTime.lean`'s `ellMeasure_withDensity_inv_ell`: the density
  `(ell)⁻¹` that reweights the speedy walk's stationary measure into Lebesgue measure is the
  mean holding time of the **actual trajectory**, not a formal reciprocal.  At a stuck `x`
  both sides are `⊤`, correctly.

**Non-vacuity.**

* `Arlib.MarkovChains.ell_unitBall_zero_of_one_le` — `ell (ball 0 1) δ 0 = (δⁿ)⁻¹` for
  `δ ≥ 1`.  For `δ ≤ 1` the centre has `ell = 1` and never holds, so this computation is
  what makes the results above non-degenerate at all.
* `Arlib.MarkovChains.exists_trajTransfer_witness` — for any `1 < δ₁ < δ₂` and any `n ≥ 1`,
  **two** ball walks (unit ball, centre `0`, steps `δ₁` and `δ₂`) for which the holding
  probability is *strictly positive at every horizon* and *strictly less than `1`* already at
  horizon `1`, and whose mean holding times are `δ₁ⁿ` and `δ₂ⁿ` — both proved **strictly
  greater than `1`**, both finite, and proved **strictly different from each other**.  The
  two instances are therefore separated by a proved strict inequality between the numbers
  the theorems compute; no result above can hold for a degenerate reason.

## What is not proved

1. **The time change itself is not proved.**  Nothing here constructs the jump chain
   `Y₀, Y₁, …` of accepted positions from a ball-walk path, nor the counting process `N t`,
   nor the identity `ω_t = Y_{N t}`.  What is proved is the two halves that identity would
   sit between: the conditional one-step factorisation along the path
   (`condDistrib_pathMeasure_ballWalk`) and the exact geometric law of each sojourn
   (`pathMeasure_ballWalk_dirac_holdsUntil`).  Assembling them into a path-level time change
   requires measurability of the successive jump times, which no file in this library has.
2. **No concentration bound for the number of speedy steps in `t` ball-walk steps.**
   `tsum_pathMeasure_ballWalk_dirac_holdsUntil` is a first-moment statement about one
   sojourn from a fixed start point.  Turning it into "with probability `1 - η`, `t` ball-walk
   steps contain at least `c·t·ell` speedy steps" needs the sojourns along a trajectory to be
   handled jointly, which is item 1.
3. **No mixing-time statement for the ball walk.**  `map_eval_pathMeasure_ballWalk_uniformOn`
   is stated at stationarity; the obstruction to a conductance lower bound for the ball walk
   is unchanged and is stated exactly in `HoldingTime.lean`
   (`conductanceOn_ballWalk_mul_volume_inter`).
4. **`pathMeasure_ballWalk_dirac_holdsUntil` is about a sojourn started at a deterministic
   point.**  It does not average `x` over any distribution; the averaged form is
   `ellMeasure_withDensity_inv_ell` in `HoldingTime.lean`, and the two are related by
   integration, not by either implying the other.

## Conventions

No `structure`, `class` or named `Prop` is introduced by this file.  The only `def`s are
`chainKernel` (plumbing: `P` presented as a kernel family) and `pathMeasure` (an
abbreviation for `Kernel.trajMeasure`); neither asserts anything — `chainKernel_apply` and
the `pathMeasure` unfolding are both `rfl`.  Every hypothesis is an inline hypothesis of the
theorem that consumes it.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ## 1. A time-homogeneous chain on one trajectory space -/

section Chain

variable {Om : Type*} [MeasurableSpace Om]

/-- **The step kernel of a time-homogeneous chain, in Ionescu–Tulcea form.**  The
Ionescu–Tulcea construction feeds the whole history `(x₀, …, x_m)` to the step kernel; a
time-homogeneous chain reads only the last coordinate.  `chainKernel P m` is `P` precomposed
with that read. -/
noncomputable def chainKernel (P : Kernel Om Om) (m : ℕ) :
    Kernel ((_i : ↥(Finset.Iic m)) → Om) Om :=
  Kernel.comap P (fun h => h ⟨m, Finset.mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

@[simp] theorem chainKernel_apply (P : Kernel Om Om) (m : ℕ)
    (h : (_i : ↥(Finset.Iic m)) → Om) :
    chainKernel P m h = P (h ⟨m, Finset.mem_Iic.2 le_rfl⟩) := rfl

instance isMarkovKernel_chainKernel (P : Kernel Om Om) [IsMarkovKernel P] (m : ℕ) :
    IsMarkovKernel (chainKernel P m) := by
  rw [chainKernel]; infer_instance

/-- **The law of the whole trajectory `(ω₀, ω₁, ω₂, …)`** of the chain with step kernel `P`
started from `mu`, as a single measure on `ℕ → Om`, built by Ionescu–Tulcea
(`ProbabilityTheory.Kernel.trajMeasure`).

This is an *infinite*-horizon object: every coordinate of every path lives on one sample
point, so events involving infinitely many times are genuine events. -/
noncomputable def pathMeasure (P : Kernel Om Om) [IsMarkovKernel P] (mu : Measure Om) :
    Measure (ℕ → Om) :=
  Kernel.trajMeasure (X := fun _ : ℕ => Om) mu (chainKernel P)

instance isProbabilityMeasure_pathMeasure (P : Kernel Om Om) [IsMarkovKernel P]
    (mu : Measure Om) [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (pathMeasure P mu) := by
  rw [pathMeasure]; infer_instance

/-- Composing a measure with a `comap`ped kernel is composing after mapping. -/
theorem bind_comap {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (kap : Kernel A C) [IsSFiniteKernel kap] {f : B → A} (hf : Measurable f)
    (nu : Measure B) [SFinite nu] :
    nu.bind (Kernel.comap kap f hf) = (nu.map f).bind kap := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.comap kap f hf).aemeasurable,
    Measure.bind_apply hs kap.aemeasurable, lintegral_map (kap.measurable_coe hs) hf]
  rfl

/-- **Time zero of the trajectory carries the initial law.**  The coordinates up to time `0`
of `Kernel.traj κ 0` are deterministic, so `mu` passes straight through. -/
theorem map_eval_pathMeasure_zero (P : Kernel Om Om) [IsMarkovKernel P] (mu : Measure Om)
    [IsProbabilityMeasure mu] :
    (pathMeasure P mu).map (fun ω => ω 0) = mu := by
  have hdet := Kernel.traj_map_frestrictLe_of_le (X := fun _ : ℕ => Om)
    (κ := chainKernel P) (a := 0) (b := 0) le_rfl
  have hmap : Kernel.map (Kernel.traj (X := fun _ : ℕ => Om) (chainKernel P) 0)
        (fun x => x 0)
      = Kernel.deterministic
          (fun x : (_i : ↥(Finset.Iic 0)) → Om => x ⟨0, Finset.mem_Iic.2 le_rfl⟩)
          (measurable_pi_apply _) := by
    rw [show (fun x : ℕ → Om => x 0)
        = (fun h : (_i : ↥(Finset.Iic 0)) → Om => h ⟨0, Finset.mem_Iic.2 le_rfl⟩)
          ∘ (Preorder.frestrictLe 0) from rfl,
      Kernel.map_comp_right _ (Preorder.measurable_frestrictLe 0) (measurable_pi_apply _), hdet,
      Kernel.deterministic_map _ (measurable_pi_apply _)]
    rfl
  rw [pathMeasure, Kernel.trajMeasure, Measure.map_comp _ _ (by fun_prop), hmap,
    Measure.deterministic_comp_eq_map, Measure.map_map (by fun_prop) (by fun_prop)]
  simp [Function.comp_def]

/-- **One step of the trajectory's time marginals**: the law at time `a + 1` is the law at
time `a` pushed through `P`.

Read off the joint law of `(history up to a, state at a+1)` from
`Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`, take its second marginal,
then use that `chainKernel P a` consults only the last coordinate of the history. -/
theorem map_eval_pathMeasure_succ (P : Kernel Om Om) [IsMarkovKernel P] (mu : Measure Om)
    [IsProbabilityMeasure mu] (a : ℕ) :
    (pathMeasure P mu).map (fun ω => ω (a + 1))
      = ((pathMeasure P mu).map (fun ω => ω a)).bind P := by
  have hjoint := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ : ℕ => Om) (μ₀ := mu) (κ := chainKernel P) (a := a)
  have hsnd := congrArg Measure.snd hjoint
  rw [Measure.snd_compProd] at hsnd
  rw [Measure.snd, Measure.map_map (by fun_prop) (by fun_prop)] at hsnd
  rw [chainKernel, bind_comap, Measure.map_map (measurable_pi_apply _) (by fun_prop)] at hsnd
  simp only [Function.comp_def, Preorder.frestrictLe_apply] at hsnd
  rw [pathMeasure, ← hsnd]

/-- **Exact identification of every time marginal, for an invariant initial law.**

If `mu` is invariant for `P` then *every* coordinate of the infinite trajectory started at
`mu` has law exactly `mu`:

    (pathMeasure P mu).map (fun ω => ω m) = mu   for every `m : ℕ`.

Assumes only `IsMarkovKernel P`, `IsProbabilityMeasure mu` and `Kernel.Invariant P mu`.
There is **no total-variation error term anywhere in this statement** — this is the exact
identification of the target along the whole path, not an approximation. -/
theorem map_eval_pathMeasure_of_invariant (P : Kernel Om Om) [IsMarkovKernel P]
    (mu : Measure Om) [IsProbabilityMeasure mu] (hinv : Kernel.Invariant P mu) (m : ℕ) :
    (pathMeasure P mu).map (fun ω => ω m) = mu := by
  induction m with
  | zero => exact map_eval_pathMeasure_zero P mu
  | succ a ih => rw [map_eval_pathMeasure_succ, ih]; exact hinv

/-! ## 2. The trajectory-level factorisation of the path law -/

/-- **The path law factorises through the one-step kernel, conditionally on the whole past.**

For every time `a`, a regular conditional distribution of the position at time `a + 1` given
the *entire history* `(ω₀, …, ω_a)` is `chainKernel P a`, i.e. `P` evaluated at `ω_a`.

Assumes `IsMarkovKernel P`, `IsProbabilityMeasure mu`, and `StandardBorelSpace Om`,
`Nonempty Om` (needed for a regular conditional distribution to exist at all).

This is the trajectory-level statement: it is an assertion about the law of the whole path,
not about any finite-dimensional marginal, and it says the path law is *exactly* the one
generated by iterating `P` — no total-variation slack. -/
theorem condDistrib_pathMeasure [StandardBorelSpace Om] [Nonempty Om] (P : Kernel Om Om)
    [IsMarkovKernel P] (mu : Measure Om) [IsProbabilityMeasure mu] (a : ℕ) :
    condDistrib (fun ω : ℕ → Om => ω (a + 1)) (Preorder.frestrictLe a) (pathMeasure P mu)
      =ᵐ[(pathMeasure P mu).map (Preorder.frestrictLe a)] chainKernel P a :=
  Kernel.condDistrib_trajMeasure (X := fun _ : ℕ => Om) (μ₀ := mu) (κ := chainKernel P)

/-! ## 3. The holding time along a trajectory -/

section Hold

variable [MeasurableSingletonClass Om]

/-- The event "the path has not moved off `x` up to time `k`". -/
theorem measurableSet_holdsUntil (x : Om) (k : ℕ) :
    MeasurableSet {ω : ℕ → Om | ∀ i ≤ k, ω i = x} := by
  have hrw : {ω : ℕ → Om | ∀ i ≤ k, ω i = x}
      = ⋂ i ∈ Set.Iic k, (fun ω : ℕ → Om => ω i) ⁻¹' {x} := by
    ext ω; simp
  rw [hrw]
  exact MeasurableSet.biInter (Set.finite_Iic k).countable fun i _ =>
    (measurable_pi_apply i) (measurableSet_singleton x)

/-- The same event, seen inside the space of histories up to time `k`. -/
theorem measurableSet_constHistory (x : Om) (k : ℕ) :
    MeasurableSet {h : (_i : ↥(Finset.Iic k)) → Om | ∀ i, h i = x} := by
  have hrw : {h : (_i : ↥(Finset.Iic k)) → Om | ∀ i, h i = x}
      = ⋂ i : ↥(Finset.Iic k), (fun h : (_i : ↥(Finset.Iic k)) → Om => h i) ⁻¹' {x} := by
    ext h; simp
  rw [hrw]
  exact MeasurableSet.iInter fun i => (measurable_pi_apply i) (measurableSet_singleton x)

omit [MeasurableSpace Om] [MeasurableSingletonClass Om] in
/-- Restricting a path to times `≤ k` sends the "has not moved" event to the constant
history. -/
theorem preimage_frestrictLe_constHistory (x : Om) (k : ℕ) :
    (Preorder.frestrictLe k) ⁻¹' {h : (_i : ↥(Finset.Iic k)) → Om | ∀ i, h i = x}
      = {ω : ℕ → Om | ∀ i ≤ k, ω i = x} := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Preorder.frestrictLe_apply]
  constructor
  · intro h i hi; exact h ⟨i, Finset.mem_Iic.2 hi⟩
  · intro h i; exact h i.1 (Finset.mem_Iic.1 i.2)

/-- **The holding time of a time-homogeneous chain is geometric, at trajectory level.**

Started at the point `x`, the law of the *whole infinite path* assigns the event
"the chain is still at `x` at every time `0, 1, …, k`" the mass

    (P x {x}) ^ k.

Assumes `IsMarkovKernel P` and `MeasurableSingletonClass Om`; nothing else.  In particular
the holding time — the first time the path leaves `x` — is `Geometric(1 - P x {x})`, so its
mean is `(1 - P x {x})⁻¹`.

This is a statement about the trajectory measure, not about iterated one-step marginals: the
event constrains infinitely many coordinates of one sample point. -/
theorem pathMeasure_dirac_holdsUntil (P : Kernel Om Om) [IsMarkovKernel P] (x : Om) (k : ℕ) :
    pathMeasure P (Measure.dirac x) {ω : ℕ → Om | ∀ i ≤ k, ω i = x} = (P x {x}) ^ k := by
  induction k with
  | zero =>
      have hrw : {ω : ℕ → Om | ∀ i ≤ 0, ω i = x} = (fun ω : ℕ → Om => ω 0) ⁻¹' {x} := by
        ext ω; simp
      rw [hrw, ← Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton x),
        map_eval_pathMeasure_zero, pow_zero]
      simp
  | succ k ih =>
      rw [pathMeasure] at ih ⊢
      have hHm : MeasurableSet {h : (_i : ↥(Finset.Iic k)) → Om | ∀ i, h i = x} :=
        measurableSet_constHistory x k
      have hjoint := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
        (X := fun _ : ℕ => Om) (μ₀ := Measure.dirac x) (κ := chainKernel P) (a := k)
      set nu : Measure (ℕ → Om) :=
        Kernel.trajMeasure (X := fun _ : ℕ => Om) (Measure.dirac x) (chainKernel P) with hnu
      set H : Set ((_i : ↥(Finset.Iic k)) → Om) := {h | ∀ i, h i = x} with hH
      have happ := congrArg (fun m : Measure (((_i : ↥(Finset.Iic k)) → Om) × Om) =>
        m (H ×ˢ ({x} : Set Om))) hjoint
      rw [Measure.compProd_apply_prod hHm (measurableSet_singleton x),
        Measure.map_apply (by fun_prop) (hHm.prod (measurableSet_singleton x))] at happ
      have hL : ∫⁻ h in H, (chainKernel P k) h {x} ∂(nu.map (Preorder.frestrictLe k))
          = P x {x} * nu.map (Preorder.frestrictLe k) H := by
        rw [setLIntegral_congr_fun (g := fun _ => P x {x}) hHm (fun h hh => by
          simp only [chainKernel_apply]
          rw [hh ⟨k, Finset.mem_Iic.2 le_rfl⟩]), setLIntegral_const, mul_comm]
      have hR : (fun ω : ℕ → Om => (Preorder.frestrictLe k ω, ω (k + 1)))
            ⁻¹' (H ×ˢ ({x} : Set Om)) = {ω : ℕ → Om | ∀ i ≤ k + 1, ω i = x} := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, Set.mem_setOf_eq, hH,
          Preorder.frestrictLe_apply]
        constructor
        · rintro ⟨h1, h2⟩ i hi
          rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hi) with hlt | heq
          · exact h1 ⟨i, Finset.mem_Iic.2 (Nat.lt_succ_iff.1 hlt)⟩
          · rw [heq]; exact h2
        · intro h
          exact ⟨fun i => h i.1 ((Finset.mem_Iic.1 i.2).trans (Nat.le_succ k)), h (k + 1) le_rfl⟩
      have hmu : nu.map (Preorder.frestrictLe k) H = (P x {x}) ^ k := by
        rw [Measure.map_apply (Preorder.measurable_frestrictLe k) hHm, hH,
          preimage_frestrictLe_constHistory, ih]
      rw [hL, hR, hmu] at happ
      rw [← happ, pow_succ']

end Hold

end Chain

/-! ## 4. The ball walk: the holding-time transfer at trajectory level -/

section BallWalkPath

variable {n : ℕ}

/-- **The ball walk stays put with probability exactly `1 - ell K δ x`.**  Complement of
`ballWalk_apply_compl_singleton`; `[NeZero n]` is inherited from it and is not removable. -/
theorem ballWalk_apply_singleton [NeZero n] {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ballWalk K δ x {x} = 1 - ell K δ x := by
  have hsum : ballWalk K δ x {x} + ballWalk K δ x {x}ᶜ = 1 := by
    rw [measure_add_measure_compl (measurableSet_singleton x)]
    exact measure_univ
  rw [ballWalk_apply_compl_singleton hK δ x] at hsum
  rw [← hsum, ENNReal.add_sub_cancel_right
    (ne_top_of_le_ne_top ENNReal.one_ne_top (ell_le_one K δ x))]

/-- **The holding time of the ball walk is `Geometric(ell K δ x)`, at trajectory level.**

Started at `x`, the law of the *whole infinite ball-walk path* assigns the event
"the walk is still at `x` at every time `0, 1, …, k`" the mass

    (1 - ell K δ x) ^ k.

Assumes `MeasurableSet K` and `[NeZero n]` (i.e. `n ≥ 1`) — nothing else: no positivity of
`δ`, no convexity, no bound on `vol K`.  `[NeZero n]` is not removable: in
`EuclideanSpace ℝ (Fin 0)` the whole space is a single atom, `{x}ᶜ = ∅`, and
`ballWalk_apply_compl_singleton` already fails there.

This is the trajectory-level counterpart of the one-step decomposition
`ballWalk_eq_ell_smul_speedyWalk_add` of `HoldingTime.lean`: the geometric holding time
that file describes in prose is here a proved property of the trajectory measure. -/
theorem pathMeasure_ballWalk_dirac_holdsUntil [NeZero n]
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (δ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    pathMeasure (ballWalk K δ) (Measure.dirac x)
        {ω : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω i = x}
      = (1 - ell K δ x) ^ k := by
  rw [pathMeasure_dirac_holdsUntil, ballWalk_apply_singleton hK]

/-- **The mean holding time of the ball walk at `x` is exactly `(ell K δ x)⁻¹`**, computed
from the trajectory measure.

The sum on the left is `∑ₖ P(the walk has not left x by time k)`, i.e. the expectation of
the exit time `inf {i | ωᵢ ≠ x}` in its tail-sum form; `lintegral_exitTime_pathMeasure_ballWalk`
below states the same number as an honest integral of the exit time itself.

Assumes `MeasurableSet K` and `[NeZero n]`.  At a stuck `x` (`ell K δ x = 0`) both sides are
`⊤`, which is correct: the walk never leaves.

This is the missing identification behind `HoldingTime.lean`'s
`ellMeasure_withDensity_inv_ell`: the density `(ell)⁻¹` that reweights the speedy walk's
stationary measure into Lebesgue measure is **the mean holding time of the actual ball-walk
trajectory**, not merely a formal reciprocal. -/
theorem tsum_pathMeasure_ballWalk_dirac_holdsUntil [NeZero n]
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (δ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ∑' k : ℕ, pathMeasure (ballWalk K δ) (Measure.dirac x)
        {ω : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω i = x}
      = (ell K δ x)⁻¹ := by
  have h : ∀ k : ℕ, pathMeasure (ballWalk K δ) (Measure.dirac x)
      {ω : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω i = x} = (1 - ell K δ x) ^ k :=
    fun k => pathMeasure_ballWalk_dirac_holdsUntil hK δ x k
  simp_rw [h]
  rw [ENNReal.tsum_geometric, ENNReal.sub_sub_cancel ENNReal.one_ne_top (ell_le_one K δ x)]

/-- **The exit time of the ball walk from `x` has mean exactly `(ell K δ x)⁻¹`.**

The integrand `∑ₖ 1[ω has not left x by time k]` *is* the exit time `inf {i | ωᵢ ≠ x}`,
counted in ℝ≥0∞ (it is `0` if `ω₀ ≠ x`, and `⊤` if the path never leaves).  Assumes
`MeasurableSet K` and `[NeZero n]`. -/
theorem lintegral_exitTime_pathMeasure_ballWalk [NeZero n]
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (δ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ∫⁻ ω, (∑' k : ℕ, {ω' : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω' i = x}.indicator
          (1 : (ℕ → EuclideanSpace ℝ (Fin n)) → ℝ≥0∞) ω)
        ∂(pathMeasure (ballWalk K δ) (Measure.dirac x))
      = (ell K δ x)⁻¹ := by
  rw [lintegral_tsum fun k =>
    (measurable_one.indicator (measurableSet_holdsUntil x k)).aemeasurable]
  have h : ∀ k : ℕ, ∫⁻ ω, {ω' : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω' i = x}.indicator
        (1 : (ℕ → EuclideanSpace ℝ (Fin n)) → ℝ≥0∞) ω
        ∂(pathMeasure (ballWalk K δ) (Measure.dirac x))
      = pathMeasure (ballWalk K δ) (Measure.dirac x)
          {ω' : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω' i = x} :=
    fun k => lintegral_indicator_one (measurableSet_holdsUntil x k)
  simp_rw [h]
  exact tsum_pathMeasure_ballWalk_dirac_holdsUntil hK δ x

/-- **The trajectory-level holding-time factorisation of the ball walk.**

Conditionally on the *entire past* `(ω₀, …, ω_a)` of the ball-walk trajectory, the position
at time `a + 1` is distributed as

    ell K δ (ω_a) • speedyWalk K δ (ω_a)  +  (1 - ell K δ (ω_a)) • dirac (ω_a),

almost surely.  Assumes `MeasurableSet K` and `IsProbabilityMeasure mu`.

This is exactly `ballWalk_eq_ell_smul_speedyWalk_add` lifted from a single step to the law
of the whole path: at every time, given everything that has happened, the walk takes a
speedy step with probability `ell` at the current point and otherwise holds.  It is an
equality of conditional laws, with no total-variation slack. -/
theorem condDistrib_pathMeasure_ballWalk {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ : ℝ) (mu : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure mu] (a : ℕ) :
    ∀ᵐ h ∂((pathMeasure (ballWalk K δ) mu).map (Preorder.frestrictLe a)),
      condDistrib (fun ω : ℕ → EuclideanSpace ℝ (Fin n) => ω (a + 1))
          (Preorder.frestrictLe a) (pathMeasure (ballWalk K δ) mu) h
        = ell K δ (h ⟨a, Finset.mem_Iic.2 le_rfl⟩)
            • speedyWalk K δ (h ⟨a, Finset.mem_Iic.2 le_rfl⟩)
          + (1 - ell K δ (h ⟨a, Finset.mem_Iic.2 le_rfl⟩))
            • Measure.dirac (h ⟨a, Finset.mem_Iic.2 le_rfl⟩) := by
  filter_upwards [condDistrib_pathMeasure (ballWalk K δ) mu a] with h hh
  rw [hh, chainKernel_apply, ballWalk_eq_ell_smul_speedyWalk_add hK]

/-- **Exact identification of the ball walk's target along the whole trajectory.**

Started from `Arlib.uniformOn volume K`, *every* coordinate of the infinite ball-walk path
has law exactly `Arlib.uniformOn volume K`.  Assumes `MeasurableSet K` and that
`Arlib.uniformOn volume K` is a probability measure (i.e. `0 < vol K < ⊤`, discharged for
the unit ball by `isProbabilityMeasure_uniformOn_unitBall`).

There is **no total-variation error term in this statement**: the target is identified
exactly, at every time, not approached to within some `ε`. -/
theorem map_eval_pathMeasure_ballWalk_uniformOn {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ : ℝ) [IsProbabilityMeasure (Arlib.uniformOn volume K)] (m : ℕ) :
    (pathMeasure (ballWalk K δ) (Arlib.uniformOn volume K)).map (fun ω => ω m)
      = Arlib.uniformOn volume K :=
  map_eval_pathMeasure_of_invariant _ _ (invariant_ballWalk hK δ) m

/-! ## 5. Non-vacuity: a pair of chains that genuinely hold and genuinely move -/

/-- **The local conductance at the centre of the unit ball, for a step at least as large as
the body**: `ell = (δⁿ)⁻¹`, which for `δ > 1` is strictly between `0` and `1`.

This is the computation that makes the holding-time statements above non-degenerate: for
`δ ≤ 1` the centre has `ell = 1` (`ell_unitBall_zero`) and the walk never holds there. -/
theorem ell_unitBall_zero_of_one_le {δ : ℝ} (hδ : 1 ≤ δ) :
    ell (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ 0
      = (ENNReal.ofReal (δ ^ n))⁻¹ := by
  have hδ0 : (0:ℝ) < δ := lt_of_lt_of_le zero_lt_one hδ
  have hinter : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ
        ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1
      = Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    Set.inter_eq_self_of_subset_right (Metric.ball_subset_ball hδ)
  have hvol : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)
      = ENNReal.ofReal (δ ^ n) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    rw [Measure.addHaar_ball_of_pos volume 0 hδ0, finrank_euclideanSpace_fin]
  have hc0 : ENNReal.ofReal (δ ^ n) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hct : ENNReal.ofReal (δ ^ n) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [ell_apply, hinter, hvol, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hc0) (Or.inl hct),
    ← mul_assoc, mul_comm (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
      (ENNReal.ofReal (δ ^ n))⁻¹, mul_assoc,
    ENNReal.mul_inv_cancel volume_unitBall_ne_zero volume_unitBall_ne_top, mul_one]

/-- **The non-vacuity witness: two structurally different chains, both non-degenerate.**

For any two steps `1 < δ₁ < δ₂` and any dimension `n ≥ 1`, the unit ball `K` and its centre
`x = 0` give two ball walks whose trajectory-level holding behaviour is *different* and, in
both cases, *strictly non-trivial*:

* the exact geometric holding law holds for both, with parameter `(δᵢⁿ)⁻¹`;
* the probability of holding through time `k` is **strictly positive** for every `k` — the
  chains really do hold, the law is not concentrated on "move immediately";
* the probability of holding through time `1` is **strictly less than `1`** — the chains
  really do move, the law is not concentrated on "never move";
* the mean holding times are `δ₁ⁿ` and `δ₂ⁿ`, both **strictly greater than `1`**, both
  **finite**, and **different from each other**;
* `Arlib.uniformOn volume K` is a genuine probability measure, and the exact-target statement
  `map_eval_pathMeasure_ballWalk_uniformOn` holds for both chains at every time — so that
  theorem's instance hypothesis is satisfiable and its conclusion is not about the zero
  measure.

The last clause is the point: the two instances are not merely both inhabited, they are
separated by a proved strict inequality between the numbers the theorems compute, so no
statement above can be true for a degenerate reason. -/
theorem exists_trajTransfer_witness [NeZero n] {δ₁ δ₂ : ℝ} (h1 : 1 < δ₁) (h12 : δ₁ < δ₂) :
    ∃ (K : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)),
      MeasurableSet K ∧ volume K ≠ 0 ∧ volume K ≠ ⊤ ∧
      (∀ k : ℕ, pathMeasure (ballWalk K δ₁) (Measure.dirac x)
            {ω : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω i = x}
          = (1 - (ENNReal.ofReal (δ₁ ^ n))⁻¹) ^ k) ∧
      (∀ k : ℕ, pathMeasure (ballWalk K δ₂) (Measure.dirac x)
            {ω : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω i = x}
          = (1 - (ENNReal.ofReal (δ₂ ^ n))⁻¹) ^ k) ∧
      (∀ k : ℕ, 0 < pathMeasure (ballWalk K δ₁) (Measure.dirac x)
          {ω : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω i = x}) ∧
      (∀ k : ℕ, 0 < pathMeasure (ballWalk K δ₂) (Measure.dirac x)
          {ω : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω i = x}) ∧
      pathMeasure (ballWalk K δ₁) (Measure.dirac x)
          {ω : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ 1, ω i = x} < 1 ∧
      pathMeasure (ballWalk K δ₂) (Measure.dirac x)
          {ω : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ 1, ω i = x} < 1 ∧
      (∑' k : ℕ, pathMeasure (ballWalk K δ₁) (Measure.dirac x)
          {ω : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω i = x}) = ENNReal.ofReal (δ₁ ^ n) ∧
      (∑' k : ℕ, pathMeasure (ballWalk K δ₂) (Measure.dirac x)
          {ω : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω i = x}) = ENNReal.ofReal (δ₂ ^ n) ∧
      1 < ENNReal.ofReal (δ₁ ^ n) ∧
      ENNReal.ofReal (δ₁ ^ n) < ENNReal.ofReal (δ₂ ^ n) ∧
      ENNReal.ofReal (δ₂ ^ n) ≠ ⊤ ∧
      IsProbabilityMeasure (Arlib.uniformOn volume K) ∧
      (∀ m : ℕ, (pathMeasure (ballWalk K δ₁) (Arlib.uniformOn volume K)).map (fun ω => ω m)
          = Arlib.uniformOn volume K) ∧
      (∀ m : ℕ, (pathMeasure (ballWalk K δ₂) (Arlib.uniformOn volume K)).map (fun ω => ω m)
          = Arlib.uniformOn volume K) := by
  have hn : n ≠ 0 := NeZero.ne n
  haveI hprob : IsProbabilityMeasure
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
    isProbabilityMeasure_uniformOn_unitBall
  have h2 : 1 < δ₂ := h1.trans h12
  have h1p : (0:ℝ) < δ₁ := lt_trans zero_lt_one h1
  -- the two dimensional volumes, as real numbers
  have hpow1 : (1:ℝ) < δ₁ ^ n := one_lt_pow₀ h1 hn
  have hpow2 : (1:ℝ) < δ₂ ^ n := one_lt_pow₀ h2 hn
  have hpow12 : δ₁ ^ n < δ₂ ^ n := pow_lt_pow_left₀ h12 h1p.le hn
  have hE1 : (1 : ℝ≥0∞) < ENNReal.ofReal (δ₁ ^ n) := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hpow1
  have hE2 : (1 : ℝ≥0∞) < ENNReal.ofReal (δ₂ ^ n) := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hpow2
  have hE12 : ENNReal.ofReal (δ₁ ^ n) < ENNReal.ofReal (δ₂ ^ n) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hpow12
  -- the exact holding laws
  have hlaw : ∀ δ : ℝ, 1 ≤ δ → ∀ k : ℕ,
      pathMeasure (ballWalk (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ)
          (Measure.dirac (0 : EuclideanSpace ℝ (Fin n)))
          {ω : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω i = 0}
        = (1 - (ENNReal.ofReal (δ ^ n))⁻¹) ^ k := by
    intro δ hδ k
    rw [pathMeasure_ballWalk_dirac_holdsUntil measurableSet_ball δ 0 k,
      ell_unitBall_zero_of_one_le hδ]
  have hsum : ∀ δ : ℝ, 1 ≤ δ →
      (∑' k : ℕ, pathMeasure (ballWalk (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ)
          (Measure.dirac (0 : EuclideanSpace ℝ (Fin n)))
          {ω : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω i = 0}) = ENNReal.ofReal (δ ^ n) := by
    intro δ hδ
    rw [tsum_pathMeasure_ballWalk_dirac_holdsUntil measurableSet_ball δ 0,
      ell_unitBall_zero_of_one_le hδ, inv_inv]
  -- strict positivity of the holding probability
  have hpos : ∀ δ : ℝ, (1 : ℝ≥0∞) < ENNReal.ofReal (δ ^ n) → 1 ≤ δ → ∀ k : ℕ,
      0 < pathMeasure (ballWalk (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ)
          (Measure.dirac (0 : EuclideanSpace ℝ (Fin n)))
          {ω : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω i = 0} := by
    intro δ hE hδ k
    rw [hlaw δ hδ k]
    exact ENNReal.pow_pos (tsub_pos_of_lt (ENNReal.inv_lt_one.2 hE)) k
  -- and it is strictly below one
  have hlt : ∀ δ : ℝ, 1 ≤ δ →
      pathMeasure (ballWalk (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ)
          (Measure.dirac (0 : EuclideanSpace ℝ (Fin n)))
          {ω : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ 1, ω i = 0} < 1 := by
    intro δ hδ
    rw [hlaw δ hδ 1, pow_one]
    exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero
      (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)
  exact ⟨Metric.ball 0 1, 0, measurableSet_ball, volume_unitBall_ne_zero,
    volume_unitBall_ne_top, hlaw δ₁ h1.le, hlaw δ₂ h2.le, hpos δ₁ hE1 h1.le,
    hpos δ₂ hE2 h2.le, hlt δ₁ h1.le, hlt δ₂ h2.le, hsum δ₁ h1.le, hsum δ₂ h2.le,
    hE1, hE12, ENNReal.ofReal_ne_top, hprob,
    fun m => map_eval_pathMeasure_ballWalk_uniformOn measurableSet_ball δ₁ m,
    fun m => map_eval_pathMeasure_ballWalk_uniformOn measurableSet_ball δ₂ m⟩

end BallWalkPath

/-! ## Axiom audit

Every theorem of this file, re-checked at elaboration time.  Each must print exactly
`[propext, Classical.choice, Quot.sound]`; anything else — in particular the axiom emitted
by an unfinished proof — means the file is not finished. -/

#print axioms chainKernel_apply
#print axioms isMarkovKernel_chainKernel
#print axioms isProbabilityMeasure_pathMeasure
#print axioms bind_comap
#print axioms map_eval_pathMeasure_zero
#print axioms map_eval_pathMeasure_succ
#print axioms map_eval_pathMeasure_of_invariant
#print axioms condDistrib_pathMeasure
#print axioms measurableSet_holdsUntil
#print axioms measurableSet_constHistory
#print axioms preimage_frestrictLe_constHistory
#print axioms pathMeasure_dirac_holdsUntil
#print axioms ballWalk_apply_singleton
#print axioms pathMeasure_ballWalk_dirac_holdsUntil
#print axioms tsum_pathMeasure_ballWalk_dirac_holdsUntil
#print axioms lintegral_exitTime_pathMeasure_ballWalk
#print axioms condDistrib_pathMeasure_ballWalk
#print axioms map_eval_pathMeasure_ballWalk_uniformOn
#print axioms ell_unitBall_zero_of_one_le
#print axioms exists_trajTransfer_witness

end Arlib.MarkovChains
