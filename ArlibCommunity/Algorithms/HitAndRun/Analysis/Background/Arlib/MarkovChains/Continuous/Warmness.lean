/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Probability.TV
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.Conductance
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Running a Markov chain: warm starts, data processing, and the mixing interface

This module is the layer between a *conductance* bound (`Arlib.MarkovChains.conductance`)
and a usable statement about a sampler.  A conductance bound is about a kernel; a sampler
guarantee is about the *law of the chain after `t` steps* started from some initial
distribution.  The three things one has to know to get from one to the other are proved
here.

## The three facts

1. **The chain's law is `iterate P μ t`.** One step of a kernel `P` pushes a law `μ`
   forward to `μ.bind P` (`step`), and `t` steps iterate that (`iterate`).  A stationary
   `pi` is fixed by both (`step_invariant`, `iterate_invariant`).
2. **Warmness is preserved forever** (`isWarm_step`, `isWarm_iterate`).  If the start `μ`
   is `M`-warm with respect to the stationary `pi`, then so is `iterate P μ t` for *every*
   `t`.  This is the reason a mixing bound may quote a warmness parameter that the caller
   only ever checks at time zero — Cousins–Vempala, §4.2 (`vol3_journal.tex:747–826`),
   where `M(Q_i, Q_{i+1}) ≤ √e` is verified once per phase and then used at every step of
   the ball walk inside that phase.

   ⚠ **`√e` is CV's constant at CV's schedule `σ²ᵢ₊₁ = σ²ᵢ(1 + 1/n)`, and this repository's
   schedule binder is twice that rate** (`hcc : cc ≤ 1 + 2/n`, binder #33 of
   `Ttc.ttc_runtime_mn4`), which supports `M ≤ e`, not `√e`.  Both are proved:
   `Arlib.GaussianCooling.isWarm_coolLaw_succ_sqrt_exp` gives `√e` at `1 + 1/n`, and
   `isWarm_coolLaw_succ_exp` gives `e` at `1 + 2/n`
   (`Arlib/Convexity/GaussianCooling/WarmChain.lean`).  Nothing downstream depends on the
   value — `hMc : 1 ≤ Mcool` is a free binder — but do not quote `√e` for this repo's
   schedule.

   ⚠ **CV's proof of that lemma has an arithmetic slip at `vol3_journal.tex:787`**, which
   computes the partition-function ratio as `(1/(1 − 1/n))^{n/2} ≤ √e`.  That inequality is
   false for every `n ≥ 2` — the quantity decreases to `√e` from *above* (`2` at `n = 2`,
   `1.6529` at `n = 100`, against `√e = 1.64872`).  The hypothesis is
   `σ²ᵢ₊₁ = σ²ᵢ(1 + 1/n)`, so the ratio is `1 + 1/n` and the correct expression is
   `(1 + 1/n)^{n/2} ≤ √e`, which *is* true (it increases to `√e` from below).  **The lemma
   is correct; only the displayed step is wrong.**  `isWarm_coolLaw_succ_sqrt_exp` proves
   the lemma as stated, via the correct conversion.
3. **Total variation never increases** (`tvLe_step`, `tvLe_iterate`, and the corollary
   `tvLe_iterate_of_invariant_mono`).  Running the chain cannot move the law *away* from
   stationarity: the map `μ ↦ step P μ` is a contraction for total variation.  This is the
   data-processing inequality for a Markov kernel, which `Arlib.Probability.TV` explicitly
   leaves out (it has only the deterministic case `Arlib.TVLe.map`); the missing
   ingredient it names — a layer-cake argument moving a setwise bound past a lower
   integral — is `lintegral_le_of_tvLe` below.

## Main definitions

* `Arlib.MarkovChains.step P μ = μ.bind P` — one step of the chain.
* `Arlib.MarkovChains.iterate P μ t` — the law after `t` steps.
* `Arlib.MarkovChains.MixesWithin P pi μ t ε` — the interface a mixing theorem produces
  and a sampler consumes: `TVLe (iterate P μ t) pi ε`.

## Main results

* `Arlib.MarkovChains.isWarm_iterate` — **warmness propagates**.
* `Arlib.MarkovChains.lintegral_le_of_tvLe` — a `TVLe` bound passes through a lower
  integral of a `[0,1]`-valued function, with no loss.  The layer-cake step.
* `Arlib.MarkovChains.tvLe_iterate` — **data processing**: a kernel cannot increase total
  variation, at any number of steps.
* `Arlib.MarkovChains.mixesWithin_const` — the **non-vacuity witness** (`CLAUDE.md` §11):
  the instantly mixing kernel `Kernel.const Ω pi` satisfies `MixesWithin _ pi μ 1 0`, i.e.
  it reaches `pi` exactly, in one step, from any start.  Since
  `Arlib.MarkovChains.conductance_const_piHalf` computes the conductance of that same
  kernel to be `1/2`, the two layers are witnessed by one and the same chain and neither
  predicate is empty.

## Scope

Nothing here converts a conductance bound into a `MixesWithin`; that is the theorem this
file is the *target* of.  There is no spectral theory, no `s`-conductance, no lower bound
on the mixing time, and no continuous-time chain.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## One step of a chain -/

/-- **One step of the Markov chain with kernel `P`**, as a map on laws: if the current
state is distributed as `μ`, the next state is distributed as `μ.bind P`.

This is Mathlib's `P ∘ₘ μ` under a name that reads as an action on the *measure*, which is
the direction the sampler literature runs it in. -/
noncomputable def step (P : Kernel Ω Ω) (μ : Measure Ω) : Measure Ω := μ.bind P

/-- `step` is Mathlib's composition `P ∘ₘ μ`. -/
theorem step_eq_comp (P : Kernel Ω Ω) (μ : Measure Ω) : step P μ = P ∘ₘ μ := rfl

/-- **The law after one step, evaluated on an event**: `(step P μ) S = ∫ P_x(S) dμ(x)`,
the average over the starting point of the chance of landing in `S`. -/
theorem step_apply (P : Kernel Ω Ω) (μ : Measure Ω) {S : Set Ω} (hS : MeasurableSet S) :
    step P μ S = ∫⁻ x, P x S ∂μ :=
  Measure.bind_apply hS P.aemeasurable

/-- **A Markov kernel maps probability measures to probability measures.** -/
instance isProbabilityMeasure_step (P : Kernel Ω Ω) [IsMarkovKernel P] (μ : Measure Ω)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (step P μ) := by
  show IsProbabilityMeasure (P ∘ₘ μ)
  infer_instance

/-- **Invariance, in the notation of this file**: `pi` is invariant for `P` exactly when a
step of the chain leaves it where it is.  This is definitionally Mathlib's
`ProbabilityTheory.Kernel.Invariant`. -/
theorem step_eq_self_iff_invariant (P : Kernel Ω Ω) (pi : Measure Ω) :
    step P pi = pi ↔ Kernel.Invariant P pi := Iff.rfl

/-- **A stationary measure is unmoved by a step of the chain.** -/
theorem step_invariant {P : Kernel Ω Ω} {pi : Measure Ω} (h : Kernel.Invariant P pi) :
    step P pi = pi := h

/-- One step of the chain is monotone in the law: a pointwise larger start gives a
pointwise larger successor. -/
theorem step_mono (P : Kernel Ω Ω) {μ ν : Measure Ω} (h : μ ≤ ν) : step P μ ≤ step P ν := by
  refine Measure.le_iff.2 fun S hS => ?_
  rw [step_apply P μ hS, step_apply P ν hS]
  exact lintegral_mono' h le_rfl

/-! ## Running the chain for `t` steps -/

/-- **The law of the chain after `t` steps**, started from `μ` and driven by `P`. -/
noncomputable def iterate (P : Kernel Ω Ω) (μ : Measure Ω) : ℕ → Measure Ω
  | 0 => μ
  | t + 1 => step P (iterate P μ t)

/-- At time zero the chain is where it started. -/
@[simp] theorem iterate_zero (P : Kernel Ω Ω) (μ : Measure Ω) : iterate P μ 0 = μ := rfl

/-- The recursion defining `iterate`: one more step. -/
@[simp] theorem iterate_succ (P : Kernel Ω Ω) (μ : Measure Ω) (t : ℕ) :
    iterate P μ (t + 1) = step P (iterate P μ t) := rfl

/-- After one step the law is `step P μ`. -/
theorem iterate_one (P : Kernel Ω Ω) (μ : Measure Ω) : iterate P μ 1 = step P μ := rfl

/-- **The chain stays a probability distribution.** -/
instance isProbabilityMeasure_iterate (P : Kernel Ω Ω) [IsMarkovKernel P] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (t : ℕ) : IsProbabilityMeasure (iterate P μ t) := by
  induction t with
  | zero => rw [iterate_zero]; infer_instance
  | succ t ih => rw [iterate_succ]; exact isProbabilityMeasure_step P _

/-- **A stationary measure is a fixed point of the whole chain**, not just of one step:
started at `pi`, the chain is at `pi` at every time. -/
theorem iterate_invariant {P : Kernel Ω Ω} {pi : Measure Ω} (h : Kernel.Invariant P pi)
    (t : ℕ) : iterate P pi t = pi := by
  induction t with
  | zero => rfl
  | succ t ih => rw [iterate_succ, ih, step_invariant h]

/-! ## Warmness propagates along the chain

The definition `Arlib.IsWarm M μ pi` says `μ S ≤ M * pi S` for every measurable `S`.  The
content of this section is that the *same* `M` works at every time: a chain started from an
`M`-warm law is `M`-warm forever.  Consequently a mixing bound whose hypothesis is
"`μ` is `M`-warm" need only be checked at time zero, which is what makes the warm-start
bookkeeping of Cousins–Vempala §4.2 (`vol3_journal.tex:747–826`) a finite amount of work:
`M(Q_i, Q_{i+1}) ≤ √e` is established once per cooling phase and then holds throughout the
ball walk of that phase.

⚠ `√e` is CV's constant at CV's rate `1 + 1/n`; this repository's schedule binder is
`cc ≤ 1 + 2/n`, which supports `e`.  Both are now proved —
`Arlib.GaussianCooling.isWarm_coolLaw_succ_sqrt_exp` and `isWarm_coolLaw_succ_exp`
(`Arlib/Convexity/GaussianCooling/WarmChain.lean`) — and the module docstring above records
an arithmetic slip in CV's own proof of the `√e` lemma. -/

/-- Warmness is exactly domination by the scaled measure, `μ ≤ M • pi`.  This is the form
in which monotonicity of `step` can be applied to it. -/
theorem isWarm_iff_le_smul {M : ℝ≥0∞} (μ pi : Measure Ω) :
    IsWarm M μ pi ↔ μ ≤ M • pi := by
  rw [Measure.le_iff]
  exact forall_congr' fun S => forall_congr' fun _ => by
    rw [Measure.smul_apply, smul_eq_mul]

/-- **Warmness is preserved by one step of the chain.**  If `μ` is `M`-warm with respect to
a *stationary* `pi`, then so is `step P μ`.

The proof is one line of measure theory: warmness says `μ ≤ M • pi`, `step` is monotone,
and `step P (M • pi) = M • step P pi = M • pi` because `step` is linear and `pi` is
stationary. -/
theorem isWarm_step {M : ℝ≥0∞} {μ pi : Measure Ω} {P : Kernel Ω Ω} (h : IsWarm M μ pi)
    (hpi : step P pi = pi) : IsWarm M (step P μ) pi := by
  refine (isWarm_iff_le_smul _ _).2 ?_
  have hle : step P μ ≤ step P (M • pi) := step_mono P ((isWarm_iff_le_smul _ _).1 h)
  have hsm : step P (M • pi) = M • pi := by rw [step, Measure.bind_smul, ← step, hpi]
  rwa [hsm] at hle

/-- **Warmness is preserved forever.**  A chain started from an `M`-warm law is `M`-warm at
every time `t`, with the same `M`.  Induction on `t` from `isWarm_step`.

This is the structural fact behind every "warm start" hypothesis: the parameter `M` is a
property of the *initial* distribution alone, yet it bounds the chain at all later times. -/
theorem isWarm_iterate {M : ℝ≥0∞} {μ pi : Measure Ω} {P : Kernel Ω Ω} (h : IsWarm M μ pi)
    (hpi : step P pi = pi) (t : ℕ) : IsWarm M (iterate P μ t) pi := by
  induction t with
  | zero => rwa [iterate_zero]
  | succ t ih => rw [iterate_succ]; exact isWarm_step ih hpi

/-- The same statement with the hypothesis spelled as Mathlib's
`ProbabilityTheory.Kernel.Invariant`, which is how a caller who obtained stationarity from
`Arlib.MarkovChains.IsReversible.invariant` will be holding it. -/
theorem isWarm_iterate_of_invariant {M : ℝ≥0∞} {μ pi : Measure Ω} {P : Kernel Ω Ω}
    (h : IsWarm M μ pi) (hpi : Kernel.Invariant P pi) (t : ℕ) :
    IsWarm M (iterate P μ t) pi :=
  isWarm_iterate h (step_invariant hpi) t

/-! ## Data processing: a kernel cannot increase total variation

`Arlib.Probability.TV` proves the *deterministic* data-processing inequality
(`Arlib.TVLe.map`) and explicitly leaves out the kernel version, naming the missing
ingredient: a layer-cake argument moving a setwise bound past a lower integral.  That
ingredient is `lintegral_le_of_tvLe`, and `tvLe_step` is the inequality it buys. -/

/-- **A `TVLe` bound survives a lower integral of a `[0,1]`-valued observable**: for
measurable `f : Ω → ℝ≥0∞` with `f ≤ 1`,

  `∫⁻ f ∂μ ≤ ∫⁻ f ∂ν + ε`.

This is the `ℝ≥0∞` companion of `Arlib.TVLe.integral_le`, and unlike that lemma it needs
no finiteness of `ε` and no probability-measure hypothesis.

The proof is the layer cake `∫⁻ f ∂μ = ∫⁻_{t > 0} μ {f ≥ t} dt`
(`MeasureTheory.lintegral_eq_lintegral_meas_le`).  Because `f ≤ 1`, the tail set `{f ≥ t}`
is empty for `t > 1`, so only `t ∈ (0,1]` contributes; there the hypothesis gives
`μ {f ≥ t} ≤ ν {f ≥ t} + ε` pointwise, and `(0,1]` has Lebesgue measure `1`, so integrating
the slack costs exactly `ε` and no more. -/
theorem lintegral_le_of_tvLe {μ ν : Measure Ω} {ε : ℝ≥0∞} (h : TVLe μ ν ε) {f : Ω → ℝ≥0∞}
    (hf : Measurable f) (hf1 : ∀ x, f x ≤ 1) :
    ∫⁻ x, f x ∂μ ≤ ∫⁻ x, f x ∂ν + ε := by
  -- Move to the real-valued `g = f.toReal`, which is what the layer cake consumes.
  set g : Ω → ℝ := fun x => (f x).toReal with hgdef
  have hgm : Measurable g := hf.ennreal_toReal
  have hofReal : ∀ x, ENNReal.ofReal (g x) = f x := fun x =>
    ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (hf1 x))
  have hg1 : ∀ x, g x ≤ 1 := fun x => by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (hf1 x)
    simpa [hgdef] using this
  -- The tail sets.
  set A : ℝ → Set Ω := fun t => {x | t ≤ g x} with hAdef
  have hAm : ∀ t, MeasurableSet (A t) := fun t => measurableSet_le measurable_const hgm
  have hlayer : ∀ ρ : Measure Ω, ∫⁻ x, f x ∂ρ = ∫⁻ t in Ioi (0 : ℝ), ρ (A t) := by
    intro ρ
    have : ∫⁻ x, ENNReal.ofReal (g x) ∂ρ = ∫⁻ t in Ioi (0 : ℝ), ρ {x | t ≤ g x} :=
      lintegral_eq_lintegral_meas_le ρ
        (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hgm.aemeasurable
    simpa only [hofReal, hAdef] using this
  -- The slack, supported on `(0,1]`.
  set c : ℝ → ℝ≥0∞ := (Ioc (0 : ℝ) 1).indicator (fun _ => ε) with hcdef
  have hcm : Measurable c := measurable_const.indicator measurableSet_Ioc
  have hcint : ∫⁻ t in Ioi (0 : ℝ), c t = ε := by
    rw [hcdef, lintegral_indicator measurableSet_Ioc, setLIntegral_const,
      Measure.restrict_apply measurableSet_Ioc,
      Set.inter_eq_self_of_subset_left Set.Ioc_subset_Ioi_self]
    simp
  -- The pointwise bound on `(0, ∞)`.
  have hpt : ∀ t ∈ Ioi (0 : ℝ), μ (A t) ≤ ν (A t) + c t := by
    intro t ht
    rcases le_or_gt t 1 with ht1 | ht1
    · have hmem : t ∈ Ioc (0 : ℝ) 1 := ⟨ht, ht1⟩
      rw [hcdef, Set.indicator_of_mem hmem]
      exact (h (A t) (hAm t)).1
    · have hempty : A t = ∅ := by
        rw [hAdef]
        exact Set.eq_empty_of_forall_notMem fun x hx => absurd (hx.trans (hg1 x)) (not_le.2 ht1)
      simp [hempty]
  calc ∫⁻ x, f x ∂μ = ∫⁻ t in Ioi (0 : ℝ), μ (A t) := hlayer μ
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), (ν (A t) + c t) := by
        refine lintegral_mono_ae ?_
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        exact hpt t ht
    _ = (∫⁻ t in Ioi (0 : ℝ), ν (A t)) + ∫⁻ t in Ioi (0 : ℝ), c t :=
        lintegral_add_right _ hcm
    _ = ∫⁻ x, f x ∂ν + ε := by rw [← hlayer ν, hcint]

/-- **Data processing for a Markov kernel, one step.**  Running both laws through the same
kernel cannot increase the total variation distance between them.

Applied with `ν = pi` stationary this says the chain never moves *away* from its target:
whatever accuracy has been reached is kept. -/
theorem tvLe_step (P : Kernel Ω Ω) [IsMarkovKernel P] {μ ν : Measure Ω} {ε : ℝ≥0∞}
    (h : TVLe μ ν ε) : TVLe (step P μ) (step P ν) ε := by
  intro S hS
  have hfm : Measurable fun x => P x S := Kernel.measurable_coe P hS
  have hf1 : ∀ x, P x S ≤ 1 := fun _ => prob_le_one
  rw [step_apply P μ hS, step_apply P ν hS]
  exact ⟨lintegral_le_of_tvLe h hfm hf1, lintegral_le_of_tvLe h.symm hfm hf1⟩

/-- **Data processing for a Markov kernel, `t` steps.**  Two chains driven by the same
kernel from starts within `ε` stay within `ε` forever. -/
theorem tvLe_iterate (P : Kernel Ω Ω) [IsMarkovKernel P] {μ ν : Measure Ω} {ε : ℝ≥0∞}
    (h : TVLe μ ν ε) (t : ℕ) : TVLe (iterate P μ t) (iterate P ν t) ε := by
  induction t with
  | zero => exact h
  | succ t ih => exact tvLe_step P ih

/-- Running the chain for `s + t` steps is running it for `s` steps and then restarting
from the law that has been reached. -/
theorem iterate_add (P : Kernel Ω Ω) (μ : Measure Ω) (s t : ℕ) :
    iterate P μ (s + t) = iterate P (iterate P μ s) t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [← Nat.add_assoc, iterate_succ, iterate_succ, ih]

/-- **One more step never hurts.**  If the chain is within `ε` of a stationary `pi`, it is
still within `ε` after another step: `pi` is a fixed point, so `tvLe_step` compares the
next law against `pi` itself. -/
theorem tvLe_step_of_invariant {P : Kernel Ω Ω} [IsMarkovKernel P] {μ pi : Measure Ω}
    {ε : ℝ≥0∞} (hpi : step P pi = pi) (h : TVLe μ pi ε) : TVLe (step P μ) pi ε := by
  have := tvLe_step P h
  rwa [hpi] at this

/-- **The distance to stationarity is non-increasing in time.**  Once the chain is within
`ε` of `pi` at some time `t`, it is within `ε` at every later time `t'`.

This is what makes a mixing statement usable as a *deadline* ("run at least `t` steps")
rather than as an instruction to stop at an exact time. -/
theorem tvLe_iterate_mono {P : Kernel Ω Ω} [IsMarkovKernel P] {μ pi : Measure Ω} {ε : ℝ≥0∞}
    (hpi : step P pi = pi) {t t' : ℕ} (htt' : t ≤ t') (h : TVLe (iterate P μ t) pi ε) :
    TVLe (iterate P μ t') pi ε := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le htt'
  rw [iterate_add]
  have hstat : iterate P pi d = pi := iterate_invariant hpi d
  have := tvLe_iterate P h d
  rwa [hstat] at this

/-! ## The mixing interface

`MixesWithin` is the contract between the two halves of a sampler correctness proof: a
quantitative mixing theorem (conductance in, a time bound out) *produces* it, and a caller
who wants an approximate sample *consumes* it.  Stating it as a named predicate rather than
as a bare `TVLe` keeps the two sides from having to agree on the spelling of "the law of
the chain after `t` steps". -/

/-- **The sampler guarantee**: started from `μ₀` and run for `t` steps, the chain with
kernel `P` is within total variation distance `ε` of `pi`. -/
def MixesWithin (P : Kernel Ω Ω) (pi : Measure Ω) (μ₀ : Measure Ω) (t : ℕ) (ε : ℝ≥0∞) : Prop :=
  TVLe (iterate P μ₀ t) pi ε

/-- Unfolding lemma for `MixesWithin`. -/
theorem mixesWithin_iff (P : Kernel Ω Ω) (pi μ₀ : Measure Ω) (t : ℕ) (ε : ℝ≥0∞) :
    MixesWithin P pi μ₀ t ε ↔ TVLe (iterate P μ₀ t) pi ε := Iff.rfl

/-- **A mixing bound is a deadline, not an appointment**: running longer is always safe. -/
theorem MixesWithin.mono_time {P : Kernel Ω Ω} [IsMarkovKernel P] {pi μ₀ : Measure Ω}
    {t t' : ℕ} {ε : ℝ≥0∞} (hpi : step P pi = pi) (h : MixesWithin P pi μ₀ t ε)
    (htt' : t ≤ t') : MixesWithin P pi μ₀ t' ε :=
  tvLe_iterate_mono hpi htt' h

/-- **A mixing bound may always be weakened.** -/
theorem MixesWithin.mono_err {P : Kernel Ω Ω} {pi μ₀ : Measure Ω} {t : ℕ} {ε ε' : ℝ≥0∞}
    (h : MixesWithin P pi μ₀ t ε) (hε : ε ≤ ε') : MixesWithin P pi μ₀ t ε' :=
  TVLe.mono h hε

/-- **What the caller gets.**  A probability computed for the target `pi` is valid for the
sample the chain actually produces, degraded by exactly the mixing error. -/
theorem MixesWithin.measure_le_add {P : Kernel Ω Ω} {pi μ₀ : Measure Ω} {t : ℕ} {ε p : ℝ≥0∞}
    (h : MixesWithin P pi μ₀ t ε) {S : Set Ω} (hS : MeasurableSet S) (hp : pi S ≤ p) :
    iterate P μ₀ t S ≤ p + ε :=
  TVLe.measure_le_add h hS hp

/-- **A warm start stays warm all the way to the deadline.**  Packaging `isWarm_iterate`
next to `MixesWithin`: at the time the mixing bound is quoted, the chain still satisfies the
warmness hypothesis that was checked at time zero. -/
theorem isWarm_of_mixesWithin {M : ℝ≥0∞} {P : Kernel Ω Ω} {pi μ₀ : Measure Ω}
    (h : IsWarm M μ₀ pi) (hpi : step P pi = pi) (t : ℕ) : IsWarm M (iterate P μ₀ t) pi :=
  isWarm_iterate h hpi t

/-! ## A non-vacuity witness

`CLAUDE.md` §11: a predicate that nothing satisfies makes every theorem about it vacuous.
The instantly mixing kernel `Kernel.const Ω pi` — resample from `pi` at every step —
satisfies `MixesWithin` with `t = 1` and `ε = 0`, the strongest possible instance.  It is
the *same* kernel whose conductance `Arlib.MarkovChains.conductance_const_piHalf` computes
to be exactly `1/2`, so a single chain witnesses both layers and neither is empty. -/

/-- **One step of the instantly mixing kernel** discards the starting law entirely and
returns `pi`, scaled by the total mass that was there. -/
theorem step_const (pi μ : Measure Ω) : step (Kernel.const Ω pi) μ = μ Set.univ • pi :=
  Measure.const_comp

/-- From *any* probability measure, one step of `Kernel.const Ω pi` lands exactly on `pi`. -/
theorem step_const_eq (pi μ : Measure Ω) [IsProbabilityMeasure μ] :
    step (Kernel.const Ω pi) μ = pi := by
  rw [step_const, measure_univ, one_smul]

/-- `pi` is of course invariant for the kernel that resamples from `pi`. -/
theorem invariant_const (pi : Measure Ω) [IsProbabilityMeasure pi] :
    Kernel.Invariant (Kernel.const Ω pi) pi :=
  step_const_eq pi pi

/-- **Non-vacuity witness for `MixesWithin`.**  The instantly mixing kernel reaches its
target exactly — error `0` — in one step, from any starting probability measure. -/
theorem mixesWithin_const (pi μ₀ : Measure Ω) [IsProbabilityMeasure μ₀] :
    MixesWithin (Kernel.const Ω pi) pi μ₀ 1 0 := by
  rw [mixesWithin_iff, iterate_one, step_const_eq]
  exact TVLe.refl pi

/-- **The witness in the form the vacuity check wants**, and the bridge to the conductance
layer: one concrete chain — the uniform resampler on the two-point space — is simultaneously
a `MixesWithin _ _ _ 1 0` instance and a kernel of conductance exactly `1/2`.

So neither `Arlib.MarkovChains.MixesWithin` nor `Arlib.MarkovChains.conductance` is a
predicate that nothing satisfies, and the two layers are consistent: the chain that mixes
instantly is the one with the large conductance. -/
theorem exists_mixesWithin_and_conductance_eq :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Kernel Ω Ω) (pi μ₀ : Measure Ω),
      IsMarkovKernel P ∧ IsProbabilityMeasure pi ∧ IsProbabilityMeasure μ₀ ∧
        Kernel.Invariant P pi ∧ MixesWithin P pi μ₀ 1 0 ∧ conductance P pi = 1 / 2 :=
  ⟨Bool, inferInstance, Kernel.const Bool piHalf, piHalf, Measure.dirac true, inferInstance,
    inferInstance, inferInstance, invariant_const piHalf, mixesWithin_const _ _,
    conductance_const_piHalf⟩

end Arlib.MarkovChains
