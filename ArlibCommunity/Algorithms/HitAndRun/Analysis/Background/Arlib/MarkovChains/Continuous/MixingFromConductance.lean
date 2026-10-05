/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.Warmness

/-!
# Mixing of a continuous-state Markov chain: from a decay rate to a step count

A sampler that runs a Markov chain has to be told **how many steps to take**.  What the
theory of conductance supplies is not a step count but a *rate*: Lovász–Simonovits, quoted
as Theorem 4.1 by Cousins–Vempala (`vol3_journal.tex:523`), state that for a lazy chain of
conductance `phi` started from an `M`-warm distribution,

`d_TV(Q_t, Q) ≤ √M · (1 − phi²/2)^t`.

Mathlib v4.32 has Markov kernels and invariance but no chain iterate as a measure, no
mixing predicate, no quantitative convergence rate and no conductance on a general
measurable space (`CV-ROADMAP.md` §3).  The chain layer — `step`, `iterate`, `MixesWithin`,
the data-processing inequality and the monotonicity of the distance to stationarity — is
supplied by `Arlib.MarkovChains.Continuous.Warmness`, which this module imports and builds
on.  What is added here is the *quantitative* half: the arithmetic that converts a decay
rate into an explicit number of steps, and the first step of the Cheeger dictionary that
relates the conductance of a set to a Rayleigh quotient of the Dirichlet form.

## What is proved here

*Geometric decay ⟹ an explicit mixing time* — pure real analysis, and the step that
actually turns a conductance into a number a sampler can use.

* `mixingTime M c eps = ⌈log (M / eps) / c⌉` and `mul_pow_le_of_mixingTime_le`:
  `M (1 − c)^t ≤ eps` for every `t ≥ mixingTime M c eps`, when `0 < c ≤ 1`, `0 < M`,
  `0 < eps`.  Proved through `1 − c ≤ exp (−c)` (`one_sub_pow_le_exp_neg_mul`).
* `tv_le_of_geometric_decay`, `exists_tv_le_of_geometric_decay` — the same statement fed a
  hypothesis `∀ t, tv t ≤ M (1 − c)^t`; the second is the bare existence of a mixing time.
* `mixingTime_le` — `mixingTime M c eps ≤ log (M / eps) / c + 1`.
* `conductanceMixingTime M phi eps = mixingTime (√M) (phi²/2) eps`, with
  `tv_le_of_conductance_decay` and `conductanceMixingTime_le`, the latter reading
  `conductanceMixingTime M phi eps ≤ (log M + 2 log (1/eps)) / phi² + 1`.  That is exactly
  the `O(phi⁻² log (M / eps))` of the informal statement, with the constants visible.

*The bridge to the chain layer.*

* `mixesWithin_of_conductance_decay` — from the Lovász–Simonovits decay bound *as a
  hypothesis*, `Arlib.MarkovChains.MixesWithin` (of `Warmness`) holds to within `eps` at
  every `t ≥ conductanceMixingTime`.
* `mixesWithin_of_invariant` — started at stationarity the chain is already mixed, at every
  time and with error `0`.

*Non-vacuity (`CLAUDE.md` §11).*

* `exists_conductance_pos_and_mixesWithin` — `Kernel.const Bool piHalf` has conductance
  exactly `1/2` (`conductance_const_piHalf`) and, by `mixesWithin_const` of `Warmness`,
  satisfies `MixesWithin _ _ mu0 1 0` *from every start*.  So the class of chains a
  hypothesis `phi ≤ conductance P pi` ranges over is inhabited by a chain that really does
  mix, and `MixesWithin` is not a predicate nothing satisfies.

*A first step of the Cheeger dictionary.*

* `dirichletForm P pi f = (∫∫ (f x − f y)² dP_x dpi) / 2`, valued in `ℝ≥0∞` so that no
  integrability hypothesis is ever needed.
* `dirichletForm_indicator` — at an indicator the Dirichlet form is the symmetrised flow
  `(flow S Sᶜ + flow Sᶜ S)/2`; `dirichletForm_indicator_of_isReversible` — under detailed
  balance it is the escape flow `flow S Sᶜ` itself; `conductanceOn_eq_dirichletForm_div` —
  hence `Φ(S)` is the Rayleigh quotient `E(1_S, 1_S) / pi(S)`.

## What is taken from `Warmness` rather than reproved here

`step`, `step_apply`, `iterate`, `iterate_zero`, `iterate_succ`, `iterate_one`,
`iterate_invariant`, the `IsProbabilityMeasure` instances, `lintegral_le_of_tvLe` (the
layer-cake step), `tvLe_step` and `tvLe_iterate` (data processing), `tvLe_iterate_mono` and
`MixesWithin.mono_time` (the distance to stationarity is non-increasing), `MixesWithin`
itself with `mixesWithin_iff` and `MixesWithin.mono_err`, and the instantly-mixing kernel
lemmas `step_const_eq` and `mixesWithin_const`.

## What is NOT proved here, and is not assumed either

**The Cheeger inequality `spectralGap ≥ phi²/2`, and with it the decay bound
`d_TV(Q_t, Q) ≤ √M (1 − phi²/2)^t`, are not proved in this file.**  They are also *not*
assumed: there is no `def` or `structure` field in this module that names either statement
and stands in for its proof, which is the failure mode `CLAUDE.md` §11 and
`AUDIT-KV97.md` §0 warn about, and which
`../gaussian-cooling-vempala/lean/GaussianCooling/Conductance.lean:439`
(`MixingFromConductance`) exhibits.  The decay bound enters the one theorem that needs it,
`mixesWithin_of_conductance_decay`, as an explicit hypothesis on the caller, so that
substituting a real proof later is a matter of supplying that argument.

Concretely, what is missing between `conductanceOn_eq_dirichletForm_div` and the decay
bound is: a variance functional on `ℝ≥0∞`-valued or `L²(pi)` functions, a definition of the
spectral gap as the infimum of `dirichletForm / variance`, the easy direction
`gap ≤ 2 · conductance` (which the indicator computation above already almost gives), the
hard direction `gap ≥ phi²/2`, and the passage from a spectral gap to `L²` — and then `TV`
— contraction of the iterate.  None of that is attempted here.

## References

* Lovász–Simonovits, *Random walks in a convex body and an improved volume algorithm*,
  RSA 1993.
* Cousins–Vempala, *Gaussian cooling and `O*(n³)` algorithms for volume and Gaussian
  volume*, §4.1 (`vol3_journal.tex:514–746`).
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ## Geometric decay -/

/-- `(1 - c)^t ≤ exp (-(c t))` for `c ≤ 1`. -/
theorem one_sub_pow_le_exp_neg_mul {c : ℝ} (hc1 : c ≤ 1) (t : ℕ) :
    (1 - c) ^ t ≤ Real.exp (-(c * t)) := by
  have h0 : (0 : ℝ) ≤ 1 - c := by linarith
  have h1 : 1 - c ≤ Real.exp (-c) := by
    have := Real.add_one_le_exp (-c)
    linarith
  calc (1 - c) ^ t ≤ Real.exp (-c) ^ t := pow_le_pow_left₀ h0 h1 t
    _ = Real.exp ((t : ℝ) * -c) := (Real.exp_nat_mul (-c) t).symm
    _ = Real.exp (-(c * t)) := by ring_nf

/-- The explicit mixing time `⌈log (M / ε) / c⌉`. -/
noncomputable def mixingTime (M c eps : ℝ) : ℕ := ⌈Real.log (M / eps) / c⌉₊

/-- After `mixingTime M c eps` steps the geometric bound `M (1-c)^t` is below `eps`. -/
theorem mul_pow_le_of_mixingTime_le {M c eps : ℝ} (hM : 0 < M) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (heps : 0 < eps) {t : ℕ} (ht : mixingTime M c eps ≤ t) : M * (1 - c) ^ t ≤ eps := by
  have hlog : Real.log (M / eps) ≤ c * t := by
    have h1 : Real.log (M / eps) / c ≤ (t : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast ht)
    have := (div_le_iff₀ hc0).1 h1
    linarith
  have h2 : M / eps ≤ Real.exp (c * t) := by
    have := Real.exp_le_exp.2 hlog
    rwa [Real.exp_log (by positivity)] at this
  have h3 : M ≤ eps * Real.exp (c * t) := by
    have := (div_le_iff₀ heps).1 h2
    linarith
  calc M * (1 - c) ^ t ≤ M * Real.exp (-(c * t)) :=
        mul_le_mul_of_nonneg_left (one_sub_pow_le_exp_neg_mul hc1 t) hM.le
    _ = M / Real.exp (c * t) := by rw [Real.exp_neg]; ring
    _ ≤ eps := by rw [div_le_iff₀ (Real.exp_pos _)]; linarith

/-- **Geometric decay gives a mixing time.** -/
theorem tv_le_of_geometric_decay {M c eps : ℝ} {tv : ℕ → ℝ} (hM : 0 < M) (hc0 : 0 < c)
    (hc1 : c ≤ 1) (heps : 0 < eps) (hdecay : ∀ t, tv t ≤ M * (1 - c) ^ t) {t : ℕ}
    (ht : mixingTime M c eps ≤ t) : tv t ≤ eps :=
  (hdecay t).trans (mul_pow_le_of_mixingTime_le hM hc0 hc1 heps ht)

/-- **Existence form.** -/
theorem exists_tv_le_of_geometric_decay {M c eps : ℝ} {tv : ℕ → ℝ} (hM : 0 < M) (hc0 : 0 < c)
    (hc1 : c ≤ 1) (heps : 0 < eps) (hdecay : ∀ t, tv t ≤ M * (1 - c) ^ t) :
    ∃ t : ℕ, tv t ≤ eps :=
  ⟨mixingTime M c eps, tv_le_of_geometric_decay hM hc0 hc1 heps hdecay le_rfl⟩

/-- The mixing time is at most `log (M / eps) / c + 1`. -/
theorem mixingTime_le {M c eps : ℝ} (hc0 : 0 < c) (heps : 0 < eps) (hle : eps ≤ M) :
    (mixingTime M c eps : ℝ) ≤ Real.log (M / eps) / c + 1 := by
  have h1 : (1 : ℝ) ≤ M / eps := (one_le_div heps).2 hle
  have h2 : 0 ≤ Real.log (M / eps) := Real.log_nonneg h1
  exact (Nat.ceil_lt_add_one (by positivity)).le

/-! ## The Lovász–Simonovits shape -/

/-- The mixing time in Lovász–Simonovits form: `c = phi²/2`, `M ↦ √M`. -/
noncomputable def conductanceMixingTime (M phi eps : ℝ) : ℕ :=
  mixingTime (Real.sqrt M) (phi ^ 2 / 2) eps

/-- **`√M (1 - phi²/2)^t ≤ eps` once `t ≥ conductanceMixingTime M phi eps`.** -/
theorem tv_le_of_conductance_decay {M phi eps : ℝ} {tv : ℕ → ℝ} (hM : 1 ≤ M) (hphi0 : 0 < phi)
    (hphi1 : phi ≤ 1) (heps : 0 < eps)
    (hdecay : ∀ t, tv t ≤ Real.sqrt M * (1 - phi ^ 2 / 2) ^ t) {t : ℕ}
    (ht : conductanceMixingTime M phi eps ≤ t) : tv t ≤ eps := by
  have hsq : phi ^ 2 ≤ 1 := by nlinarith
  refine tv_le_of_geometric_decay ?_ (by positivity) (by linarith) heps hdecay ht
  exact Real.sqrt_pos.2 (by linarith)

/-- **The `O(phi⁻² log (M / eps))` bound.** -/
theorem conductanceMixingTime_le {M phi eps : ℝ} (hM : 1 ≤ M) (hphi0 : 0 < phi) (heps : 0 < eps)
    (hle : eps ≤ Real.sqrt M) :
    (conductanceMixingTime M phi eps : ℝ)
      ≤ (Real.log M + 2 * Real.log (1 / eps)) / phi ^ 2 + 1 := by
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM
  have h := mixingTime_le (M := Real.sqrt M) (c := phi ^ 2 / 2) (eps := eps)
    (by positivity) heps hle
  refine h.trans_eq ?_
  have hlog : Real.log (Real.sqrt M / eps) = Real.log M / 2 + Real.log (1 / eps) := by
    rw [Real.log_div (Real.sqrt_ne_zero'.2 hMpos) heps.ne', Real.log_sqrt hMpos.le, one_div,
      Real.log_inv]
    ring
  rw [hlog]
  field_simp

/-! ## Converting a decay rate into a mixing time

The chain iterate `Arlib.MarkovChains.iterate` and the mixing predicate
`Arlib.MarkovChains.MixesWithin` are those of
`Arlib.MarkovChains.Continuous.Warmness`; nothing about them is redefined here. -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **`O(phi⁻² log (M / eps))` steps suffice**, given the Lovász–Simonovits decay bound.

The decay bound is a *hypothesis*, not something this file proves or assumes on the side:
see the module docstring.  Supplying it is the caller's obligation, and is exactly what a
proof of the Cheeger inequality would discharge. -/
theorem mixesWithin_of_conductance_decay {P : Kernel Ω Ω} {pi mu0 : Measure Ω} {M phi eps : ℝ}
    (hM : 1 ≤ M) (hphi0 : 0 < phi) (hphi1 : phi ≤ 1) (heps : 0 < eps)
    (hdecay : ∀ s : ℕ, TVLe (iterate P mu0 s) pi
      (ENNReal.ofReal (Real.sqrt M * (1 - phi ^ 2 / 2) ^ s)))
    {t : ℕ} (ht : conductanceMixingTime M phi eps ≤ t) :
    MixesWithin P pi mu0 t (ENNReal.ofReal eps) :=
  (hdecay t).mono (ENNReal.ofReal_le_ofReal
    (tv_le_of_conductance_decay (tv := fun s => Real.sqrt M * (1 - phi ^ 2 / 2) ^ s) hM hphi0
      hphi1 heps (fun _ => le_rfl) ht))

/-- Started at stationarity the chain is already mixed, at every `t` and with `eps = 0`. -/
theorem mixesWithin_of_invariant {P : Kernel Ω Ω} {pi : Measure Ω} (h : Kernel.Invariant P pi)
    (t : ℕ) : MixesWithin P pi pi t 0 := by
  rw [mixesWithin_iff, iterate_invariant h]
  exact TVLe.refl pi

/-! ## A non-vacuity witness

`Arlib.MarkovChains.exists_mixesWithin_and_conductance_eq` (in `Warmness`) already exhibits
one chain that is simultaneously a `MixesWithin _ _ _ 1 0` instance and a kernel of
conductance `1/2`.  The statement below strengthens it to *every* starting probability
measure, and additionally records invariance of the target, which is what the mixing
theorems above quantify over. -/

/-- **Non-vacuity witness (`CLAUDE.md` §11).** -/
theorem exists_conductance_pos_and_mixesWithin :
    ∃ (Om : Type) (_ : MeasurableSpace Om) (P : Kernel Om Om) (pi : Measure Om),
      IsMarkovKernel P ∧ IsProbabilityMeasure pi ∧ Kernel.Invariant P pi ∧
        conductance P pi = 1 / 2 ∧
        ∀ mu0 : Measure Om, IsProbabilityMeasure mu0 → MixesWithin P pi mu0 1 0 := by
  refine ⟨Bool, inferInstance, Kernel.const Bool piHalf, piHalf, inferInstance, inferInstance,
    (isReversible_const piHalf).invariant, conductance_const_piHalf, ?_⟩
  intro mu0 _
  exact mixesWithin_const piHalf mu0

/-! ## The Dirichlet form

The classical route from a conductance bound to the geometric decay hypothesis of
`mixesWithin_of_conductance_decay` runs through the Cheeger inequality, which compares the
conductance with the spectral gap of the chain.  **The Cheeger inequality is not proved in
this file, and nothing here assumes it**: what follows is only the first, elementary half
of the dictionary — the identification of the *Dirichlet form at an indicator* with the
*ergodic flow*, hence of the conductance of a set with a Rayleigh quotient of the Dirichlet
form.  See the module docstring for exactly what is and is not established. -/

/-- The **Dirichlet form** of `f`. -/
noncomputable def dirichletForm (P : Kernel Ω Ω) (pi : Measure Ω) (f : Ω → ℝ) : ℝ≥0∞ :=
  (∫⁻ x, ∫⁻ y, ENNReal.ofReal ((f x - f y) ^ 2) ∂(P x) ∂pi) / 2

/-- **A constant function has zero Dirichlet energy.** -/
@[simp] theorem dirichletForm_const (P : Kernel Ω Ω) (pi : Measure Ω) (c : ℝ) :
    dirichletForm P pi (fun _ => c) = 0 := by
  simp [dirichletForm]

/-- **The inner integral of the Dirichlet form at an indicator.** -/
theorem lintegral_kernel_sub_indicator_sq (P : Kernel Ω Ω) {S : Set Ω} (hS : MeasurableSet S)
    (x : Ω) :
    ∫⁻ y, ENNReal.ofReal ((Set.indicator S (fun _ => (1 : ℝ)) x
        - Set.indicator S (fun _ => (1 : ℝ)) y) ^ 2) ∂(P x)
      = Set.indicator S (fun x => P x Sᶜ) x + Set.indicator Sᶜ (fun x => P x S) x := by
  by_cases hx : x ∈ S
  · have hrw : (fun y => ENNReal.ofReal ((Set.indicator S (fun _ => (1 : ℝ)) x
        - Set.indicator S (fun _ => (1 : ℝ)) y) ^ 2))
        = Set.indicator Sᶜ (fun _ => (1 : ℝ≥0∞)) := by
      funext y
      by_cases hy : y ∈ S <;> simp [hx, hy]
    rw [hrw, lintegral_indicator hS.compl]
    simp [hx]
  · have hrw : (fun y => ENNReal.ofReal ((Set.indicator S (fun _ => (1 : ℝ)) x
        - Set.indicator S (fun _ => (1 : ℝ)) y) ^ 2))
        = Set.indicator S (fun _ => (1 : ℝ≥0∞)) := by
      funext y
      by_cases hy : y ∈ S <;> simp [hx, hy]
    rw [hrw, lintegral_indicator hS]
    simp [hx]

/-- **The Dirichlet form at an indicator is the symmetrised ergodic flow.** -/
theorem dirichletForm_indicator (P : Kernel Ω Ω) (pi : Measure Ω) {S : Set Ω}
    (hS : MeasurableSet S) :
    dirichletForm P pi (Set.indicator S (fun _ => (1 : ℝ)))
      = (flow P pi S Sᶜ + flow P pi Sᶜ S) / 2 := by
  rw [dirichletForm]
  congr 1
  calc ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((Set.indicator S (fun _ => (1 : ℝ)) x
          - Set.indicator S (fun _ => (1 : ℝ)) y) ^ 2) ∂(P x) ∂pi
      = ∫⁻ x, (Set.indicator S (fun x => P x Sᶜ) x
          + Set.indicator Sᶜ (fun x => P x S) x) ∂pi :=
        lintegral_congr fun x => lintegral_kernel_sub_indicator_sq P hS x
    _ = (∫⁻ x, Set.indicator S (fun x => P x Sᶜ) x ∂pi)
          + ∫⁻ x, Set.indicator Sᶜ (fun x => P x S) x ∂pi :=
        lintegral_add_right _ ((Kernel.measurable_coe P hS).indicator hS.compl)
    _ = flow P pi S Sᶜ + flow P pi Sᶜ S := by
        rw [lintegral_indicator hS, lintegral_indicator hS.compl]
        rfl

/-- **For a reversible chain the Dirichlet form at an indicator is the escape flow.** -/
theorem dirichletForm_indicator_of_isReversible {P : Kernel Ω Ω} {pi : Measure Ω}
    (hrev : IsReversible P pi) {S : Set Ω} (hS : MeasurableSet S) :
    dirichletForm P pi (Set.indicator S (fun _ => (1 : ℝ))) = flow P pi S Sᶜ := by
  rw [dirichletForm_indicator P pi hS, ← hrev S Sᶜ hS hS.compl, ← two_mul, mul_div_assoc,
    ENNReal.mul_div_cancel (by simp) (by simp)]

/-- **The conductance of a set is a Rayleigh quotient of the Dirichlet form.** -/
theorem conductanceOn_eq_dirichletForm_div {P : Kernel Ω Ω} {pi : Measure Ω}
    (hrev : IsReversible P pi) {S : Set Ω} (hS : MeasurableSet S) :
    conductanceOn P pi S = dirichletForm P pi (Set.indicator S (fun _ => (1 : ℝ))) / pi S := by
  rw [conductanceOn, dirichletForm_indicator_of_isReversible hrev hS]

end Arlib.MarkovChains
