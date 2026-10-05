/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Lattice.Rounding.ProdKernel
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Set integrals of the randomized-rounding kernel

`Arlib.Lattice.Rounding.integral_prodTent` says that the rounding kernel is a
probability density in the continuous variable:

  `∫ p, prodTent x p = 1`.

Theorem 2 of Kannan–Vempala, *Sampling Lattice Points* (STOC '97), never uses
that integral over all of `ℝⁿ`; it uses the integral over the body `P'` being
sampled,

  `Pr[rnd p = x] = ∫_{P'} ν(p) · prodTent x p dp`,

and it bounds that set integral from both sides:

* **upper**: `∫_{P'} prodTent x p dp ≤ ∫_{ℝⁿ} prodTent x p dp = 1`, because the
  integrand is nonnegative — this file's
  `Arlib.Lattice.Rounding.setIntegral_prodTent_le_one`;
* **lower**: `∫_{P'} prodTent x p dp = 1 − ∫_{P'ᶜ} prodTent x p dp`, so the
  deficit is exactly the mass that *escapes* `P'` — this file's
  `Arlib.Lattice.Rounding.setIntegral_prodTent_compl`.

Everything else here is the routine plumbing those two steps need: restriction of
integrability, nonnegativity, monotonicity in the domain, and the fact that all of
the kernel's mass already sits inside the paper's side-2 cube `C(x,1)`
(`Arlib.Lattice.Rounding.setIntegral_prodTent_roundBox`).

The last section restates the same content at the level of measures:
`Arlib.Lattice.Rounding.roundKernelMeasure x` is the probability measure with
density `prodTent x`, and
`Arlib.Lattice.Rounding.roundKernelMeasure_apply` is the bridge
`roundKernelMeasure x S = ENNReal.ofReal (∫ p in S, prodTent x p)`.
-/

namespace Arlib.Lattice.Rounding

open MeasureTheory

variable {n : ℕ}

/-- The kernel is integrable on every set: it is integrable on all of `ℝⁿ`, and
integrability is inherited by restriction. No measurability of `S` is needed. -/
theorem integrableOn_prodTent (x : EuclideanSpace ℝ (Fin n))
    (S : Set (EuclideanSpace ℝ (Fin n))) : IntegrableOn (prodTent x) S :=
  (integrable_prodTent x).integrableOn

/-- Every set integral of the kernel is nonnegative, the integrand being
nonnegative pointwise. -/
theorem setIntegral_prodTent_nonneg (x : EuclideanSpace ℝ (Fin n))
    (S : Set (EuclideanSpace ℝ (Fin n))) : 0 ≤ ∫ p in S, prodTent x p :=
  integral_nonneg fun p => prodTent_nonneg x p

/-- **The complement decomposition — the lower bound of Kannan–Vempala Theorem 2.**

`∫ p in S, prodTent x p = 1 - ∫ p in Sᶜ, prodTent x p`.

Since the kernel has total mass `1`, the mass it puts on `S` is `1` minus the
mass that *escapes* `S`. Taking `S = P'`, this is precisely the shape of the
lower bound `Pr[rnd p = x] ≥ (1 - escape mass) / Vol(P')`: one only has to bound
the escape integral `∫_{P'ᶜ}`, and no lower bound on `∫_{P'}` itself is ever
needed. -/
theorem setIntegral_prodTent_compl (x : EuclideanSpace ℝ (Fin n))
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S) :
    ∫ p in S, prodTent x p = 1 - ∫ p in Sᶜ, prodTent x p := by
  have h := integral_add_compl (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (s := S) hS (integrable_prodTent x)
  rw [integral_prodTent n x] at h
  linarith

/-- **The upper bound of Kannan–Vempala Theorem 2.**

`∫ p in S, prodTent x p ≤ 1` for every measurable `S`.

The kernel's total mass is `1` (`Arlib.Lattice.Rounding.integral_prodTent`) and it
is nonnegative, so no piece of `ℝⁿ` can carry more than all of it. With
`S = P'` this is the step that yields `Pr[rnd p = x] ≤ 1 / Vol(P')`. -/
theorem setIntegral_prodTent_le_one (x : EuclideanSpace ℝ (Fin n))
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S) :
    ∫ p in S, prodTent x p ≤ 1 := by
  have hcompl := setIntegral_prodTent_nonneg x Sᶜ
  rw [setIntegral_prodTent_compl x hS]
  linarith

/-- Set integrals of the kernel are monotone in the domain: enlarging the region
can only add nonnegative mass.

The measurability hypotheses are accepted for uniformity with the rest of the
file (and because callers always have them) but are not used: monotonicity of the
restricted measure suffices, hence the underscored names. -/
theorem setIntegral_prodTent_mono (x : EuclideanSpace ℝ (Fin n))
    {S T : Set (EuclideanSpace ℝ (Fin n))} (hST : S ⊆ T) (_hS : MeasurableSet S)
    (_hT : MeasurableSet T) :
    ∫ p in S, prodTent x p ≤ ∫ p in T, prodTent x p :=
  setIntegral_mono_set (integrableOn_prodTent x T)
    (Filter.Eventually.of_forall fun p => prodTent_nonneg x p) hST.eventuallyLE

/-- **All of the kernel's mass sits in the paper's cube `C(x,1)`.**

`∫ p in roundBox x, prodTent x p = 1`: the density vanishes off the side-2 box
about `x` (`Arlib.Lattice.Rounding.prodTent_eq_zero_of_notMem`), so the escape
integral in `Arlib.Lattice.Rounding.setIntegral_prodTent_compl` is zero there. -/
theorem setIntegral_prodTent_roundBox (x : EuclideanSpace ℝ (Fin n)) :
    ∫ p in roundBox x, prodTent x p = 1 := by
  have hzero : ∫ p in (roundBox x)ᶜ, prodTent x p = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun _ hp => prodTent_eq_zero_of_notMem hp
  rw [setIntegral_prodTent_compl x (measurableSet_roundBox x), hzero, sub_zero]

/-! ### The measure-level restatement -/

/-- **The law of `rnd p = x` as a measure.** The measure on `ℝⁿ` with density
`prodTent x` against Lebesgue measure; by
`Arlib.Lattice.Rounding.integral_prodTent` it is a probability measure. -/
noncomputable def roundKernelMeasure (x : EuclideanSpace ℝ (Fin n)) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity fun p => ENNReal.ofReal (prodTent x p)

/-- `Arlib.Lattice.Rounding.roundKernelMeasure` is a probability measure — the
`def`-level packaging of `Arlib.Lattice.Rounding.isProbabilityMeasure_withDensity_prodTent`. -/
instance isProbabilityMeasure_roundKernelMeasure (x : EuclideanSpace ℝ (Fin n)) :
    IsProbabilityMeasure (roundKernelMeasure x) :=
  isProbabilityMeasure_withDensity_prodTent x

/-- **The bridge between the integral and measure formulations.**

`roundKernelMeasure x S = ENNReal.ofReal (∫ p in S, prodTent x p)` for measurable
`S`: the mass the rounding kernel puts on `S` is exactly the set integral this
file bounds. Combined with
`Arlib.Lattice.Rounding.setIntegral_prodTent_le_one` and
`Arlib.Lattice.Rounding.setIntegral_prodTent_compl`, it turns those bounds into
statements about a probability measure. -/
theorem roundKernelMeasure_apply (x : EuclideanSpace ℝ (Fin n))
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S) :
    roundKernelMeasure x S = ENNReal.ofReal (∫ p in S, prodTent x p) := by
  rw [roundKernelMeasure, withDensity_apply _ hS,
    ← ofReal_integral_eq_lintegral_ofReal (integrableOn_prodTent x S)
      (Filter.Eventually.of_forall fun p => prodTent_nonneg x p)]

end Arlib.Lattice.Rounding
