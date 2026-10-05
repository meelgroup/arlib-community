/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Lattice.Rounding.Tent
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.Basic

/-!
# The law of independent coordinatewise randomized rounding on `ℤⁿ`

`Arlib.Lattice.Rounding.tent` is the displacement density `1 − |u|` read in the
*continuous* variable: for a fixed lattice point, it is the density of the point
being rounded. This file reads the very same kernel in the **lattice** variable.

Fix a real `a` and round it as `⌊a⌋ + Bernoulli(a − ⌊a⌋)`. The resulting law on
`ℤ` puts mass `tent (a − m)` on each integer `m`, and `tent (a − ·)` vanishes off
`{⌊a⌋, ⌊a⌋ + 1}` (`tent_eq_zero_of_ne_floor`), where it takes the two Bernoulli
weights `1 − (a − ⌊a⌋)` and `a − ⌊a⌋`. So the law is the two-point measure
`tentInt a` (`tentInt_eq_two_point`), presented uniformly as a density against
counting measure so that the `n`-fold product `roundLaw p` is a plain
`MeasureTheory.Measure.pi`.

That product presentation gives the three facts an analysis of the rounding error
consumes, all by transfer from one coordinate:

* boundedness — `|a − m| ≤ 1` almost surely (`ae_latDisp_mem_Icc`);
* mean zero — `∫ (a − m) = 0` (`integral_latDisp_eq_zero`);
* independence across coordinates (`iIndepFun_latDisp`).

Everything here depends only on `Arlib.Lattice.Rounding.Tent` and Mathlib.
-/

namespace Arlib.Lattice.Rounding

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ## The tent is a two-point mass on the integers -/

/-- Only `⌊a⌋` and `⌊a⌋ + 1` are within distance `1` of `a`, so the tent read in
the lattice variable is supported on exactly those two integers. -/
theorem tent_eq_zero_of_ne_floor (a : ℝ) (m : ℤ) (h : m ≠ ⌊a⌋) (h2 : m ≠ ⌊a⌋ + 1) :
    tent (a - m) = 0 := by
  refine tent_eq_zero_of_one_le ?_
  rcases lt_or_gt_of_ne h with hm | hm
  · have : (m : ℝ) ≤ (⌊a⌋ : ℝ) - 1 := by exact_mod_cast Int.le_sub_one_of_lt hm
    have hfl : (⌊a⌋ : ℝ) ≤ a := Int.floor_le a
    rw [abs_of_nonneg (by linarith)]; linarith
  · have : (⌊a⌋ : ℝ) + 2 ≤ (m : ℝ) := by exact_mod_cast (by omega : ⌊a⌋ + 2 ≤ m)
    have hfl : a < (⌊a⌋ : ℝ) + 1 := Int.lt_floor_add_one a
    rw [abs_of_nonpos (by linarith)]; linarith

/-- The mass at `⌊a⌋` is the Bernoulli failure probability `1 − (a − ⌊a⌋)`. -/
theorem tent_sub_floor (a : ℝ) : tent (a - ⌊a⌋) = 1 - (a - ⌊a⌋) := by
  have h1 : (0:ℝ) ≤ a - ⌊a⌋ := by linarith [Int.floor_le a]
  have h2 : a - ⌊a⌋ < 1 := by linarith [Int.lt_floor_add_one a]
  rw [tent_of_abs_le (by rw [abs_of_nonneg h1]; linarith), abs_of_nonneg h1]

/-- The mass at `⌊a⌋ + 1` is the Bernoulli success probability `a − ⌊a⌋`. -/
theorem tent_sub_floor_succ (a : ℝ) : tent (a - (⌊a⌋ + 1 : ℤ)) = a - ⌊a⌋ := by
  have h1 : (0:ℝ) ≤ a - ⌊a⌋ := by linarith [Int.floor_le a]
  have h2 : a - ⌊a⌋ < 1 := by linarith [Int.lt_floor_add_one a]
  have h3 : a - ((⌊a⌋ : ℝ) + 1) ≤ 0 := by linarith
  push_cast
  rw [tent_of_abs_le (by rw [abs_of_nonpos h3]; linarith), abs_of_nonpos h3]
  ring

/-- The two contributing values sum to `1`: `(1 − {a}) + {a}`. -/
theorem tent_floor_add (a : ℝ) : tent (a - ⌊a⌋) + tent (a - (⌊a⌋ + 1 : ℤ)) = 1 := by
  rw [tent_sub_floor, tent_sub_floor_succ]; ring

/-- The tent is supported on two integers, hence summable. -/
theorem summable_tent (a : ℝ) : Summable (fun m : ℤ => tent (a - m)) := by
  classical
  refine summable_of_ne_finset_zero (s := ({⌊a⌋, ⌊a⌋ + 1} : Finset ℤ)) ?_
  intro m hm
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
  exact tent_eq_zero_of_ne_floor a m hm.1 hm.2

/-- **Partition of unity on the lattice**: the two-point masses sum to one. -/
theorem sum_tent (a : ℝ) : ∑' m : ℤ, tent (a - m) = 1 := by
  classical
  rw [tsum_eq_sum (s := ({⌊a⌋, ⌊a⌋ + 1} : Finset ℤ)) ?_]
  · rw [Finset.sum_insert (by simp), Finset.sum_singleton]; exact tent_floor_add a
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    exact tent_eq_zero_of_ne_floor a m hm.1 hm.2

/-! ## The one-dimensional rounding law -/

/-- **The one-dimensional rounding law**: `⌊a⌋ + Bernoulli(a − ⌊a⌋)`, presented as
the tent density against counting measure on `ℤ`. -/
noncomputable def tentInt (a : ℝ) : Measure ℤ :=
  (Measure.count : Measure ℤ).withDensity (fun m => ENNReal.ofReal (tent (a - m)))

/-- The point masses of `tentInt a` are the tent's values. -/
@[simp] theorem tentInt_singleton (a : ℝ) (m : ℤ) :
    tentInt a {m} = ENNReal.ofReal (tent (a - m)) := by
  rw [tentInt, withDensity_apply _ (measurableSet_singleton m)]
  simp [Measure.restrict_singleton, lintegral_dirac]

/-- `tentInt a` is a probability measure, by `Arlib.Lattice.Rounding.sum_tent`. -/
instance isProbabilityMeasure_tentInt (a : ℝ) : IsProbabilityMeasure (tentInt a) := by
  constructor
  rw [tentInt, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_count, ← ENNReal.ofReal_tsum_of_nonneg (fun m => tent_nonneg _) (summable_tent a),
    sum_tent, ENNReal.ofReal_one]

/-- **The rounding law in one coordinate is supported on `{⌊a⌋, ⌊a⌋+1}`**, with the
Bernoulli weights as masses. This is the presentation every statement below is
proved from: it turns integrals against `tentInt` into two-term sums. -/
theorem tentInt_eq_two_point (a : ℝ) :
    tentInt a = ENNReal.ofReal (tent (a - ⌊a⌋)) • Measure.dirac ⌊a⌋
      + ENNReal.ofReal (tent (a - (⌊a⌋ + 1 : ℤ))) • Measure.dirac (⌊a⌋ + 1) := by
  have hd : ∀ x y : ℤ, (Measure.dirac x) ({y} : Set ℤ) = if x = y then 1 else 0 := by
    intro x y
    rw [Measure.dirac_apply]
    by_cases h : x = y <;> simp [h]
  refine Measure.ext_of_singleton fun m => ?_
  rw [tentInt_singleton, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    smul_eq_mul, smul_eq_mul, hd, hd]
  by_cases h1 : m = ⌊a⌋
  · subst h1
    rw [if_pos rfl, if_neg (by omega), mul_one, mul_zero, add_zero]
  · by_cases h2 : m = ⌊a⌋ + 1
    · subst h2
      rw [if_neg (by omega), if_pos rfl, mul_one, mul_zero, zero_add]
    · rw [if_neg (Ne.symm h1), if_neg (Ne.symm h2), mul_zero, mul_zero, add_zero,
        tent_eq_zero_of_ne_floor a m h1 h2, ENNReal.ofReal_zero]

/-! ## Integration against the one-dimensional law -/

/-- **Everything is integrable against a two-point law.** -/
theorem integrable_tentInt (a : ℝ) (f : ℤ → ℝ) : Integrable f (tentInt a) := by
  rw [tentInt_eq_two_point]
  refine integrable_add_measure.2 ⟨?_, ?_⟩ <;>
    exact (integrable_dirac (by finiteness)).smul_measure (by finiteness)

/-- **Every integral against `tentInt a` is a two-term sum.** -/
theorem integral_tentInt (a : ℝ) (f : ℤ → ℝ) :
    ∫ m, f m ∂(tentInt a)
      = tent (a - ⌊a⌋) * f ⌊a⌋ + tent (a - (⌊a⌋ + 1 : ℤ)) * f (⌊a⌋ + 1) := by
  have hint : ∀ (x : ℝ) (z : ℤ), Integrable f (ENNReal.ofReal x • Measure.dirac z) :=
    fun x z => (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top
  rw [tentInt_eq_two_point, integral_add_measure (hint _ _) (hint _ _),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal (tent_nonneg _), ENNReal.toReal_ofReal (tent_nonneg _),
    smul_eq_mul, smul_eq_mul]

/-- **Mean zero, one coordinate**: the rounding displacement `a − rnd a` has mean
zero. With `t = a − ⌊a⌋` the two-term sum is `(1−t)·t + t·(t−1) = 0`. -/
theorem integral_tentInt_disp (a : ℝ) : ∫ m : ℤ, (a - (m : ℝ)) ∂(tentInt a) = 0 := by
  rw [integral_tentInt a (fun m => a - (m : ℝ)), tent_sub_floor, tent_sub_floor_succ]
  push_cast
  ring

/-- A set on which the tent vanishes is null for `tentInt a`. -/
theorem tentInt_eq_zero_of_forall (a : ℝ) {s : Set ℤ} (hs : ∀ m ∈ s, tent (a - m) = 0) :
    tentInt a s = 0 := by
  rw [tentInt_eq_two_point]
  have hz : ∀ z : ℤ, ENNReal.ofReal (tent (a - z)) * Measure.dirac z s = 0 := by
    intro z
    by_cases hz : z ∈ s
    · rw [hs z hz, ENNReal.ofReal_zero, zero_mul]
    · rw [Measure.dirac_apply, Set.indicator_of_notMem hz, mul_zero]
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    hz, hz, add_zero]

/-- **Boundedness, one coordinate**: the displacement lies in `[−1,1]` almost
surely, because the tent vanishes outside. -/
theorem ae_tentInt_mem_Icc (a : ℝ) :
    ∀ᵐ m : ℤ ∂(tentInt a), a - (m : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [ae_iff]
  refine tentInt_eq_zero_of_forall a fun m hm => tent_eq_zero_of_one_le ?_
  simp only [Set.mem_setOf_eq, Set.mem_Icc, not_and_or, not_le] at hm
  rcases hm with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

/-! ## The `n`-dimensional law

`roundLaw p` is a `MeasureTheory.Measure.pi`, so each of the three facts above
transfers coordinatewise: the marginals are the `tentInt (p k)` (via
`MeasureTheory.measurePreserving_eval`), and independence is
`ProbabilityTheory.iIndepFun_pi`.
-/

variable {n : ℕ}

/-- **The rounding law on `ℤⁿ`** for a fixed `p`: independent coordinates, each a
one-dimensional rounding law. -/
noncomputable def roundLaw (p : Fin n → ℝ) : Measure (Fin n → ℤ) :=
  Measure.pi (fun i => tentInt (p i))

/-- The `n`-dimensional rounding law is a probability measure. -/
instance isProbabilityMeasure_roundLaw (p : Fin n → ℝ) :
    IsProbabilityMeasure (roundLaw p) := by
  rw [roundLaw]; infer_instance

/-- **The point masses are the product kernel**: `Pr[rnd p = z] = ∏ᵢ tent(pᵢ − zᵢ)`. -/
theorem roundLaw_singleton (p : Fin n → ℝ) (z : Fin n → ℤ) :
    roundLaw p {z} = ENNReal.ofReal (∏ i, tent (p i - z i)) := by
  have hbox : ({z} : Set (Fin n → ℤ)) = Set.univ.pi (fun i => ({z i} : Set ℤ)) := by
    ext w
    constructor
    · rintro rfl; intro i _; rfl
    · intro hw
      funext i
      exact hw i (Set.mem_univ i)
  rw [roundLaw, hbox, Measure.pi_pi]
  simp only [tentInt_singleton]
  rw [ENNReal.ofReal_prod_of_nonneg fun i _ => tent_nonneg _]

/-- The rounding displacement in coordinate `k`, as a measurable function. -/
theorem measurable_latDisp (p : Fin n → ℝ) (k : Fin n) :
    Measurable (fun z : Fin n → ℤ => p k - (z k : ℝ)) :=
  measurable_const.sub (Measurable.of_discrete.comp (measurable_pi_apply k))

/-- The `k`-th marginal of `roundLaw p` is the one-dimensional law `tentInt (p k)`. -/
theorem measurePreserving_roundLaw_eval (p : Fin n → ℝ) (k : Fin n) :
    MeasurePreserving (Function.eval k) (roundLaw p) (tentInt (p k)) :=
  measurePreserving_eval (fun i => tentInt (p i)) k

/-- **Boundedness**: the displacement lies in `[−1,1]` in each coordinate, almost
surely under the fixed-`p` law. -/
theorem ae_latDisp_mem_Icc (p : Fin n → ℝ) (k : Fin n) :
    ∀ᵐ z ∂(roundLaw p), p k - (z k : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
  have h := ae_tentInt_mem_Icc (p k)
  rw [ae_iff] at h ⊢
  have hpre : {z : Fin n → ℤ | ¬ (p k - (z k : ℝ) ∈ Set.Icc (-1 : ℝ) 1)}
      = Function.eval k ⁻¹' {m : ℤ | ¬ (p k - (m : ℝ) ∈ Set.Icc (-1 : ℝ) 1)} := rfl
  rw [hpre, (measurePreserving_roundLaw_eval p k).measure_preimage
    ((Set.to_countable _).measurableSet).nullMeasurableSet]
  exact h

/-- **Mean zero**: each coordinate of the displacement has mean zero under the
fixed-`p` law. -/
theorem integral_latDisp_eq_zero (p : Fin n → ℝ) (k : Fin n) :
    ∫ z, (p k - (z k : ℝ)) ∂(roundLaw p) = 0 := by
  have h := MeasureTheory.integral_comp_eval (μ := fun i => tentInt (p i)) (i := k)
    (f := fun m : ℤ => p k - (m : ℝ)) (integrable_tentInt (p k) _).aestronglyMeasurable
  rw [roundLaw, h]
  exact integral_tentInt_disp (p k)

/-- **Independence**: the displacement's coordinates are independent under the
fixed-`p` law — immediate, since `roundLaw` is a product measure. Stated with an
arbitrary coefficient vector `A`, the form the tail bounds consume. -/
theorem iIndepFun_latDisp (p : Fin n → ℝ) (A : Fin n → ℝ) :
    iIndepFun (fun (k : Fin n) (z : Fin n → ℤ) => A k * (p k - (z k : ℝ))) (roundLaw p) :=
  iIndepFun_pi (μ := fun i => tentInt (p i)) (X := fun i (m : ℤ) => A i * (p i - (m : ℝ)))
    (fun i => (integrable_tentInt (p i) _).aemeasurable)

end Arlib.Lattice.Rounding
