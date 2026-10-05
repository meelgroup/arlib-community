/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Lattice.Rounding.Tent
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The product kernel of independent coordinatewise randomized rounding

`Arlib.Lattice.Rounding.tent` is the displacement density of randomized rounding in a
single coordinate. Rounding each coordinate of `p ∈ ℝⁿ` independently therefore
has kernel

  `k p x = Pr[rnd p = x] = ∏ᵢ tent (pᵢ − xᵢ)`,

which this file calls `Arlib.Lattice.Rounding.prodTent x p`, read as a function of the
*continuous* variable `p` for a *fixed* lattice point `x`.

The headline is `Arlib.Lattice.Rounding.integral_prodTent`:

  `∫ p, prodTent x p = 1`  for every fixed `x`.

This is **double stochasticity**. It is emphatically not the trivial statement
`∑ₓ k p x = 1` (each `p` rounds somewhere); it says that, seen as a function of
`p` with the lattice point held fixed, the kernel is again a probability density.
That is exactly what yields the *upper* bound `Pr[rnd p = x] ≤ 1 / Vol(P')` in
Theorem 2 of Kannan–Vempala, *Sampling Lattice Points* (STOC '97), and it is the
reason the sampling argument works at all.

The proof is Fubini over the product measure — `volume` on `EuclideanSpace ℝ (Fin n)`
is `Measure.pi` transported along the `PiLp` identification — followed by
translation invariance and `Arlib.Lattice.Rounding.integral_tent` in each coordinate.

The supporting facts describe the support: the density vanishes off the paper's
side-2 cube `C(x,1) =` `Arlib.Lattice.Rounding.roundBox x`, which sits inside the closed
ball of radius `√n` about `x`; hence compact support, hence integrability.
-/

namespace Arlib.Lattice.Rounding

open MeasureTheory

variable {n : ℕ}

/-- Coordinate projection on `EuclideanSpace ℝ (Fin n)` is measurable. -/
theorem measurable_coord (i : Fin n) :
    Measurable (fun p : EuclideanSpace ℝ (Fin n) => p i) :=
  (measurable_pi_apply i).comp (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurable

/-- Coordinate projection on `EuclideanSpace ℝ (Fin n)` is continuous. -/
theorem continuous_coord (i : Fin n) :
    Continuous (fun p : EuclideanSpace ℝ (Fin n) => p i) :=
  (continuous_apply i).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).continuous

/-- **The kernel of independent coordinatewise randomized rounding.**
`prodTent x p` is the density at `p` of the event `rnd p = x`: the product over
coordinates of the one-dimensional tent densities of the displacements
`pᵢ − xᵢ`. The first argument is the (fixed) lattice point, the second the
continuous variable. -/
noncomputable def prodTent (x p : EuclideanSpace ℝ (Fin n)) : ℝ := ∏ i, tent (p i - x i)

/-- The kernel is nonnegative: a product of nonnegative tents. -/
theorem prodTent_nonneg (x p : EuclideanSpace ℝ (Fin n)) : 0 ≤ prodTent x p :=
  Finset.prod_nonneg fun _ _ => tent_nonneg _

/-- The kernel is continuous in the continuous variable `p`. -/
theorem continuous_prodTent (x : EuclideanSpace ℝ (Fin n)) : Continuous (prodTent x) :=
  continuous_finsetProd _ fun i _ =>
    continuous_tent.comp ((continuous_coord i).sub continuous_const)

/-- The kernel is measurable in the continuous variable `p`. -/
theorem measurable_prodTent (x : EuclideanSpace ℝ (Fin n)) : Measurable (prodTent x) :=
  (continuous_prodTent x).measurable

/-- The paper's cube `C(x,1)`: the side-2 box about `x`, where the displacement of
randomized rounding lives. -/
def roundBox (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {p | ∀ i, |p i - x i| ≤ 1}

/-- The box is a measurable set — a countable intersection of coordinate slabs. -/
theorem measurableSet_roundBox (x : EuclideanSpace ℝ (Fin n)) : MeasurableSet (roundBox x) := by
  have hrw : roundBox x = ⋂ i, {p : EuclideanSpace ℝ (Fin n) | |p i - x i| ≤ 1} := by
    ext p; simp [roundBox]
  rw [hrw]
  refine MeasurableSet.iInter fun i => measurableSet_le ?_ measurable_const
  have hd : Measurable (fun p : EuclideanSpace ℝ (Fin n) => p i - x i) :=
    (measurable_coord i).sub measurable_const
  exact continuous_abs.measurable.comp hd

/-- A point of the box is within `√n` of the centre: each of the `n` coordinate
displacements contributes at most `1` to the squared Euclidean norm. This is what
makes the box bounded, and hence the kernel compactly supported. -/
theorem norm_sub_le_of_mem_roundBox {x p : EuclideanSpace ℝ (Fin n)} (h : p ∈ roundBox x) :
    ‖p - x‖ ≤ Real.sqrt n := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖(p - x) i‖ ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hi : ‖(p - x) i‖ = |p i - x i| := by simp [Real.norm_eq_abs]
        rw [hi]
        nlinarith [abs_nonneg (p i - x i), h i]
    _ = (n : ℝ) := by simp

/-- The box sits inside the closed ball of radius `√n` about its centre. -/
theorem roundBox_subset_closedBall (x : EuclideanSpace ℝ (Fin n)) :
    roundBox x ⊆ Metric.closedBall x (Real.sqrt n) := by
  intro p hp
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact norm_sub_le_of_mem_roundBox hp

/-- The kernel vanishes off the box: some coordinate's displacement exceeds `1`,
and that factor of the product is `0`. -/
theorem prodTent_eq_zero_of_notMem {x p : EuclideanSpace ℝ (Fin n)} (h : p ∉ roundBox x) :
    prodTent x p = 0 := by
  simp only [roundBox, Set.mem_setOf_eq, not_forall, not_le] at h
  obtain ⟨i, hi⟩ := h
  exact Finset.prod_eq_zero (Finset.mem_univ i) (tent_eq_zero_of_one_le hi.le)

/-- The kernel has compact support — it vanishes outside the closed ball of radius
`√n` about `x`. -/
theorem hasCompactSupport_prodTent (x : EuclideanSpace ℝ (Fin n)) :
    HasCompactSupport (prodTent x) := by
  refine HasCompactSupport.intro (isCompact_closedBall x (Real.sqrt n)) ?_
  intro p hp
  exact prodTent_eq_zero_of_notMem fun hbox => hp (roundBox_subset_closedBall x hbox)

/-- The kernel is integrable in `p`: it is continuous with compact support. -/
theorem integrable_prodTent (x : EuclideanSpace ℝ (Fin n)) : Integrable (prodTent x) :=
  (continuous_prodTent x).integrable_of_hasCompactSupport (hasCompactSupport_prodTent x)

/-- Transporting the integral of a product density from `EuclideanSpace ℝ (Fin n)` to
the plain function space `Fin n → ℝ`, where `volume` is literally `Measure.pi`. -/
private theorem integral_prodTent_eq_pi (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    (∫ p : EuclideanSpace ℝ (Fin n), prodTent x p)
      = ∫ q : Fin n → ℝ, ∏ i, tent (q i - x i) :=
  (PiLp.volume_preserving_ofLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding
    (g := fun q : Fin n → ℝ => ∏ i, tent (q i - x i))

/-- Each one-dimensional factor is a probability density even after translating:
`∫ tent (u − c) du = 1`, by translation invariance of Lebesgue measure and
`Arlib.Lattice.Rounding.integral_tent`. -/
theorem integral_tent_sub (c : ℝ) : ∫ u : ℝ, tent (u - c) = 1 := by
  rw [(measurePreserving_sub_right (volume : Measure ℝ) c).integral_comp
    (MeasurableEquiv.subRight c).measurableEmbedding tent, integral_tent]

/-- **Double stochasticity of the rounding kernel.**

`∫ p, prodTent x p = 1` for every *fixed* lattice point `x`: the kernel, read as a
function of the continuous variable, is itself a probability density.

This is the nontrivial direction of stochasticity — the trivial one is that each
`p` rounds to *some* lattice point. It is what supplies the upper bound
`Pr[rnd p = x] ≤ 1 / Vol(P')` in Theorem 2 of Kannan–Vempala.

Proof: `volume` on `EuclideanSpace ℝ (Fin n)` is the product measure, so Fubini
factors the integral of the product into a product of one-variable integrals, and
each of those is `1` by `Arlib.Lattice.Rounding.integral_tent_sub`. -/
theorem integral_prodTent (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ∫ p : EuclideanSpace ℝ (Fin n), prodTent x p = 1 := by
  rw [integral_prodTent_eq_pi n x,
    integral_fintype_prod_volume_eq_prod (fun i u => tent (u - x i))]
  simp [integral_tent_sub]

/-- The kernel's density measure is a probability measure: `volume.withDensity` of
`prodTent x` assigns total mass `1`. The `Measure`-level restatement of
`Arlib.Lattice.Rounding.integral_prodTent`. -/
instance isProbabilityMeasure_withDensity_prodTent (x : EuclideanSpace ℝ (Fin n)) :
    IsProbabilityMeasure
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (fun p => ENNReal.ofReal (prodTent x p))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_prodTent x)
      (Filter.Eventually.of_forall (prodTent_nonneg x)),
    integral_prodTent n x, ENNReal.ofReal_one]

end Arlib.Lattice.Rounding
