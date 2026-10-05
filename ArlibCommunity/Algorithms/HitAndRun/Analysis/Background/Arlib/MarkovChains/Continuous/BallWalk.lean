/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.Conductance
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Probability.UniformOn
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The ball walk on a convex body, as a Markov kernel

Cousins-Vempala, *Gaussian cooling and `O*(n^3)` algorithms for volume and Gaussian
volume*, section 4.1 (`../gaussian-cooling-vempala/vol3_journal.tex:514-746`), define the
**ball walk with `δ`-steps** on a convex body `K ⊆ ℝⁿ`: from the current point `x`, pick
`y` uniformly at random from the ball `x + δBₙ`, move to `y` if `y ∈ K`, and otherwise
stay at `x`.  This module builds that walk as a genuine `ProbabilityTheory.Kernel` on
`EuclideanSpace ℝ (Fin n)`, and proves the two structural facts a conductance argument
needs before it can start: the kernel is Markov, and the uniform measure on `K` is
reversible — hence invariant — for it.

The Metropolis filter of the paper's Figure 2 is *not* applied here: this is the
unweighted (uniform-target) ball walk, which is the `P^unif` of `lem:overlap`
(`vol3_journal.tex:582`).

## Main definitions

* `Arlib.MarkovChains.ell K δ x = vol(x + δBₙ ∩ K) / vol(δBₙ)` — the **local
  conductance** at `x` (`vol3_journal.tex:293`), the probability that the proposed point
  is accepted.
* `Arlib.MarkovChains.ballWalk K δ` — **the ball walk kernel**.  On a measurable `K` it
  is `(vol(x + δBₙ))⁻¹ • volume.restrict (x + δBₙ ∩ K) + (1 - ℓ(x)) • dirac x`: the
  uniform proposal restricted to `K`, plus an atom at `x` carrying exactly the rejected
  mass.  On a non-measurable `K` — where the proposal is not a kernel at all — it is the
  identity kernel, so that `ballWalk` is a total function of `K` and `δ`; every lemma
  below that says anything about its value carries `MeasurableSet K`.
* `Arlib.MarkovChains.SpeedyPoints K δ = {x | 3/4 ≤ ℓ(x)}` — the points from which the
  walk moves with probability at least `3/4`; the speedy-walk analysis
  (`vol3_journal.tex:829`) discards the rest.
* `Arlib.MarkovChains.avgLocalConductance K δ` and `Arlib.MarkovChains.IsSmooth K δ s` —
  the **average local conductance** `λ = (∫_K ℓ)/vol(K)` of `vol3_journal.tex:848`, and
  the statement that `K` is `(δ, s)`-smooth, i.e. `λ ≥ 1 - s`.

## Main results

* `Arlib.MarkovChains.isMarkovKernel_ballWalk` — **the ball walk is a Markov kernel**,
  for every `K` and every `δ`, including the degenerate `δ ≤ 0` (where the proposal ball
  is empty and the walk is the identity).
* `Arlib.MarkovChains.ballWalk_apply_compl_singleton` — **the walk moves with probability
  exactly `ℓ(x)`**: `P_x({x}ᶜ) = ℓ(x)`.  This needs `[NeZero n]`; see the warning below.
* `Arlib.MarkovChains.lintegral_volume_inter_ball_comm` — the crux:
  `∫_A vol(B ∩ ball x δ) dx = ∫_B vol(A ∩ ball x δ) dx`, because `y ∈ ball x δ` iff
  `x ∈ ball y δ`.  Proved by evaluating both sides as the Lebesgue measure of one
  symmetric subset of `ℝⁿ × ℝⁿ` and applying `Measure.prod_swap`.
* `Arlib.MarkovChains.isReversible_ballWalk`, `Arlib.MarkovChains.invariant_ballWalk` —
  **detailed balance for the uniform measure on `K`**, and therefore (via the landed
  `Arlib.MarkovChains.IsReversible.invariant`) its invariance.  No convexity, no
  isoperimetry, and no bound on `δ` is needed: reversibility is exactly the symmetry of
  the ball relation above.

## Degenerate cases: two warnings

**`n = 0`.**  `EuclideanSpace ℝ (Fin 0)` is a single point of `volume` one, so `{x}` is
*not* null and the walk "stays put" with probability one while `ℓ(x) = 1`.  The identity
`P_x({x}ᶜ) = ℓ(x)` is therefore **false** at `n = 0`, and
`ballWalk_apply_compl_singleton` carries `[NeZero n]`.  Nothing else in the file does:
the kernel, its Markov property, and reversibility are all correct at `n = 0`.

**`δ ≤ 0` and null `K`.**  `ℝ≥0∞` divides by zero to zero, so `ell K δ x = 0` when the
proposal ball is null, and the kernel degenerates to `dirac x` — still Markov, still
reversible, but with nothing to say.  Likewise `Arlib.uniformOn volume K` is the *zero*
measure unless `0 < volume K < ⊤`, in which case `isReversible_ballWalk` is a true
statement about the zero measure.  The witnesses in the last section discharge all of
these guards at once on the unit ball.

## Scope: what is deliberately absent

There is **no conductance bound and no mixing bound here, in any form** — not as a
theorem, not as an assumed predicate, not as a definition whose name asserts one.  The
Cousins-Vempala conductance bound `Φ = Ω(δ/(σ√n))` (`thm:speedyconductance`,
`vol3_journal.tex:624`) rests on the isoperimetric inequality for log-concave densities,
which Mathlib does not have and which `Arlib/Convexity/Isoperimetry.lean` deliberately
stops short of; see `CV-ROADMAP.md` section 3.  A predicate named after that bound would
be inhabited only by degenerate witnesses, which is the trap `CV-ROADMAP.md` section 2a
records.  What this file supplies is the object such a bound would be *about*.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

variable {n : ℕ}

/-! ## Measurability of the proposal -/

/-- **`x ↦ vol(B ∩ (x + δBₙ))` is measurable.**  This is the one genuinely
measure-theoretic ingredient in turning "pick a uniform point of the ball" into a
`Kernel`: the map is the `x`-section of the measurable subset
`{(x, y) | y ∈ B ∧ dist x y < δ}` of `ℝⁿ × ℝⁿ`, so `measurable_measure_prodMk_left`
applies. -/
theorem measurable_volume_inter_ball {B : Set (EuclideanSpace ℝ (Fin n))}
    (hB : MeasurableSet B) (δ : ℝ) :
    Measurable fun x : EuclideanSpace ℝ (Fin n) => volume (B ∩ Metric.ball x δ) := by
  have hd : Measurable fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      dist p.1 p.2 := continuous_dist.measurable
  have hS : MeasurableSet
      {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
        p.2 ∈ B ∧ dist p.1 p.2 < δ} :=
    (measurable_snd hB).inter (measurableSet_lt hd measurable_const)
  have hEq : ∀ x : EuclideanSpace ℝ (Fin n), B ∩ Metric.ball x δ =
      Prod.mk x ⁻¹' {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
        p.2 ∈ B ∧ dist p.1 p.2 < δ} := by
    intro x; ext y; simp [Metric.mem_ball, dist_comm]
  simp_rw [hEq]
  exact measurable_measure_prodMk_left hS

/-! ## The local conductance -/

/-- The **local conductance** at `x`,
`ℓ(x) = vol(K ∩ (x + δBₙ)) / vol(x + δBₙ)` (`vol3_journal.tex:293`): the fraction of the
proposal ball that lies inside `K`, equivalently the probability that a single step of
the ball walk from `x` actually moves (`ballWalk_apply_compl_singleton`).

The denominator is the volume of the ball *centred at `x`*, which by translation
invariance (`volume_ball_eq`) is the `vol(δBₙ)` of the paper.  Because `ℝ≥0∞` divides by
zero to zero, `ell K δ x = 0` whenever `δ ≤ 0`; that is the same convention under which
the kernel degenerates to `dirac x`, so the two agree. -/
noncomputable def ell (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  volume (Metric.ball x δ ∩ K) / volume (Metric.ball x δ)

/-- Unfolding lemma for `ell`. -/
theorem ell_apply (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ell K δ x = volume (Metric.ball x δ ∩ K) / volume (Metric.ball x δ) := rfl

/-- **The volume of a ball does not depend on its centre**, Lebesgue measure being
translation invariant.  This is what lets the denominator of `ell` be treated as a
constant, which is what makes `ell` measurable. -/
theorem volume_ball_eq (x : EuclideanSpace ℝ (Fin n)) (δ : ℝ) :
    volume (Metric.ball x δ) = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ) :=
  Measure.addHaar_ball_center volume x δ

/-- **The local conductance is a probability**: `ℓ(x) ≤ 1`, since `K ∩ (x + δBₙ)` is a
subset of `x + δBₙ`.  (`0 ≤ ℓ(x)` is automatic in `ℝ≥0∞`.)  This is what makes the
stay-put mass `1 - ℓ(x)` in the definition of the kernel an exact complement rather than
a truncated subtraction that loses information. -/
theorem ell_le_one (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ell K δ x ≤ 1 :=
  ENNReal.div_le_of_le_mul (by simpa using measure_mono Set.inter_subset_left)

/-- **The local conductance is a measurable function of the current point.**  The
numerator is `measurable_volume_inter_ball` and the denominator is a constant
(`volume_ball_eq`). -/
theorem measurable_ell {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (δ : ℝ) :
    Measurable (ell K δ) := by
  have h : ell K δ = fun x => volume (K ∩ Metric.ball x δ) /
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ) := by
    funext x
    rw [ell_apply, Set.inter_comm, volume_ball_eq]
  rw [h]
  exact (measurable_volume_inter_ball hK δ).div_const _

/-! ## The crux: symmetry of the ball relation -/

/-- The **`δ`-neighbourhood relation between `A` and `B`**,
`{(x, y) | x ∈ A, y ∈ B, dist x y < δ}` as a subset of `ℝⁿ × ℝⁿ`.  It exists only to
carry the symmetry of `dist` into a measure-theoretic statement: its two marginal
integrals are the two sides of `lintegral_volume_inter_ball_comm`, and swapping the
coordinates exchanges `A` and `B`. -/
def nearRel (A B : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ) :
    Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
  {p | p.1 ∈ A ∧ p.2 ∈ B ∧ dist p.1 p.2 < δ}

/-- `nearRel A B δ` is measurable when `A` and `B` are: it is an intersection of two
preimages of measurable sets with the sublevel set of the (continuous) distance. -/
theorem measurableSet_nearRel {A B : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (δ : ℝ) : MeasurableSet (nearRel A B δ) :=
  (measurable_fst hA).inter ((measurable_snd hB).inter
    (measurableSet_lt continuous_dist.measurable measurable_const))

/-- **Swapping the coordinates exchanges the two sets.**  This is `dist_comm`, and it is
the entire mathematical content of reversibility of the ball walk. -/
theorem preimage_swap_nearRel (A B : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ) :
    Prod.swap ⁻¹' nearRel A B δ = nearRel B A δ := by
  ext p
  simp only [Set.mem_preimage, nearRel, Set.mem_setOf_eq, Prod.fst_swap, Prod.snd_swap]
  rw [dist_comm]
  tauto

/-- **The `x`-sections of `nearRel` compute the integral.**  `(vol × vol)(nearRel A B δ)`
equals `∫_A vol(B ∩ ball x δ) dx`, because the section over `x ∈ A` is `B ∩ ball x δ` and
the section over `x ∉ A` is empty. -/
theorem prod_nearRel {A B : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (δ : ℝ) :
    (volume.prod volume) (nearRel A B δ) = ∫⁻ x in A, volume (B ∩ Metric.ball x δ) := by
  rw [Measure.prod_apply (measurableSet_nearRel hA hB δ), ← lintegral_indicator hA]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ A
  · have : Prod.mk x ⁻¹' nearRel A B δ = B ∩ Metric.ball x δ := by
      ext y
      simp only [Set.mem_preimage, nearRel, Set.mem_setOf_eq, Set.mem_inter_iff,
        Metric.mem_ball']
      tauto
    rw [this, Set.indicator_of_mem hx]
  · have : Prod.mk x ⁻¹' nearRel A B δ = ∅ := by
      ext y
      simp only [Set.mem_preimage, nearRel, Set.mem_setOf_eq, Set.mem_empty_iff_false,
        iff_false, not_and]
      exact fun h => absurd h hx
    rw [this, Set.indicator_of_notMem hx, measure_empty]

/-- **The crux: the ball relation is symmetric.**

    ∫_A vol(B ∩ (x + δBₙ)) dx = ∫_B vol(A ∩ (x + δBₙ)) dx.

Both sides are the Lebesgue measure of `nearRel` on `ℝⁿ × ℝⁿ` (`prod_nearRel`), and
`Measure.prod_swap` together with `preimage_swap_nearRel` identifies the two relations.
This single identity is what makes the ball walk reversible: it says that the transition
density `1[dist x y < δ]/vol(δBₙ)` is symmetric in `x` and `y`. -/
theorem lintegral_volume_inter_ball_comm {A B : Set (EuclideanSpace ℝ (Fin n))}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (δ : ℝ) :
    ∫⁻ x in A, volume (B ∩ Metric.ball x δ) = ∫⁻ x in B, volume (A ∩ Metric.ball x δ) := by
  rw [← prod_nearRel hA hB δ, ← prod_nearRel hB hA δ, ← preimage_swap_nearRel A B δ,
    ← Measure.map_apply measurable_swap (measurableSet_nearRel hA hB δ), Measure.prod_swap]

/-! ## The kernel -/

/-- **The ball walk kernel on a measurable `K`.**  From `x`, the measure

    (vol(x + δBₙ))⁻¹ • volume.restrict (x + δBₙ ∩ K)  +  (1 - ℓ(x)) • dirac x

puts uniform mass on the part of the proposal ball that lies in `K` — total mass `ℓ(x)` —
and returns the rejected mass `1 - ℓ(x)` to the current point.  `ballWalk` is the version
that does not carry the measurability proof; use that one. -/
noncomputable def ballWalkAux (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (δ : ℝ) : Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) where
  toFun x := (volume (Metric.ball x δ))⁻¹ • volume.restrict (Metric.ball x δ ∩ K)
      + (1 - ell K δ x) • Measure.dirac x
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun t ht => ?_
    have hrw : ∀ x : EuclideanSpace ℝ (Fin n),
        ((volume (Metric.ball x δ))⁻¹ • volume.restrict (Metric.ball x δ ∩ K)
            + (1 - ell K δ x) • Measure.dirac x) t
          = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ))⁻¹ *
              volume ((t ∩ K) ∩ Metric.ball x δ)
            + (1 - ell K δ x) * t.indicator 1 x := by
      intro x
      have hset : t ∩ (Metric.ball x δ ∩ K) = (t ∩ K) ∩ Metric.ball x δ := by
        ext y
        simp only [Set.mem_inter_iff]
        tauto
      rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
        Measure.restrict_apply ht, Measure.dirac_apply' _ ht, hset, volume_ball_eq]
    simp_rw [hrw]
    exact ((measurable_volume_inter_ball (ht.inter hK) δ).const_mul _).add
      ((measurable_const.sub (measurable_ell hK δ)).mul (measurable_one.indicator ht))

/-- Unfolding lemma for `ballWalkAux`: the kernel's value at `x` is the measure in its
docstring. -/
theorem ballWalkAux_apply (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K) (δ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ballWalkAux K hK δ x = (volume (Metric.ball x δ))⁻¹ • volume.restrict (Metric.ball x δ ∩ K)
      + (1 - ell K δ x) • Measure.dirac x := rfl

open scoped Classical in
/-- **The ball walk with `δ`-steps on `K`** (`vol3_journal.tex:249`): from `x`, pick `y`
uniformly in `x + δBₙ`; go to `y` if `y ∈ K`, else stay at `x`.

Defined as `ballWalkAux` when `K` is measurable — which is the only case in which the
proposal is a kernel at all — and as the identity kernel otherwise, so that `ballWalk` is
a function of the data `K` and `δ` alone.  It is a Markov kernel unconditionally
(`isMarkovKernel_ballWalk`); every statement about its *value* assumes
`MeasurableSet K`. -/
noncomputable def ballWalk (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ) :
    Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
  if hK : MeasurableSet K then ballWalkAux K hK δ else Kernel.deterministic id measurable_id

open scoped Classical in
/-- On a measurable `K`, `ballWalk` is `ballWalkAux`. -/
theorem ballWalk_eq {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (δ : ℝ) :
    ballWalk K δ = ballWalkAux K hK δ := dif_pos hK

/-- **The value of `ballWalkAux` on a measurable event.**  The mass
`ballWalkAux K hK δ x t` splits into the proposal part
`vol(t ∩ (x + δBₙ) ∩ K)/vol(x + δBₙ)` and the stay-put part `(1 - ℓ(x))·1[x ∈ t]`. -/
theorem ballWalkAux_apply_set {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (δ : ℝ) (x : EuclideanSpace ℝ (Fin n)) {t : Set (EuclideanSpace ℝ (Fin n))}
    (ht : MeasurableSet t) :
    ballWalkAux K hK δ x t
      = (volume (Metric.ball x δ))⁻¹ * volume (t ∩ (Metric.ball x δ ∩ K))
        + (1 - ell K δ x) * t.indicator 1 x := by
  rw [ballWalkAux_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
    smul_eq_mul, Measure.restrict_apply ht, Measure.dirac_apply' _ ht]

/-- The proposal's total mass is the local conductance:
`vol(x + δBₙ)⁻¹ · vol((x + δBₙ) ∩ K) = ℓ(x)`.  Unconditional — both sides are `0` when
the ball is null. -/
theorem inv_mul_volume_eq_ell (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (volume (Metric.ball x δ))⁻¹ * volume (Metric.ball x δ ∩ K) = ell K δ x := by
  rw [ell_apply, ENNReal.div_eq_inv_mul]

/-- **`ballWalkAux` is a Markov kernel.**  Its total mass is `ℓ(x) + (1 - ℓ(x))`, which
is `1` because `ell_le_one` makes the truncated subtraction exact. -/
instance isMarkovKernel_ballWalkAux (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : MeasurableSet K) (δ : ℝ) : IsMarkovKernel (ballWalkAux K hK δ) := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [ballWalkAux_apply_set hK δ x MeasurableSet.univ, Set.univ_inter,
    Set.indicator_of_mem (Set.mem_univ x), Pi.one_apply, mul_one, inv_mul_volume_eq_ell]
  exact add_tsub_cancel_of_le (ell_le_one K δ x)

open scoped Classical in
/-- **The ball walk is a Markov kernel**, for every set `K` (measurable or not) and every
step `δ` (positive or not).  On the measurable branch this is
`isMarkovKernel_ballWalkAux`; on the other branch the kernel is `dirac`. -/
instance isMarkovKernel_ballWalk (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ) :
    IsMarkovKernel (ballWalk K δ) := by
  unfold ballWalk
  split_ifs with hK
  · exact isMarkovKernel_ballWalkAux K hK δ
  · infer_instance

/-- **The value of the ball walk on a measurable event**, for measurable `K`. -/
theorem ballWalk_apply_set {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (δ : ℝ) (x : EuclideanSpace ℝ (Fin n)) {t : Set (EuclideanSpace ℝ (Fin n))}
    (ht : MeasurableSet t) :
    ballWalk K δ x t
      = (volume (Metric.ball x δ))⁻¹ * volume (t ∩ (Metric.ball x δ ∩ K))
        + (1 - ell K δ x) * t.indicator 1 x := by
  rw [ballWalk_eq hK, ballWalkAux_apply_set hK δ x ht]

/-- **The walk moves with probability exactly the local conductance:**
`P_x({x}ᶜ) = ℓ(x)`.

The stay-put atom contributes nothing to `{x}ᶜ`, and the proposal part loses nothing by
deleting `{x}`, since singletons are Lebesgue-null.  That last step is where `[NeZero n]`
is used, and it is not removable: in `EuclideanSpace ℝ (Fin 0)` the whole space is one
atom of volume one, `{x}ᶜ = ∅`, and the identity fails. -/
theorem ballWalk_apply_compl_singleton [NeZero n] {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ballWalk K δ x {x}ᶜ = ell K δ x := by
  rw [ballWalk_apply_set hK δ x (measurableSet_singleton x).compl,
    Set.indicator_of_notMem (by simp) , mul_zero, add_zero]
  have hset : ({x}ᶜ : Set (EuclideanSpace ℝ (Fin n))) ∩ (Metric.ball x δ ∩ K)
      = (Metric.ball x δ ∩ K) \ {x} := by
    rw [Set.sdiff_eq, Set.inter_comm]
  rw [hset, measure_sdiff_null (measure_singleton x), inv_mul_volume_eq_ell]

/-! ## Reversibility -/

/-- **Detailed balance is invariant under rescaling the measure.**  Every flow scales by
the same constant (`flow_smul_measure`), so the symmetry survives.  This is what lets
reversibility be proved for the unnormalised `volume.restrict K` and then transported to
the probability measure `Arlib.uniformOn volume K`. -/
theorem IsReversible.smul {Om : Type*} [MeasurableSpace Om] {P : Kernel Om Om}
    {pi : Measure Om} (h : IsReversible P pi) (c : ℝ≥0∞) : IsReversible P (c • pi) := by
  intro S T hS hT
  rw [flow_smul_measure, flow_smul_measure, h S T hS hT]

/-- **The flow of the ball walk, split into its two parts.**  For `pi = volume.restrict K`,

    flow(S, T) = vol(δBₙ)⁻¹ · ∫_{S ∩ K} vol((T ∩ K) ∩ (x + δBₙ)) dx
                 + ∫_{T ∩ S ∩ K} (1 - ℓ(x)) dx.

The first term is the mass that actually moves from `S` into `T`; the second is the mass
that stays put, and it is only present where `S` and `T` overlap.  Written this way both
terms are visibly symmetric under exchanging `S` and `T` — the first by
`lintegral_volume_inter_ball_comm`, the second because the domain of integration is
symmetric — which is `isReversible_ballWalk_restrict`. -/
theorem flow_ballWalk {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (δ : ℝ)
    {S T : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    flow (ballWalk K δ) (volume.restrict K) S T
      = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ))⁻¹ *
            (∫⁻ x in S ∩ K, volume ((T ∩ K) ∩ Metric.ball x δ))
        + ∫⁻ x in T ∩ (S ∩ K), (1 - ell K δ x) := by
  have hpt : ∀ x : EuclideanSpace ℝ (Fin n), ballWalk K δ x T
      = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ))⁻¹ *
          volume ((T ∩ K) ∩ Metric.ball x δ)
        + T.indicator (fun y => 1 - ell K δ y) x := by
    intro x
    have hset : T ∩ (Metric.ball x δ ∩ K) = (T ∩ K) ∩ Metric.ball x δ := by
      ext y
      simp only [Set.mem_inter_iff]
      tauto
    rw [ballWalk_apply_set hK δ x hT, hset, volume_ball_eq]
    by_cases hx : x ∈ T
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, mul_one]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
  rw [flow, Measure.restrict_restrict hS]
  simp_rw [hpt]
  rw [lintegral_add_left ((measurable_volume_inter_ball (hT.inter hK) δ).const_mul _),
    lintegral_const_mul _ (measurable_volume_inter_ball (hT.inter hK) δ),
    lintegral_indicator hT, Measure.restrict_restrict hT]

/-- **The ball walk satisfies detailed balance for Lebesgue measure restricted to `K`.**
The proof is the symmetry of the two terms of `flow_ballWalk`.  No convexity of `K`, no
positivity of `δ`, and no bound relating `δ` to `K` is required. -/
theorem isReversible_ballWalk_restrict {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ : ℝ) : IsReversible (ballWalk K δ) (volume.restrict K) := by
  intro S T hS hT
  have h1 : (∫⁻ x in S ∩ K, volume ((T ∩ K) ∩ Metric.ball x δ))
      = ∫⁻ x in T ∩ K, volume ((S ∩ K) ∩ Metric.ball x δ) :=
    lintegral_volume_inter_ball_comm (hS.inter hK) (hT.inter hK) δ
  have h2 : T ∩ (S ∩ K) = S ∩ (T ∩ K) := by
    ext y
    simp only [Set.mem_inter_iff]
    tauto
  rw [flow_ballWalk hK δ hS hT, flow_ballWalk hK δ hT hS, h1, h2]

/-- **The ball walk is reversible for the uniform measure on `K`.**  Immediate from
`isReversible_ballWalk_restrict` and `IsReversible.smul`, since
`Arlib.uniformOn volume K = (volume K)⁻¹ • volume.restrict K`.

Note the statement is *true but empty* when `volume K` is `0` or `⊤`, where `uniformOn`
is the zero measure; `isProbabilityMeasure_uniformOn_unitBall` discharges that guard on
the witness. -/
theorem isReversible_ballWalk {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (δ : ℝ) : IsReversible (ballWalk K δ) (Arlib.uniformOn volume K) :=
  (isReversible_ballWalk_restrict hK δ).smul _

/-- **The uniform measure on `K` is invariant for the ball walk.**  Detailed balance
(`isReversible_ballWalk`) plus the landed `IsReversible.invariant`.  This is the
stationarity claim that every mixing statement about the ball walk presupposes. -/
theorem invariant_ballWalk {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (δ : ℝ) : Kernel.Invariant (ballWalk K δ) (Arlib.uniformOn volume K) :=
  (isReversible_ballWalk hK δ).invariant

/-! ## The speedy walk and smooth bodies

Two plain definitions.  Neither carries an assumed conclusion: nothing below asserts a
conductance, a mixing time, or any bound on the quantities it names. -/

/-- The **points of high local conductance**, `{x | ℓ(x) ≥ 3/4}`.

The speedy walk of `vol3_journal.tex:829` is the subsequence of *proper* steps of the
ball walk — those on which the proposed point lands in `K` — and its analysis is driven
by the points where that happens often.  `3/4` is the threshold at which
`vol3_journal.tex:551` (`lem:f-dist`) controls the ratio `ℓ(u)/ℓ(v)` for nearby `u, v`.

This is a plain definition: **nothing about the speedy walk's conductance or mixing is
asserted anywhere in this file.** -/
def SpeedyPoints (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) := {x | 3 / 4 ≤ ell K δ x}

/-- Membership in `SpeedyPoints`, unfolded. -/
theorem mem_speedyPoints_iff {K : Set (EuclideanSpace ℝ (Fin n))} {δ : ℝ}
    {x : EuclideanSpace ℝ (Fin n)} : x ∈ SpeedyPoints K δ ↔ 3 / 4 ≤ ell K δ x := Iff.rfl

/-- `SpeedyPoints K δ` is measurable when `K` is: it is a superlevel set of the
measurable function `ell K δ`. -/
theorem measurableSet_speedyPoints {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ : ℝ) : MeasurableSet (SpeedyPoints K δ) :=
  measurableSet_le measurable_const (measurable_ell hK δ)

/-- The **average local conductance** `λ = (∫_K ℓ(x) dx) / vol(K)`
(`vol3_journal.tex:848`) — for the uniform density, the expected fraction of steps of the
ball walk that are proper.  It governs the number of *wasted* steps, which is the only
role it plays in Cousins-Vempala; no bound on it is proved or assumed here. -/
noncomputable def avgLocalConductance (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ) : ℝ≥0∞ :=
  (∫⁻ x in K, ell K δ x) / volume K

/-- **`K` is `(δ, s)`-smooth**: the average local conductance for `δ`-steps is at least
`1 - s`, written multiplicatively as `(1 - s)·vol(K) ≤ ∫_K ℓ`.

The multiplicative form is the robust one — it says the right thing at `vol(K) ∈ {0, ⊤}`,
where the quotient of `avgLocalConductance` would be junk; `isSmooth_iff_le_avg` proves
the two agree on `0 < vol(K) < ⊤`.

This is a plain definition.  It asserts nothing: `IsSmooth K δ s` is a hypothesis a
caller supplies, never a conclusion this file provides for a general `K`.
`isSmooth_unitBall` proves one concrete non-trivial instance of it. -/
def IsSmooth (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ) (s : ℝ≥0∞) : Prop :=
  (1 - s) * volume K ≤ ∫⁻ x in K, ell K δ x

/-- **`(δ, s)`-smoothness really is a statement about the average**, once `K` has
positive finite volume.  Both guards are load-bearing: `ENNReal` division would otherwise
turn the right-hand side into `⊤` or `0`. -/
theorem isSmooth_iff_le_avg {K : Set (EuclideanSpace ℝ (Fin n))} (h0 : volume K ≠ 0)
    (htop : volume K ≠ ⊤) (δ : ℝ) (s : ℝ≥0∞) :
    IsSmooth K δ s ↔ 1 - s ≤ avgLocalConductance K δ := by
  rw [IsSmooth, avgLocalConductance, ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl htop)]

/-! ## Non-vacuity witness -/

/-- The first guard on the witness: the unit ball is not Lebesgue-null. -/
theorem volume_unitBall_ne_zero :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ 0 :=
  (Metric.measure_ball_pos volume 0 one_pos).ne'

/-- The second guard on the witness: the unit ball has finite volume. -/
theorem volume_unitBall_ne_top :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ⊤ :=
  measure_ball_lt_top.ne

/-- **The uniform measure on the unit ball is a genuine probability measure.**  This is
what stops `isReversible_ballWalk` and `invariant_ballWalk` from being statements about
the zero measure. -/
theorem isProbabilityMeasure_uniformOn_unitBall :
    IsProbabilityMeasure
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
  Arlib.isProbabilityMeasure_uniformOn volume volume_unitBall_ne_zero volume_unitBall_ne_top

/-- **Deep interior points of the unit ball have local conductance `1`**: if
`‖x‖ < 1 - δ` then the whole proposal ball `x + δBₙ` lies inside the body, so every step
from `x` is proper. -/
theorem ell_unitBall_eq_one_of_mem {δ : ℝ} (hδ : 0 < δ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 - δ)) :
    ell (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ x = 1 := by
  have hsub : Metric.ball x δ ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    intro y hy
    have h1 : dist y x < δ := Metric.mem_ball.1 hy
    have h2 : dist x 0 < 1 - δ := Metric.mem_ball.1 hx
    refine Metric.mem_ball.2 ?_
    calc dist y 0 ≤ dist y x + dist x 0 := dist_triangle _ _ _
      _ < δ + (1 - δ) := add_lt_add h1 h2
      _ = 1 := by ring
  rw [ell_apply, Set.inter_eq_self_of_subset_left hsub,
    ENNReal.div_self (Metric.measure_ball_pos volume x hδ).ne' measure_ball_lt_top.ne]

/-- **At the centre of the unit ball the local conductance is `1`** for every step
`0 < δ ≤ 1`: the proposal ball is contained in the body. -/
theorem ell_unitBall_zero {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ell (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ 0 = 1 := by
  rw [ell_apply, Set.inter_eq_self_of_subset_left (Metric.ball_subset_ball hδ1),
    ENNReal.div_self (Metric.measure_ball_pos volume 0 hδ).ne' measure_ball_lt_top.ne]

/-- **The local conductance is not identically zero.**  Without this, `ell` could be the
constant `0` (which it is, for instance, when `δ ≤ 0`) and every statement about it would
be vacuous. -/
theorem ell_unitBall_zero_pos {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 < ell (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ 0 := by
  rw [ell_unitBall_zero hδ hδ1]
  exact zero_lt_one

/-- **`SpeedyPoints` is non-empty**: the centre of the unit ball has local conductance
`1 ≥ 3/4`. -/
theorem zero_mem_speedyPoints_unitBall {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (0 : EuclideanSpace ℝ (Fin n))
      ∈ SpeedyPoints (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ := by
  rw [mem_speedyPoints_iff, ell_unitBall_zero hδ hδ1]
  rw [ENNReal.div_le_iff_le_mul (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  norm_num

/-- **The witness kernel really moves.**  From the centre of the unit ball with step
`0 < δ ≤ 1`, the ball walk leaves the current point with probability exactly `1`: the
stay-put atom of the kernel is not carrying all the mass. -/
theorem ballWalk_unitBall_apply_compl_singleton [NeZero n] {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ballWalk (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ 0
        ({(0 : EuclideanSpace ℝ (Fin n))}ᶜ) = 1 := by
  rw [ballWalk_apply_compl_singleton measurableSet_ball δ 0, ell_unitBall_zero hδ hδ1]

/-- **A lower bound for the total local conductance of the unit ball**: the inner ball
of radius `1 - δ`, on which the local conductance is identically `1`, already contributes
its own volume. -/
theorem volume_ball_le_lintegral_ell_unitBall {δ : ℝ} (hδ : 0 < δ) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 - δ))
      ≤ ∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1,
          ell (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ x := by
  have h1 : ∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 - δ),
      ell (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ x
      = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 - δ)) := by
    rw [setLIntegral_congr_fun (g := fun _ => (1 : ℝ≥0∞)) measurableSet_ball
      (fun x hx => ell_unitBall_eq_one_of_mem hδ hx), setLIntegral_one]
  rw [← h1]
  exact lintegral_mono' (Measure.restrict_mono
    (Metric.ball_subset_ball (by linarith)) le_rfl) le_rfl

/-- **The unit ball is `(δ, 1 - (1 - δ)ⁿ)`-smooth.**  Combining
`volume_ball_le_lintegral_ell_unitBall` with the scaling law `vol(rBₙ) = rⁿ vol(Bₙ)`
(`Measure.addHaar_ball`), the average local conductance of the unit ball for `δ`-steps is
at least `(1 - δ)ⁿ`.

This is a genuinely non-trivial instance of `IsSmooth` — the bound is informative for
`δ ≪ 1/n`, which is exactly the regime `vol3_journal.tex:904` works in — and it is what
stops `IsSmooth` from being a predicate whose only witnesses are degenerate. -/
theorem isSmooth_unitBall [NeZero n] {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    IsSmooth (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ
      (1 - ENNReal.ofReal ((1 - δ) ^ n)) := by
  have hle : ENNReal.ofReal ((1 - δ) ^ n) ≤ 1 := by
    refine ENNReal.ofReal_le_one.2 ?_
    exact pow_le_one₀ (by linarith) (by linarith)
  have hvol : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 - δ))
      = ENNReal.ofReal ((1 - δ) ^ n) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    rw [Measure.addHaar_ball volume 0 (by linarith : (0:ℝ) ≤ 1 - δ), finrank_euclideanSpace_fin]
  rw [IsSmooth, ENNReal.sub_sub_cancel ENNReal.one_ne_top hle, ← hvol]
  exact volume_ball_le_lintegral_ell_unitBall hδ

/-- **The non-vacuity witness (`CLAUDE.md` section 11), packaged.**  For every dimension
`n ≥ 1` and every step `0 < δ ≤ 1` there is a body `K` — the unit ball — such that

* `K` is measurable, so `ballWalk K δ` is the real kernel and not the fallback;
* `Arlib.uniformOn volume K` is a genuine probability measure, not the zero measure;
* `ballWalk K δ` is a Markov kernel, reversible for it, and leaves it invariant;
* the local conductance is strictly positive, and from the centre the walk moves with
  probability one.

Without this every result above could be a true statement about a degenerate object. -/
theorem exists_ballWalk_witness [NeZero n] {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ K : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet K ∧ IsProbabilityMeasure (Arlib.uniformOn volume K) ∧
        IsMarkovKernel (ballWalk K δ) ∧
        IsReversible (ballWalk K δ) (Arlib.uniformOn volume K) ∧
        Kernel.Invariant (ballWalk K δ) (Arlib.uniformOn volume K) ∧
        0 < ell K δ 0 ∧ ballWalk K δ 0 {(0 : EuclideanSpace ℝ (Fin n))}ᶜ = 1 :=
  ⟨Metric.ball 0 1, measurableSet_ball, isProbabilityMeasure_uniformOn_unitBall,
    isMarkovKernel_ballWalk _ _, isReversible_ballWalk measurableSet_ball δ,
    invariant_ballWalk measurableSet_ball δ, ell_unitBall_zero_pos hδ hδ1,
    ballWalk_unitBall_apply_compl_singleton hδ hδ1⟩

end Arlib.MarkovChains
