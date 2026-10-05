/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.LogConcave
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.PrekopaLeindlerN
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.BallWalk
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.Convexity.OneDimSharp

/-!
# The local conductance `ell` is log-concave

`Arlib.MarkovChains.ell K δ x = vol(B(x,δ) ∩ K) / vol(δBₙ)` is the local conductance of the
ball walk (`Arlib/MarkovChains/Continuous/BallWalk.lean:131`).  This file proves that, for a
**convex** `K`, its real-valued form `x ↦ (ell K δ x).toReal` is **log-concave** on all of
`ℝⁿ` in the sense of `Arlib.IsLogConcave` — and hence so is `1_K · ell`, the density of the
speedy walk's stationary measure `Arlib.MarkovChains.ellMeasure`.

## The proof

Not by convolution.  `vol(B(x,δ) ∩ K)` *is* the convolution `(1_K ⋆ 1_{δB})(x)`, and
log-concavity is indeed preserved under convolution by Prékopa–Leindler — but the repository
has no convolution-preserves-log-concavity lemma and Mathlib has neither, so that route would
have to be built from scratch.  The direct route is one set inclusion plus the *multiplicative*
Brunn–Minkowski inequality:

* `Arlib.ball_inter_convex_combination_subset` — for convex `K` and weights `a, b > 0` with
  `a + b = 1`,
  `a·(B(x,δ) ∩ K) + b·(B(y,δ) ∩ K) ⊆ B(a·x + b·y, δ) ∩ K`.
  Membership in `K` is convexity; membership in the ball is the triangle inequality
  `‖a(u−x) + b(v−y)‖ ≤ a‖u−x‖ + b‖v−y‖ < aδ + bδ = δ`.
* `Arlib.brunn_minkowski_mul_euclidean` — `Arlib.brunn_minkowski_pi` transported from
  `Fin n → ℝ` to `EuclideanSpace ℝ (Fin n)` along `WithLp.toLp`, which is measure preserving
  (`PiLp.volume_preserving_toLp`).  The **multiplicative** form is used rather than the sharp
  `1/n`-concave `Arlib.brunn_minkowski_sharp_euclidean` precisely because it needs no
  nonemptiness hypothesis: when one of the two intersections is empty the left-hand side is
  `0 ^ lam · … = 0` and the inequality is free, whereas the sharp form is *false* there.

Monotonicity of `volume` on the inclusion then gives exactly the geometric-mean inequality
defining `Arlib.LogConcaveOn`.

## Main results

* `Arlib.brunn_minkowski_mul_euclidean` — multiplicative Brunn–Minkowski on
  `EuclideanSpace ℝ (Fin n)`.
* `Arlib.ball_inter_convex_combination_subset` — the crux inclusion.
* `Arlib.isLogConcave_volume_ball_inter` — `x ↦ vol(B(x,δ) ∩ K)` is log-concave.
* `Arlib.isLogConcave_ell_toReal` — **the headline**: `x ↦ (ell K δ x).toReal` is log-concave,
  for every `δ` (including the degenerate `δ ≤ 0`, where `ell ≡ 0`).
* `Arlib.isLogConcave_indicator_mul_ell_toReal` — `1_K · ell` is log-concave, i.e. the density
  of `Arlib.MarkovChains.ellMeasure K δ` relative to Lebesgue measure is log-concave.
* `Arlib.isLogConcave_ell_toReal_witness`, `Arlib.isLogConcave_indicator_mul_ell_toReal_witness`
  — non-vacuity: a bounded convex body of positive volume at which every hypothesis holds and
  the log-concave function is **not** identically zero.
* `Arlib.continuous_ell_toReal` — `ell` is continuous, via the annulus estimate
  `Arlib.volume_ball_inter_toReal_le`.  This is the *other* binder the isoperimetric capstone
  needs beyond log-concavity.
* `Arlib.ellGaussian_isoperimetry_openClosed_logTwo` — **`thm:iso` for the `ell`-weighted
  Gaussian-restricted density** `h(x) = ℓ(x)·e^{−‖x‖²/(2σ²)}`, for open `S₁, S₂` and closed
  `S₃`.
* `Arlib.ellGaussian_isoperimetry_openClosed_logTwo_witness`,
  `Arlib.ellGaussian_isoperimetry_openClosed_logTwo_strict_witness` — non-vacuity, the second
  with an explicit admissible slab partition at which the conclusion is an inequality between
  strictly positive quantities.

## Scope

The isoperimetric inequality here is an **instance** of an existing theorem, not a new one:
`Arlib.gaussianRestricted_isoperimetry_openClosed_logTwo`
(`Arlib/Convexity/OneDimSharp.lean:631`) already quantifies over an arbitrary nonnegative
log-concave `f`, and the results above merely discharge its `hf₀`, `hfc`, `hhc`, `hhB`, `hhi`
and `hmass` binders at `f := ell K δ`.  Nothing here is a conductance bound, a mixing bound or
a runtime statement, and none of it may be quoted as one.

**What it does not unlock.**  The `hiso` binder of
`Arlib.MarkovChains.conductance_speedyWalk_ge_of_convex`
(`Arlib/MarkovChains/Continuous/StarPolar.lean:626`) is an isoperimetric inequality for the
density `h` of the walk's stationary measure `pi`, and `hrev` forces `pi` to be a scalar
multiple of `Arlib.MarkovChains.ellMeasure K δ`
(`Arlib/MarkovChains/Continuous/SpeedyWalk.lean:379, 403` are the only reversibility results
for `speedyWalk`), whose density is `1_K · ell` — with **no Gaussian factor**.  Every
unconditional `n`-dimensional isoperimetric inequality in this repository is for a density of
the form `f · e^{−‖x‖²/(2σ²)}`, and `1_K · ell` is not of that form with `f` log-concave: the
compensating factor `e^{+‖x‖²/(2σ²)}` is log-*convex*.  A second, independent mismatch: that
binder quantifies over **measurable** `S₁, S₂, S₃`, whereas the general-`f` capstone is proved
only for `S₁, S₂` open and `S₃` closed — the measurable upgrade
(`Arlib.gaussianIndicator_isoperimetry_measurable_logTwo`) is specific to indicator densities,
and the general reduction
`Arlib.gaussianRestricted_isoperimetry_of_openClosed_enlargement`
(`Arlib/Convexity/IsoOpenClosed.lean:1114`) needs disjoint open enlargements that
`Arlib.exists_separated_no_disjoint_open_enlargement` shows need not exist.  Log-concavity of
`ell` is therefore necessary for the `ell`-weighted Gaussian route but not by itself sufficient
for the speedy walk's binder.

There is no `def`, `structure`, `class` or `axiom` in this file; every declaration is a
`theorem`.
-/

open MeasureTheory Metric
open scoped ENNReal Pointwise

namespace Arlib

open MarkovChains

variable {n : ℕ}

/-! ### The multiplicative Brunn–Minkowski inequality on `EuclideanSpace ℝ (Fin n)`

`Arlib.brunn_minkowski_pi` lives on `Fin n → ℝ`.  The measurable-space structure, the additive
group structure and the `ℝ`-action of `EuclideanSpace ℝ (Fin n)` are the same ones transported
along `WithLp.toLp`, and `PiLp.volume_preserving_toLp` transports Lebesgue measure; the
inequality mentions no norm, so it transports verbatim. -/

section BrunnMinkowskiEuclidean

/-- Lebesgue measure on `EuclideanSpace ℝ (Fin n)` is the pushforward of Lebesgue measure on
`Fin n → ℝ`, so volumes may be computed on `toLp`-preimages.  Holds for *all* sets, measurable
or not, because `MeasurableEquiv.toLp` is a measurable equivalence. -/
theorem volume_preimage_toLp_eq (S : Set (EuclideanSpace ℝ (Fin n))) :
    volume S = volume ((MeasurableEquiv.toLp 2 (Fin n → ℝ)) ⁻¹' S) := by
  conv_lhs => rw [← (PiLp.volume_preserving_toLp (Fin n)).map_eq]
  rw [show (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n))
        = (MeasurableEquiv.toLp 2 (Fin n → ℝ) : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) from rfl,
    MeasurableEquiv.map_apply]

/-- `toLp`-preimages commute with Minkowski sums. -/
theorem preimage_toLp_add_eq (X Y : Set (EuclideanSpace ℝ (Fin n))) :
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)) ⁻¹' (X + Y)
      = (MeasurableEquiv.toLp 2 (Fin n → ℝ)) ⁻¹' X
        + (MeasurableEquiv.toLp 2 (Fin n → ℝ)) ⁻¹' Y := by
  ext z
  simp only [Set.mem_preimage, Set.mem_add]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    exact ⟨WithLp.ofLp a, by simpa using ha, WithLp.ofLp b, by simpa using hb, by
      simpa using congrArg WithLp.ofLp hab⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    exact ⟨_, ha, _, hb, by simp [← hab]⟩

/-- `toLp`-preimages commute with dilations. -/
theorem preimage_toLp_smul_eq (c : ℝ) (X : Set (EuclideanSpace ℝ (Fin n))) :
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)) ⁻¹' (c • X)
      = c • ((MeasurableEquiv.toLp 2 (Fin n → ℝ)) ⁻¹' X) := by
  ext z
  simp only [Set.mem_preimage, Set.mem_smul_set]
  constructor
  · rintro ⟨a, ha, hab⟩
    exact ⟨WithLp.ofLp a, by simpa using ha, by simpa using congrArg WithLp.ofLp hab⟩
  · rintro ⟨a, ha, hab⟩
    exact ⟨_, ha, by simp [← hab]⟩

/-- **The multiplicative Brunn–Minkowski inequality on `EuclideanSpace ℝ (Fin n)`.**

`volume A ^ lam * volume B ^ (1 - lam) ≤ volume (lam • A + (1 - lam) • B)`, with `^` denoting
`ENNReal.rpow`.  No finiteness and no nonemptiness hypothesis: if either set is null the
left-hand side is `0`.  As in `Arlib.brunn_minkowski_pi`, the Minkowski sum need not be
measurable and `volume` is used as an outer measure on the right. -/
theorem brunn_minkowski_mul_euclidean {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1)
    {A B : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    volume A ^ lam * volume B ^ (1 - lam) ≤ volume (lam • A + (1 - lam) • B) := by
  have key := brunn_minkowski_pi (n := n) hlam0 hlam1
    ((MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable hA)
    ((MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable hB)
  rw [← volume_preimage_toLp_eq A, ← volume_preimage_toLp_eq B,
    ← preimage_toLp_smul_eq, ← preimage_toLp_smul_eq, ← preimage_toLp_add_eq,
    ← volume_preimage_toLp_eq] at key
  exact key

end BrunnMinkowskiEuclidean

/-! ### The crux: the convex-combination inclusion -/

/-- **The crux.**  For a convex `K` and weights `a, b > 0` with `a + b = 1`,

  `a·(B(x,δ) ∩ K) + b·(B(y,δ) ∩ K) ⊆ B(a·x + b·y, δ) ∩ K`.

Membership in `K` is convexity of `K`; membership in the ball is the triangle inequality plus
homogeneity of the norm:
`‖a(u−x) + b(v−y)‖ ≤ a‖u−x‖ + b‖v−y‖ < aδ + bδ = δ`,
where strictness uses `a, b > 0`.  This is the whole geometric content of the log-concavity of
`ell`; everything after it is Brunn–Minkowski and bookkeeping. -/
theorem ball_inter_convex_combination_subset {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (δ : ℝ) (x y : EuclideanSpace ℝ (Fin n)) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    a • (ball x δ ∩ K) + b • (ball y δ ∩ K) ⊆ ball (a • x + b • y) δ ∩ K := by
  rintro z hz
  rw [Set.mem_add] at hz
  obtain ⟨p, hp, q, hq, rfl⟩ := hz
  rw [Set.mem_smul_set] at hp hq
  obtain ⟨u, hu, rfl⟩ := hp
  obtain ⟨v, hv, rfl⟩ := hq
  refine ⟨?_, hKc hu.2 hv.2 ha.le hb.le hab⟩
  have hux : ‖u - x‖ < δ := by rw [← dist_eq_norm]; exact hu.1
  have hvy : ‖v - y‖ < δ := by rw [← dist_eq_norm]; exact hv.1
  rw [mem_ball, dist_eq_norm]
  have heq : a • u + b • v - (a • x + b • y) = a • (u - x) + b • (v - y) := by
    rw [smul_sub, smul_sub]; abel
  rw [heq]
  calc ‖a • (u - x) + b • (v - y)‖ ≤ ‖a • (u - x)‖ + ‖b • (v - y)‖ := norm_add_le _ _
    _ = a * ‖u - x‖ + b * ‖v - y‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos ha, abs_of_pos hb]
    _ < a * δ + b * δ := by
        exact add_lt_add (mul_lt_mul_of_pos_left hux ha) (mul_lt_mul_of_pos_left hvy hb)
    _ = δ := by rw [← add_mul, hab, one_mul]

/-! ### Log-concavity of the ball-intersection volume, and of `ell` -/

/-- **`x ↦ vol(B(x,δ) ∩ K)` is log-concave** for convex measurable `K`, at every step size `δ`
(including `δ ≤ 0`, where the function is identically `0`).

The two endpoint weights are handled separately because
`Arlib.brunn_minkowski_mul_euclidean` asks for `0 < lam < 1`; at an endpoint the inequality is
an equality. -/
theorem isLogConcave_volume_ball_inter {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K) (δ : ℝ) :
    IsLogConcave (fun x : EuclideanSpace ℝ (Fin n) => (volume (ball x δ ∩ K)).toReal) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only
  rcases ha.lt_or_eq with ha' | ha0
  swap
  · -- `a = 0`, hence `b = 1`
    rw [← ha0] at hab ⊢
    have hb1 : b = 1 := by linarith
    subst hb1
    simp
  rcases hb.lt_or_eq with hb' | hb0
  swap
  · -- `b = 0`, hence `a = 1`
    rw [← hb0] at hab ⊢
    have ha1 : a = 1 := by linarith
    subst ha1
    simp
  -- the main case `0 < a, b < 1`
  have hb1 : b = 1 - a := by linarith
  subst hb1
  have hlam1 : a < 1 := by linarith
  have hAm : MeasurableSet (ball x δ ∩ K) := measurableSet_ball.inter hK
  have hBm : MeasurableSet (ball y δ ∩ K) := measurableSet_ball.inter hK
  have hsub := ball_inter_convex_combination_subset (a := a) (b := 1 - a) hKc δ x y ha' hb'
    (by ring)
  have hle : volume (ball x δ ∩ K) ^ a * volume (ball y δ ∩ K) ^ (1 - a)
      ≤ volume (ball (a • x + (1 - a) • y) δ ∩ K) :=
    le_trans (brunn_minkowski_mul_euclidean ha' hlam1 hAm hBm) (measure_mono hsub)
  have htop : volume (ball (a • x + (1 - a) • y) δ ∩ K) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono Set.inter_subset_left)
  have hmono := ENNReal.toReal_mono htop hle
  rwa [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at hmono

/-- **The headline: the local conductance is log-concave.**

For a convex measurable `K` and any step size `δ`, `x ↦ (ell K δ x).toReal` is log-concave on
all of `ℝⁿ`.  `ell` is the ball-intersection volume divided by the *constant* `vol(δBₙ)`
(`Arlib.MarkovChains.volume_ball_eq`), and scaling by a nonnegative constant preserves
log-concavity.

No hypothesis on `δ` is needed: at `δ ≤ 0` both numerator and denominator vanish, `ell ≡ 0`,
and the constant `0` is log-concave. -/
theorem isLogConcave_ell_toReal {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K) (δ : ℝ) :
    IsLogConcave (fun x : EuclideanSpace ℝ (Fin n) => (ell K δ x).toReal) := by
  have hrw : (fun x : EuclideanSpace ℝ (Fin n) => (ell K δ x).toReal)
      = fun x : EuclideanSpace ℝ (Fin n) =>
          ((volume (ball (0 : EuclideanSpace ℝ (Fin n)) δ)).toReal)⁻¹
            * (volume (ball x δ ∩ K)).toReal := by
    funext x
    rw [ell_apply, ENNReal.toReal_div, volume_ball_eq]
    ring
  rw [hrw]
  exact IsLogConcave.const_mul (isLogConcave_volume_ball_inter hK hKc δ)
    (fun _ => ENNReal.toReal_nonneg) (inv_nonneg.2 ENNReal.toReal_nonneg)

/-- **The density of `Arlib.MarkovChains.ellMeasure K δ` is log-concave.**

`ellMeasure K δ = (volume.restrict K).withDensity (ell K δ)`
(`Arlib/MarkovChains/Continuous/SpeedyWalk.lean:277`), so its density relative to Lebesgue
measure is `1_K · ell`.  It is log-concave as a product of two log-concave functions: the
indicator of the convex set `K` (`Arlib.isLogConcave_indicator`) and `ell`
(`Arlib.isLogConcave_ell_toReal`). -/
theorem isLogConcave_indicator_mul_ell_toReal {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K) (δ : ℝ) :
    IsLogConcave (fun x : EuclideanSpace ℝ (Fin n) =>
      Set.indicator K (1 : EuclideanSpace ℝ (Fin n) → ℝ) x * (ell K δ x).toReal) :=
  IsLogConcave.mul (isLogConcave_indicator hKc) (isLogConcave_ell_toReal hK hKc δ)
    (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x)
    (fun _ => ENNReal.toReal_nonneg)

/-! ### Non-vacuity -/

/-- **Non-vacuity for `Arlib.isLogConcave_ell_toReal`.**

Every hypothesis is satisfiable at a *bounded* convex body of positive, finite volume — the
unit ball, at step size `δ = 1` — and there the log-concave function is **not** identically
zero: `ell K 1 0 = 1`, since `B(0,1) ⊆ B(0,1)`.  So the theorem is not vacuously about the
constant `0`. -/
theorem isLogConcave_ell_toReal_witness :
    ∃ (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ) (x : EuclideanSpace ℝ (Fin n)),
      MeasurableSet K ∧ Convex ℝ K ∧ Bornology.IsBounded K ∧ volume K ≠ 0 ∧ volume K ≠ ⊤ ∧
        0 < δ ∧ IsLogConcave (fun z : EuclideanSpace ℝ (Fin n) => (ell K δ z).toReal) ∧
        (ell K δ x).toReal = 1 := by
  refine ⟨ball (0 : EuclideanSpace ℝ (Fin n)) 1, 1, 0, measurableSet_ball, convex_ball _ _,
    isBounded_ball, (measure_ball_pos volume 0 one_pos).ne', measure_ball_lt_top.ne, one_pos,
    isLogConcave_ell_toReal measurableSet_ball (convex_ball _ _) 1, ?_⟩
  rw [ell_apply, Set.inter_self, ENNReal.div_self (measure_ball_pos volume 0 one_pos).ne'
    measure_ball_lt_top.ne]
  simp

/-- **Non-vacuity for `Arlib.isLogConcave_indicator_mul_ell_toReal`.**  Same witness: at the
centre of the unit ball the density `1_K · ell` equals `1`. -/
theorem isLogConcave_indicator_mul_ell_toReal_witness :
    ∃ (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ) (x : EuclideanSpace ℝ (Fin n)),
      MeasurableSet K ∧ Convex ℝ K ∧ Bornology.IsBounded K ∧ volume K ≠ 0 ∧ volume K ≠ ⊤ ∧
        0 < δ ∧
        IsLogConcave (fun z : EuclideanSpace ℝ (Fin n) =>
          Set.indicator K (1 : EuclideanSpace ℝ (Fin n) → ℝ) z * (ell K δ z).toReal) ∧
        Set.indicator K (1 : EuclideanSpace ℝ (Fin n) → ℝ) x * (ell K δ x).toReal = 1 := by
  refine ⟨ball (0 : EuclideanSpace ℝ (Fin n)) 1, 1, 0, measurableSet_ball, convex_ball _ _,
    isBounded_ball, (measure_ball_pos volume 0 one_pos).ne', measure_ball_lt_top.ne, one_pos,
    isLogConcave_indicator_mul_ell_toReal measurableSet_ball (convex_ball _ _) 1, ?_⟩
  have hmem : (0 : EuclideanSpace ℝ (Fin n)) ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    rw [mem_ball, dist_self]; norm_num
  rw [Set.indicator_of_mem hmem, ell_apply, Set.inter_self,
    ENNReal.div_self (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne]
  simp

/-! ### Continuity of `ell`

The isoperimetric capstone `Arlib.gaussianRestricted_isoperimetry_openClosed_logTwo` asks for a
**continuous** density, so log-concavity alone does not let one instantiate it.  `ell` is
continuous, by an elementary two-sided ball estimate: moving the centre by `e` moves the ball
inside a ball of radius `δ + e` about the new centre, so the intersection volume changes by at
most the volume of the annulus, `((δ+e)ⁿ − δⁿ)·vol(B₁)`, which tends to `0` with `e`.

No measurability of `K` is used: `volume` is monotone and subadditive as an outer measure. -/

section Continuity

/-- `EuclideanSpace ℝ (Fin n)` is nontrivial once `n ≠ 0`; this is what
`MeasureTheory.Measure.addHaar_ball` needs. -/
theorem nontrivial_euclideanSpace (hn : n ≠ 0) : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
  have h0 : (0 : ℕ) < n := Nat.pos_of_ne_zero hn
  refine ⟨EuclideanSpace.single (⟨0, h0⟩ : Fin n) (1 : ℝ), 0, fun hcon => ?_⟩
  have := congrArg (fun w : EuclideanSpace ℝ (Fin n) => w ⟨0, h0⟩) hcon
  simp at this

/-- The volume of a Euclidean ball of nonnegative radius, in real form. -/
theorem volume_ball_toReal (hn : n ≠ 0) (y : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 ≤ r) :
    (volume (ball y r)).toReal
      = r ^ n * (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
  haveI := nontrivial_euclideanSpace hn
  rw [Measure.addHaar_ball volume y hr, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]

/-- **The annulus estimate.**  Moving the centre of the proposal ball by `e = dist x y` changes
the intersection volume `vol(B(·,δ) ∩ K)` by at most the volume of the annulus between the
balls of radii `δ` and `δ + e`. -/
theorem volume_ball_inter_toReal_le {K : Set (EuclideanSpace ℝ (Fin n))} (hn : n ≠ 0)
    {δ : ℝ} (hδ : 0 ≤ δ) (x y : EuclideanSpace ℝ (Fin n)) :
    (volume (ball x δ ∩ K)).toReal
      ≤ (volume (ball y δ ∩ K)).toReal
        + ((δ + dist x y) ^ n - δ ^ n)
            * (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
  set e : ℝ := dist x y with hedef
  have he : 0 ≤ e := dist_nonneg
  have hδe : 0 ≤ δ + e := by linarith
  have hball_sub : ball y δ ⊆ ball y (δ + e) := ball_subset_ball (by linarith)
  have hsub1 : ball x δ ⊆ ball y (δ + e) := by
    intro z hz
    rw [mem_ball] at hz ⊢
    calc dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
      _ < δ + e := by rw [hedef]; exact add_lt_add_of_lt_of_le hz le_rfl
  have hsub2 : ball x δ ∩ K ⊆ (ball y δ ∩ K) ∪ (ball y (δ + e) \ ball y δ) := by
    rintro z ⟨hzb, hzK⟩
    by_cases hz : z ∈ ball y δ
    · exact Or.inl ⟨hz, hzK⟩
    · exact Or.inr ⟨hsub1 hzb, hz⟩
  -- the annulus has the expected volume
  have hdiff : volume (ball y (δ + e) \ ball y δ) + volume (ball y δ)
      = volume (ball y (δ + e)) := by
    have hd := measure_sdiff_add_inter (μ := volume) (ball y (δ + e))
      (measurableSet_ball (x := y) (ε := δ))
    rwa [Set.inter_eq_self_of_subset_right hball_sub] at hd
  have hfinδ : volume (ball y δ) ≠ ⊤ := measure_ball_lt_top.ne
  have hfinδe : volume (ball y (δ + e)) ≠ ⊤ := measure_ball_lt_top.ne
  have hfinann : volume (ball y (δ + e) \ ball y δ) ≠ ⊤ :=
    ne_top_of_le_ne_top hfinδe (measure_mono Set.sdiff_subset)
  have hann : (volume (ball y (δ + e) \ ball y δ)).toReal
      = ((δ + e) ^ n - δ ^ n) * (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
    have := congrArg ENNReal.toReal hdiff
    rw [ENNReal.toReal_add hfinann hfinδ, volume_ball_toReal hn y hδe,
      volume_ball_toReal hn y hδ] at this
    linarith
  -- and the intersection is covered by the smaller intersection plus the annulus
  have hle : volume (ball x δ ∩ K)
      ≤ volume (ball y δ ∩ K) + volume (ball y (δ + e) \ ball y δ) :=
    le_trans (measure_mono hsub2) (measure_union_le _ _)
  have hfinint : volume (ball y δ ∩ K) ≠ ⊤ :=
    ne_top_of_le_ne_top hfinδ (measure_mono Set.inter_subset_left)
  have hmono := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfinint, hfinann⟩) hle
  rwa [ENNReal.toReal_add hfinint hfinann, hann] at hmono

/-- **`x ↦ vol(B(x,δ) ∩ K)` is continuous.**  Immediate from the annulus estimate applied in
both directions, together with `((δ+e)ⁿ − δⁿ)·vol(B₁) → 0` as `e → 0`. -/
theorem continuous_volume_ball_inter_toReal {K : Set (EuclideanSpace ℝ (Fin n))} (hn : n ≠ 0)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    Continuous fun x : EuclideanSpace ℝ (Fin n) => (volume (ball x δ ∩ K)).toReal := by
  rw [Metric.continuous_iff]
  intro b τ hτ
  have hcont : ContinuousAt (fun t : ℝ =>
      ((δ + t) ^ n - δ ^ n) * (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal) 0 := by
    fun_prop
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨ρ, hρ, hgood⟩ := hcont τ hτ
  refine ⟨ρ, hρ, fun a hab => ?_⟩
  have h1 := volume_ball_inter_toReal_le (K := K) hn hδ a b
  have h2 := volume_ball_inter_toReal_le (K := K) hn hδ b a
  rw [dist_comm b a] at h2
  have hg := hgood (x := dist a b)
    (by rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg]; exact hab)
  rw [Real.dist_eq, show ((δ + (0 : ℝ)) ^ n - δ ^ n)
      * (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal = 0 by ring, sub_zero] at hg
  have hgle := le_abs_self (((δ + dist a b) ^ n - δ ^ n)
    * (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- **The local conductance is continuous**, for every `δ ≥ 0` in every dimension `n ≠ 0`. -/
theorem continuous_ell_toReal {K : Set (EuclideanSpace ℝ (Fin n))} (hn : n ≠ 0)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    Continuous fun x : EuclideanSpace ℝ (Fin n) => (ell K δ x).toReal := by
  have hrw : (fun x : EuclideanSpace ℝ (Fin n) => (ell K δ x).toReal)
      = fun x : EuclideanSpace ℝ (Fin n) =>
          ((volume (ball (0 : EuclideanSpace ℝ (Fin n)) δ)).toReal)⁻¹
            * (volume (ball x δ ∩ K)).toReal := by
    funext x
    rw [ell_apply, ENNReal.toReal_div, volume_ball_eq]
    ring
  rw [hrw]
  exact continuous_const.mul (continuous_volume_ball_inter_toReal hn hδ)

end Continuity

/-! ### `thm:iso` for the `ell`-weighted Gaussian-restricted density

`Arlib.gaussianRestricted_isoperimetry_openClosed_logTwo`
(`Arlib/Convexity/OneDimSharp.lean:631`) is stated for `h = f · e^{−‖x‖²/(2σ²)}` with `f` an
**arbitrary** nonnegative log-concave function — its binders are
`hf₀ : ∀ x, 0 ≤ f x` and `hfc : IsLogConcave f`, nothing about indicators.  So the results
above instantiate it at `f := ell K δ`, with no new isoperimetry work. -/

section Isoperimetry

/-- **`thm:iso` at the separation threshold `d / log 2`, for the `ell`-weighted Gaussian
density** `h(x) = ℓ(x)·e^{−‖x‖²/(2σ²)}` on a convex body `K`.

This is `Arlib.gaussianRestricted_isoperimetry_openClosed_logTwo` with its log-concave factor
`f` pinned to the local conductance: `hf₀` is `ENNReal.toReal_nonneg`, `hfc` is
`Arlib.isLogConcave_ell_toReal`, `hhc` is `Arlib.continuous_ell_toReal`, `hhB` is `ℓ ≤ 1`
(`Arlib.MarkovChains.ell_le_one`) times `e^{…} ≤ 1`, `hhi` is domination by the Gaussian, and
`hmass` comes from `hpos` — one point where the proposal ball meets `K` in positive volume
makes `h` strictly positive on a nonempty open set.

Every binder except `hpos` and `hh` is *verbatim* that of
`Arlib.gaussianRestricted_isoperimetry_openClosed_logTwo`, including the conclusion.

**Scope.**  This is an isoperimetric inequality and nothing more.  It is **not** the `hiso`
binder of `Arlib.MarkovChains.conductance_speedyWalk_ge_of_convex`, for two reasons recorded in
the module docstring: that binder is stated for **measurable** `S₁, S₂, S₃`, whereas this one
needs `S₁, S₂` open and `S₃` closed; and its density is `1_K · ℓ`, with **no** Gaussian factor,
whereas this one carries `e^{−‖x‖²/(2σ²)}`. -/
theorem ellGaussian_isoperimetry_openClosed_logTwo (hn : 2 ≤ n) {σ d δ : ℝ} (hσ : 0 < σ)
    (hδ : 0 < δ) {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    (hK : MeasurableSet K) {x₀ : EuclideanSpace ℝ (Fin n)}
    (hpos : volume (ball x₀ δ ∩ K) ≠ 0)
    {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hh : ∀ x, h x = (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))
    {S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))}
    (hpart : IsPartition3 Set.univ S₁ S₂ S₃)
    (hS₁ : IsOpen S₁) (hS₂ : IsOpen S₂) (hS₃ : IsClosed S₃)
    (hsep : ∀ u ∈ S₁, ∀ v ∈ S₂,
      d / Real.log 2 ≤ ‖u - v‖ ∨ 4 * (d / σ) * Real.sqrt n ≤ densDist h u v) :
    d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x) ≤ (∫ x, h x) * ∫ x in S₃, h x := by
  have hn0 : n ≠ 0 := by omega
  have hgc : Continuous fun x : EuclideanSpace ℝ (Fin n) =>
      Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) := by fun_prop
  have hellc : Continuous fun x : EuclideanSpace ℝ (Fin n) => (ell K δ x).toReal :=
    continuous_ell_toReal hn0 hδ.le
  have hhc : Continuous h := by
    have : h = fun x : EuclideanSpace ℝ (Fin n) =>
        (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) := funext hh
    rw [this]; exact hellc.mul hgc
  have hell1 : ∀ x : EuclideanSpace ℝ (Fin n), (ell K δ x).toReal ≤ 1 := by
    intro x
    have := ENNReal.toReal_mono ENNReal.one_ne_top (ell_le_one K δ x)
    simpa using this
  have hgle : ∀ x : EuclideanSpace ℝ (Fin n), Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) ≤ 1 := by
    intro x
    rw [Real.exp_le_one_iff, neg_div]
    exact neg_nonpos.2 (div_nonneg (sq_nonneg _) (by positivity))
  have hh0 : ∀ x, 0 ≤ h x := by
    intro x; rw [hh]
    exact mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le
  have hhB : ∀ x, h x ≤ 1 := by
    intro x; rw [hh]
    calc (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))
        ≤ 1 * 1 := by
          exact mul_le_mul (hell1 x) (hgle x) (Real.exp_pos _).le zero_le_one
      _ = 1 := one_mul 1
  have hgi : Integrable fun x : EuclideanSpace ℝ (Fin n) =>
      Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) := by
    have := integrable_gaussianWeightReal (n := n) hσ
    simpa [gaussianWeightReal] using this
  have hhi : Integrable h := by
    refine hgi.mono' hhc.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hh0 x), hh]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (hell1 x)
  -- positivity of the total mass, from one point where the proposal ball meets `K`
  have hellpos : 0 < (ell K δ x₀).toReal := by
    refine ENNReal.toReal_pos ?_ (ne_top_of_le_ne_top ENNReal.one_ne_top (ell_le_one K δ x₀))
    rw [ell_apply]
    exact fun hz => hpos (by
      rcases (ENNReal.div_eq_zero_iff).1 hz with hnum | hden
      · exact hnum
      · exact absurd hden measure_ball_lt_top.ne)
  have hx₀ : 0 < h x₀ := by
    rw [hh]; exact mul_pos hellpos (Real.exp_pos _)
  have hmass : 0 < ∫ x, h x := by
    rw [integral_pos_iff_support_of_nonneg hh0 hhi]
    have hopen : IsOpen {x : EuclideanSpace ℝ (Fin n) | 0 < h x} :=
      isOpen_lt continuous_const hhc
    refine lt_of_lt_of_le (hopen.measure_pos volume ⟨x₀, hx₀⟩) (measure_mono ?_)
    intro z hz
    exact ne_of_gt hz
  exact gaussianRestricted_isoperimetry_openClosed_logTwo (B := 1) hn hσ
    (fun _ => ENNReal.toReal_nonneg) (isLogConcave_ell_toReal hK hKc δ) hh hhc hhB hhi
    hpart hS₁ hS₂ hS₃ hmass hsep

/-- **Non-vacuity for `Arlib.ellGaussian_isoperimetry_openClosed_logTwo`.**

Every hypothesis is satisfiable simultaneously at a bounded convex body of positive finite
volume, with a *strictly positive* left-hand side, so the conclusion is not the trivial
`0 ≤ something`.  The instance is `K = B(0,1)`, `δ = 1`, `σ = 1`, `d = 1/8`, and the slab
partition orthogonal to the first coordinate axis

  `S₁ = {⟪e,x⟫ < −1/4}`, `S₂ = {1/4 < ⟪e,x⟫}`, `S₃ = {−1/4 ≤ ⟪e,x⟫ ≤ 1/4}`,

the same one used by `Arlib.gaussianRestricted_isoperimetry_openClosed_witness`.  The
separation hypothesis fires on the metric branch: `d/log 2 ≤ 2√3·d ≤ 1/2 ≤ ‖u − v‖`. -/
theorem ellGaussian_isoperimetry_openClosed_logTwo_witness (hn : 2 ≤ n) :
    ∃ (K : Set (EuclideanSpace ℝ (Fin n))) (δ σ d : ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
      (h : EuclideanSpace ℝ (Fin n) → ℝ),
      Convex ℝ K ∧ MeasurableSet K ∧ Bornology.IsBounded K ∧ volume K ≠ 0 ∧ volume K ≠ ⊤ ∧
        0 < δ ∧ 0 < σ ∧ 0 < d ∧ volume (ball x₀ δ ∩ K) ≠ 0 ∧
        (∀ x, h x = (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) ∧
        Continuous h ∧ IsLogConcave (fun x => (ell K δ x).toReal) ∧
        0 < ∫ x, h x := by
  have hn0 : n ≠ 0 := by omega
  refine ⟨ball (0 : EuclideanSpace ℝ (Fin n)) 1, 1, 1, 1 / 8, 0,
    fun x => (ell (ball (0 : EuclideanSpace ℝ (Fin n)) 1) 1 x).toReal
      * Real.exp (-‖x‖ ^ 2 / (2 * (1 : ℝ) ^ 2)),
    convex_ball _ _, measurableSet_ball, isBounded_ball,
    (measure_ball_pos volume 0 one_pos).ne', measure_ball_lt_top.ne, one_pos, one_pos,
    by norm_num, ?_, fun _ => rfl, ?_,
    isLogConcave_ell_toReal measurableSet_ball (convex_ball _ _) 1, ?_⟩
  · rw [Set.inter_self]
    exact (measure_ball_pos volume 0 one_pos).ne'
  · exact (continuous_ell_toReal hn0 zero_le_one).mul (by fun_prop)
  · -- the total mass is positive: `h` is continuous and strictly positive at the origin
    set K : Set (EuclideanSpace ℝ (Fin n)) := ball (0 : EuclideanSpace ℝ (Fin n)) 1 with hKdef
    set h : EuclideanSpace ℝ (Fin n) → ℝ :=
      fun x => (ell K 1 x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * (1 : ℝ) ^ 2)) with hhdef
    have hhc : Continuous h :=
      (continuous_ell_toReal hn0 zero_le_one).mul (by fun_prop)
    have hh0 : ∀ x, 0 ≤ h x := fun x =>
      mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le
    have hell1 : ∀ x : EuclideanSpace ℝ (Fin n), (ell K 1 x).toReal ≤ 1 := by
      intro x
      have := ENNReal.toReal_mono ENNReal.one_ne_top (ell_le_one K 1 x)
      simpa using this
    have hgi : Integrable fun x : EuclideanSpace ℝ (Fin n) =>
        Real.exp (-‖x‖ ^ 2 / (2 * (1 : ℝ) ^ 2)) := by
      have := integrable_gaussianWeightReal (n := n) (σ := 1) one_pos
      simpa [gaussianWeightReal] using this
    have hhi : Integrable h := by
      refine hgi.mono' hhc.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hh0 x), hhdef]
      exact mul_le_of_le_one_left (Real.exp_pos _).le (hell1 x)
    have hx₀ : 0 < h (0 : EuclideanSpace ℝ (Fin n)) := by
      refine mul_pos ?_ (Real.exp_pos _)
      refine ENNReal.toReal_pos ?_ (ne_top_of_le_ne_top ENNReal.one_ne_top (ell_le_one K 1 0))
      rw [ell_apply, hKdef, Set.inter_self]
      exact ENNReal.div_ne_zero.2
        ⟨(measure_ball_pos volume 0 one_pos).ne', measure_ball_lt_top.ne⟩
    rw [integral_pos_iff_support_of_nonneg hh0 hhi]
    have hopen : IsOpen {x : EuclideanSpace ℝ (Fin n) | 0 < h x} :=
      isOpen_lt continuous_const hhc
    refine lt_of_lt_of_le (hopen.measure_pos volume ⟨0, hx₀⟩) (measure_mono ?_)
    intro z hz
    exact ne_of_gt hz

/-- **Non-degenerate non-vacuity for `Arlib.ellGaussian_isoperimetry_openClosed_logTwo`.**

The witness of `Arlib.ellGaussian_isoperimetry_openClosed_logTwo_witness` extended with an
explicit admissible partition, so that the *conclusion* of the theorem is a genuine inequality
between strictly positive quantities and not the trivial `0 ≤ something`.

`K = B(0,1)`, `δ = 1`, `σ = 1`, `d = 1/8`, and the slab partition orthogonal to the first
coordinate axis

  `S₁ = {x j < −1/4}`,  `S₂ = {1/4 < x j}`,  `S₃ = {−1/4 ≤ x j} ∩ {x j ≤ 1/4}`,

whose first two parts are open and whose third is closed.  The separation hypothesis fires on
the metric branch: `‖u − v‖ ≥ |u j − v j| > 1/2 ≥ (1/8)/log 2`, using `log 2 > 1/4`.  Both
`∫_{S₁} h` and `∫_{S₂} h` are strictly positive because `h` is continuous and strictly positive
at `∓(1/2)·e_j`, points at which the proposal ball meets `K` in positive volume. -/
theorem ellGaussian_isoperimetry_openClosed_logTwo_strict_witness (hn : 2 ≤ n) :
    ∃ (K S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))) (δ σ d : ℝ)
      (x₀ : EuclideanSpace ℝ (Fin n)) (h : EuclideanSpace ℝ (Fin n) → ℝ),
      Convex ℝ K ∧ MeasurableSet K ∧ volume K ≠ 0 ∧ volume K ≠ ⊤ ∧
        0 < δ ∧ 0 < σ ∧ 0 < d ∧ volume (ball x₀ δ ∩ K) ≠ 0 ∧
        (∀ x, h x = (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) ∧
        IsPartition3 Set.univ S₁ S₂ S₃ ∧ IsOpen S₁ ∧ IsOpen S₂ ∧ IsClosed S₃ ∧
        (∀ u ∈ S₁, ∀ v ∈ S₂,
          d / Real.log 2 ≤ ‖u - v‖ ∨ 4 * (d / σ) * Real.sqrt n ≤ densDist h u v) ∧
        0 < d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x) := by
  have hn0 : (0 : ℕ) < n := by omega
  set j : Fin n := ⟨0, hn0⟩ with hjdef
  have hproj : Continuous fun z : EuclideanSpace ℝ (Fin n) => z j :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).continuous
  have hcoord : ∀ z : EuclideanSpace ℝ (Fin n), |z j| ≤ ‖z‖ := by
    intro z
    have hEq := EuclideanSpace.norm_eq z
    have hle : ‖z j‖ ^ 2 ≤ ∑ i, ‖z i‖ ^ 2 :=
      Finset.single_le_sum (f := fun i => ‖z i‖ ^ 2) (fun i _ => by positivity)
        (Finset.mem_univ j)
    have hs : |z j| ≤ Real.sqrt (∑ i, ‖z i‖ ^ 2) := by
      rw [show |z j| = Real.sqrt (‖z j‖ ^ 2) by
        rw [Real.sqrt_sq_eq_abs, Real.norm_eq_abs, abs_abs]]
      exact Real.sqrt_le_sqrt hle
    rwa [← hEq] at hs
  set K : Set (EuclideanSpace ℝ (Fin n)) := ball (0 : EuclideanSpace ℝ (Fin n)) 1 with hKdef
  set h : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => (ell K 1 x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * (1 : ℝ) ^ 2)) with hhdef
  have hhc : Continuous h :=
    (continuous_ell_toReal (by omega) zero_le_one).mul (by fun_prop)
  have hh0 : ∀ x, 0 ≤ h x := fun x =>
    mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le
  have hell1 : ∀ x : EuclideanSpace ℝ (Fin n), (ell K 1 x).toReal ≤ 1 := by
    intro x
    have := ENNReal.toReal_mono ENNReal.one_ne_top (ell_le_one K 1 x)
    simpa using this
  have hgi : Integrable fun x : EuclideanSpace ℝ (Fin n) =>
      Real.exp (-‖x‖ ^ 2 / (2 * (1 : ℝ) ^ 2)) := by
    have := integrable_gaussianWeightReal (n := n) (σ := 1) one_pos
    simpa [gaussianWeightReal] using this
  have hhi : Integrable h := by
    refine hgi.mono' hhc.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hh0 x), hhdef]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (hell1 x)
  -- `h` is strictly positive at every point of the half-radius ball
  have hhpos : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 / 2 → 0 < h x := by
    intro x hx
    refine mul_pos ?_ (Real.exp_pos _)
    refine ENNReal.toReal_pos ?_ (ne_top_of_le_ne_top ENNReal.one_ne_top (ell_le_one K 1 x))
    rw [ell_apply]
    refine ENNReal.div_ne_zero.2 ⟨?_, measure_ball_lt_top.ne⟩
    have hsub : ball x (1 / 2 : ℝ) ⊆ ball x 1 ∩ K := by
      intro z hz
      have hzx : ‖z - x‖ < 1 / 2 := by rw [← dist_eq_norm]; exact hz
      refine ⟨mem_ball.2 (by rw [dist_eq_norm]; linarith), ?_⟩
      rw [hKdef, mem_ball, dist_zero_right]
      calc ‖z‖ = ‖z - x + x‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
        _ < 1 := by linarith
    exact ne_of_gt (lt_of_lt_of_le (measure_ball_pos volume x (by norm_num))
      (measure_mono hsub))
  -- strict positivity of the integral over any open set carrying a point where `h > 0`
  have hintpos : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsOpen S →
      ∀ z ∈ S, 0 < h z → 0 < ∫ x in S, h x := by
    intro S hS z hzS hz
    rw [← integral_indicator hS.measurableSet,
      integral_pos_iff_support_of_nonneg
        (fun x => Set.indicator_nonneg (fun y _ => hh0 y) x)
        (hhi.indicator hS.measurableSet)]
    refine lt_of_lt_of_le
      ((hS.inter (isOpen_lt continuous_const hhc)).measure_pos volume ⟨z, hzS, hz⟩)
      (measure_mono ?_)
    rintro w ⟨hw1, hw2⟩
    rw [Function.mem_support, Set.indicator_of_mem hw1]
    exact ne_of_gt hw2
  -- the two test points
  set p : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j (-(1 / 2) : ℝ) with hpdef
  set q : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j (1 / 2 : ℝ) with hqdef
  have hpn : ‖p‖ = 1 / 2 := by
    rw [hpdef, PiLp.norm_single, Real.norm_eq_abs]; norm_num
  have hqn : ‖q‖ = 1 / 2 := by
    rw [hqdef, PiLp.norm_single, Real.norm_eq_abs]; norm_num
  have hpj : p j = -(1 / 2 : ℝ) := by rw [hpdef]; simp
  have hqj : q j = (1 / 2 : ℝ) := by rw [hqdef]; simp
  refine ⟨K, {x : EuclideanSpace ℝ (Fin n) | x j < -(1 / 4 : ℝ)},
    {x : EuclideanSpace ℝ (Fin n) | (1 / 4 : ℝ) < x j},
    {x : EuclideanSpace ℝ (Fin n) | -(1 / 4 : ℝ) ≤ x j} ∩
      {x : EuclideanSpace ℝ (Fin n) | x j ≤ (1 / 4 : ℝ)},
    1, 1, 1 / 8, 0, h, convex_ball _ _, measurableSet_ball,
    (measure_ball_pos volume 0 one_pos).ne', measure_ball_lt_top.ne, one_pos, one_pos,
    by norm_num, ?_, fun _ => rfl, ?_, isOpen_lt hproj continuous_const,
    isOpen_lt continuous_const hproj,
    (isClosed_le continuous_const hproj).inter (isClosed_le hproj continuous_const), ?_, ?_⟩
  · rw [hKdef, Set.inter_self]
    exact (measure_ball_pos volume 0 one_pos).ne'
  · refine { union := ?_, disjoint₁₂ := ?_, disjoint₁₃ := ?_, disjoint₂₃ := ?_ }
    · ext x
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      rcases lt_or_ge (x j) (-(1 / 4) : ℝ) with hx | hx
      · exact Or.inl (Or.inl hx)
      · rcases lt_or_ge (1 / 4 : ℝ) (x j) with hx' | hx'
        · exact Or.inl (Or.inr hx')
        · exact Or.inr ⟨hx, hx'⟩
    · exact Set.disjoint_left.2 (by
        intro a ha ha'; simp only [Set.mem_setOf_eq] at ha ha'; linarith)
    · exact Set.disjoint_left.2 (by
        intro a ha ha'; simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at ha ha'
        linarith [ha'.1])
    · exact Set.disjoint_left.2 (by
        intro a ha ha'; simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at ha ha'
        linarith [ha'.2])
  · intro u hu v hv
    left
    simp only [Set.mem_setOf_eq] at hu hv
    have hlog : (1 / 4 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have hlog0 : (0 : ℝ) < Real.log 2 := by linarith
    have habs : (1 / 2 : ℝ) < |(u - v) j| := by
      have huv : (u - v) j = u j - v j := by simp
      rw [huv, abs_of_nonpos (by linarith)]
      linarith
    calc (1 / 8 : ℝ) / Real.log 2 ≤ 1 / 2 := by
          rw [div_le_iff₀ hlog0]; linarith
      _ ≤ ‖u - v‖ := le_trans habs.le (hcoord (u - v))
  · have h₁ : 0 < ∫ x in {x : EuclideanSpace ℝ (Fin n) | x j < -(1 / 4 : ℝ)}, h x :=
      hintpos _ (isOpen_lt hproj continuous_const) p (by
        simp only [Set.mem_setOf_eq, hpj]; norm_num) (hhpos p (by rw [hpn]))
    have h₂ : 0 < ∫ x in {x : EuclideanSpace ℝ (Fin n) | (1 / 4 : ℝ) < x j}, h x :=
      hintpos _ (isOpen_lt continuous_const hproj) q (by
        simp only [Set.mem_setOf_eq, hqj]; norm_num) (hhpos q (by rw [hqn]))
    positivity

end Isoperimetry

end Arlib

/-! ### Axiom audit -/

#print axioms Arlib.volume_preimage_toLp_eq
#print axioms Arlib.preimage_toLp_add_eq
#print axioms Arlib.preimage_toLp_smul_eq
#print axioms Arlib.brunn_minkowski_mul_euclidean
#print axioms Arlib.ball_inter_convex_combination_subset
#print axioms Arlib.isLogConcave_volume_ball_inter
#print axioms Arlib.isLogConcave_ell_toReal
#print axioms Arlib.isLogConcave_indicator_mul_ell_toReal
#print axioms Arlib.isLogConcave_ell_toReal_witness
#print axioms Arlib.isLogConcave_indicator_mul_ell_toReal_witness
#print axioms Arlib.nontrivial_euclideanSpace
#print axioms Arlib.volume_ball_toReal
#print axioms Arlib.volume_ball_inter_toReal_le
#print axioms Arlib.continuous_volume_ball_inter_toReal
#print axioms Arlib.continuous_ell_toReal
#print axioms Arlib.ellGaussian_isoperimetry_openClosed_logTwo
#print axioms Arlib.ellGaussian_isoperimetry_openClosed_logTwo_witness
#print axioms Arlib.ellGaussian_isoperimetry_openClosed_logTwo_strict_witness
