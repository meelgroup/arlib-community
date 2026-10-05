/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.Convexity.DyerFrieze
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Prod

/-!
# An unconditional isoperimetric inequality for a convex body, with an explicit constant

This file proves — outright, with no hypothesis carried — the three-set isoperimetric
inequality in the exact shape consumed by `Arlib.conductance_ballWalk_ge`'s `hiso`
argument, for **every** bounded convex body, and in particular for the Euclidean unit
ball.

> Let `K ⊆ ℝⁿ` be convex with `diam K ≤ D`, let `A, B ⊆ K` be measurable with
> `dist u v ≥ d` for all `u ∈ A`, `v ∈ B`, and put `C = K \ A \ B`.  Then
> `(d/D) · vol A · vol B ≤ 2ⁿ · vol C · vol K`,
> equivalently `κ · d · π A · π B ≤ π C` for `π = uniformOn volume K` and
> `κ = (1/2)ⁿ / D`.

The constant `(1/2)ⁿ/D` is exponentially worse in the dimension than the truth `2/D`
(Lovász–Simonovits / Dyer–Frieze), which needs localization.  It is, however, **positive
and explicit**, and it is *proved*, so every theorem in this development that carries
`hiso` as an inline `∀`-hypothesis can be instantiated with it and becomes unconditional.

## The proof, in four lines

Fix `a ∈ A`, `b ∈ B`.  The chord `λ ↦ (1-λ)a + λb` lies in `K`; the parameters landing in
`A` and those landing in `B` are `(d/‖b-a‖)`-separated subsets of `[0,1]` containing `0`
and `1` respectively, so `Arlib.exists_gap_of_separated` produces a parameter interval of
length `≥ d/‖b-a‖ ≥ d/D` all of whose points land in `C`.  Integrating this over
`A × B` (Tonelli) gives

    (d/D) · vol A · vol B  ≤  M₁ + M₂,

where `Mᵢ` is the mass of `{(a,b,λ) : (1-λ)a + λb ∈ C}` with `λ` confined to `[0,½]` and
`[½,1]`.  Re-slicing the *same* set the other way bounds each `Mᵢ`: for fixed `λ` and
fixed `a`, the map `b ↦ (1-λ)a + λb` is affine with linear part `λ·id`, so it multiplies
volume by `λⁿ`, and its fibre over `C` has volume at most `λ⁻ⁿ·vol C ≤ 2ⁿ·vol C` when
`λ ≥ ½`; symmetrically in `a` when `λ ≤ ½`.  Hence
`M₂ ≤ 2ⁿ · vol C · vol A · ½` and `M₁ ≤ 2ⁿ · vol C · vol B · ½`, and `vol A, vol B ≤ vol K`
finishes it.  The `2ⁿ` is exactly the price of using the crude bound
`max(λ, 1-λ) ≥ ½` in place of a localization argument.

## Main results

* `Arlib.ofReal_div_le_volume_chordFree_add` — the one-dimensional input, per chord.
* `Arlib.volume_inter_setOf_affine_mem_le` — the affine-fibre volume bound.
* `Arlib.volume_mul_volume_le_of_separated` — the inequality in volume form, for any
  bounded convex body.
* `Arlib.uniformOn_iso_of_convex` — the same in the exact `hiso` shape,
  `κ = (1/2)ⁿ/D`.
* `Arlib.uniformOn_iso_unitBall` — the specialisation to `Metric.ball 0 1`, `κ =
  (1/2)ⁿ⁺¹`.  This is a closed statement with no hypotheses at all.

Nothing here is a `def`, `structure`, `class` or named `Prop` asserting an isoperimetric
inequality: every declaration below is a theorem proved outright.
-/

namespace Arlib

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ}

/-! ### The one-dimensional input, transported to a chord -/

/-- **Every chord from `A` to `B` spends parameter-time at least `d/D` in `C = K \ A \ B`.**

Along the chord `λ ↦ (1-λ)·a + λ·b` (which lies in `K` by convexity), the parameters
landing in `A` and those landing in `B` are `(d/‖b-a‖)`-separated subsets of `[0,1]`
containing `0` and `1`; `Arlib.exists_gap_of_separated` therefore produces an open
parameter interval of length at least `d/‖b-a‖ ≥ d/D` avoiding both, i.e. landing in `C`.

The conclusion is stated as the sum of the two half-interval masses because that is the
form the Tonelli argument in `Arlib.volume_mul_volume_le_of_separated` consumes: the
bound on a fibre is `λ⁻ⁿ` on `[½,1]` and `(1-λ)⁻ⁿ` on `[0,½]`, so the two halves are
estimated by different slicings of the same set. -/
theorem ofReal_div_le_volume_chordFree_add
    {K A B : Set (EuclideanSpace ℝ (Fin n))} {d D : ℝ} (hd : 0 < d)
    (hK : Convex ℝ K) (hAK : A ⊆ K) (hBK : B ⊆ K)
    (hsep : ∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    {a b : EuclideanSpace ℝ (Fin n)} (ha : a ∈ A) (hb : b ∈ B) :
    ENNReal.ofReal (d / D)
      ≤ volume ({lam : ℝ | (1 - lam) • a + lam • b ∈ (K \ A) \ B} ∩ Icc 0 (1 / 2))
        + volume ({lam : ℝ | (1 - lam) • a + lam • b ∈ (K \ A) \ B} ∩ Icc (1 / 2) 1) := by
  classical
  have hdab : d ≤ dist a b := hsep a ha b hb
  have hrpos : 0 < ‖b - a‖ := by
    have h0 : (0 : ℝ) < dist a b := lt_of_lt_of_le hd hdab
    rwa [dist_eq_norm, ← norm_neg, neg_sub] at h0
  set r : ℝ := ‖b - a‖ with hrdef
  have hrD : r ≤ D := by
    have h := hdiam a (hAK ha) b (hBK hb)
    rwa [dist_eq_norm, ← norm_neg, neg_sub] at h
  -- distances along the chord
  have hdist : ∀ s t : ℝ,
      dist ((1 - s) • a + s • b) ((1 - t) • a + t • b) = |s - t| * r := by
    intro s t
    have heq : ((1 - s) • a + s • b) - ((1 - t) • a + t • b) = (s - t) • (b - a) := by
      module
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, hrdef]
  have hchordK : ∀ t ∈ Icc (0 : ℝ) 1, (1 - t) • a + t • b ∈ K := by
    intro t ht
    exact hK (hAK ha) (hBK hb) (by linarith [ht.2]) ht.1 (by ring)
  set A' : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧ (1 - t) • a + t • b ∈ A} with hA'
  set B' : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧ (1 - t) • a + t • b ∈ B} with hB'
  have h0A : (0 : ℝ) ∈ A' := by
    refine ⟨⟨le_rfl, zero_le_one⟩, ?_⟩
    simpa using ha
  have h1B : (1 : ℝ) ∈ B' := by
    refine ⟨⟨zero_le_one, le_rfl⟩, ?_⟩
    simpa using hb
  have hsep' : ∀ s ∈ A', ∀ t ∈ B', d / r ≤ |s - t| := by
    intro s hs t ht
    have hle := hsep _ hs.2 _ ht.2
    rw [hdist] at hle
    rw [div_le_iff₀ hrpos]
    exact hle
  obtain ⟨s, t, hs0, ht1, hdt, hgap⟩ := exists_gap_of_separated h0A h1B zero_le_one hsep'
  have hdr : 0 < d / r := div_pos hd hrpos
  have hst : s < t := by linarith
  -- the free parameter interval
  have hsub : Ioo s t ⊆ {lam : ℝ | (1 - lam) • a + lam • b ∈ (K \ A) \ B} ∩ Icc 0 1 := by
    intro z hz
    have hzmem : z ∈ Icc (0 : ℝ) 1 := ⟨le_trans hs0 hz.1.le, le_trans hz.2.le ht1⟩
    obtain ⟨hnA, hnB⟩ := hgap z hz
    exact ⟨⟨⟨hchordK z hzmem, fun h => hnA ⟨hzmem, h⟩⟩, fun h => hnB ⟨hzmem, h⟩⟩, hzmem⟩
  have hcover : {lam : ℝ | (1 - lam) • a + lam • b ∈ (K \ A) \ B} ∩ Icc 0 1
      ⊆ ({lam : ℝ | (1 - lam) • a + lam • b ∈ (K \ A) \ B} ∩ Icc 0 (1 / 2))
        ∪ ({lam : ℝ | (1 - lam) • a + lam • b ∈ (K \ A) \ B} ∩ Icc (1 / 2) 1) := by
    rintro z ⟨hz1, hz2⟩
    rcases le_total z (1 / 2 : ℝ) with h | h
    · exact Or.inl ⟨hz1, hz2.1, h⟩
    · exact Or.inr ⟨hz1, h, hz2.2⟩
  have hDr : d / D ≤ d / r := by
    have hDpos : 0 < D := lt_of_lt_of_le hrpos hrD
    rw [div_le_div_iff₀ hDpos hrpos]
    nlinarith
  calc ENNReal.ofReal (d / D) ≤ ENNReal.ofReal (t - s) := by
        apply ENNReal.ofReal_le_ofReal; linarith
    _ = volume (Ioo s t) := Real.volume_Ioo.symm
    _ ≤ volume ({lam : ℝ | (1 - lam) • a + lam • b ∈ (K \ A) \ B} ∩ Icc 0 1) :=
        measure_mono hsub
    _ ≤ _ := le_trans (measure_mono hcover) (measure_union_le _ _)

/-! ### The affine-fibre volume bound -/

/-- **The fibre of `C` under an affine map with linear part `r·id` has volume
`≤ |r|⁻ⁿ · vol C`.**

`x ↦ c + r·x` is a translation composed with a dilation by `r`, so it scales Lebesgue
measure by `|r|ⁿ`; the displayed set is contained in the preimage of `C`. -/
theorem volume_inter_setOf_affine_mem_le (C T : Set (EuclideanSpace ℝ (Fin n)))
    (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : r ≠ 0) :
    volume ({x : EuclideanSpace ℝ (Fin n) | c + r • x ∈ C} ∩ T)
      ≤ ENNReal.ofReal |(r ^ n)⁻¹| * volume C := by
  have hsub : {x : EuclideanSpace ℝ (Fin n) | c + r • x ∈ C} ∩ T
      ⊆ (fun x : EuclideanSpace ℝ (Fin n) => r • x) ⁻¹'
          ((fun y : EuclideanSpace ℝ (Fin n) => c + y) ⁻¹' C) := fun x hx => hx.1
  calc volume ({x : EuclideanSpace ℝ (Fin n) | c + r • x ∈ C} ∩ T)
      ≤ volume ((fun x : EuclideanSpace ℝ (Fin n) => r • x) ⁻¹'
          ((fun y : EuclideanSpace ℝ (Fin n) => c + y) ⁻¹' C)) := measure_mono hsub
    _ = ENNReal.ofReal |(r ^ n)⁻¹|
          * volume ((fun y : EuclideanSpace ℝ (Fin n) => c + y) ⁻¹' C) := by
        rw [Measure.addHaar_preimage_smul volume hr, finrank_euclideanSpace_fin]
    _ = ENNReal.ofReal |(r ^ n)⁻¹| * volume C := by
        rw [measure_preimage_add]

/-- `|(r ^ n)⁻¹| ≤ 2 ^ n` for `1/2 ≤ r`, in `ℝ≥0∞`. -/
theorem ofReal_abs_inv_pow_le_two_pow {r : ℝ} (h1 : 1 / 2 ≤ r) :
    ENNReal.ofReal |(r ^ n)⁻¹| ≤ (2 : ℝ≥0∞) ^ n := by
  have hr0 : (0 : ℝ) < r := by linarith
  have hpow : (1 / 2 : ℝ) ^ n ≤ r ^ n := pow_le_pow_left₀ (by norm_num) h1 n
  have hrn : (0 : ℝ) < r ^ n := pow_pos hr0 n
  have hle : |(r ^ n)⁻¹| ≤ (2 : ℝ) ^ n := by
    rw [abs_of_pos (inv_pos.2 hrn)]
    have h2n : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
    calc (r ^ n)⁻¹ = 1 / r ^ n := (one_div _).symm
      _ ≤ 1 / (1 / 2 : ℝ) ^ n := one_div_le_one_div_of_le h2n hpow
      _ = (2 : ℝ) ^ n := by
          rw [one_div, ← inv_pow]; norm_num
  calc ENNReal.ofReal |(r ^ n)⁻¹| ≤ ENNReal.ofReal ((2 : ℝ) ^ n) :=
        ENNReal.ofReal_le_ofReal hle
    _ = (2 : ℝ≥0∞) ^ n := by
        rw [ENNReal.ofReal_pow (by norm_num)]
        norm_num

/-! ### The isoperimetric inequality, in volume form -/

/-- **The three-set isoperimetric inequality for a bounded convex body**, with the
explicit constant `2⁻ⁿ/D`:

    (d/D) · vol A · vol B  ≤  2ⁿ · vol (K \ A \ B) · vol K.

No hypothesis is carried: this is proved outright.  See the module docstring for the
argument; the `2ⁿ` is the price of avoiding localization. -/
theorem volume_mul_volume_le_of_separated
    {K A B : Set (EuclideanSpace ℝ (Fin n))} {d D : ℝ} (hd : 0 < d)
    (hK : Convex ℝ K) (hKm : MeasurableSet K)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAK : A ⊆ K) (hBK : B ⊆ K)
    (hsep : ∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) :
    ENNReal.ofReal (d / D) * volume A * volume B
      ≤ 2 ^ n * volume ((K \ A) \ B) * volume K := by
  classical
  have hCm : MeasurableSet ((K \ A) \ B) := (hKm.diff hA).diff hB
  have hcont : Continuous fun p :
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) × ℝ =>
      (1 - p.2) • p.1.1 + p.2 • p.1.2 := by fun_prop
  set W : Set ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) × ℝ) :=
    {p | (1 - p.2) • p.1.1 + p.2 • p.1.2 ∈ (K \ A) \ B} with hWdef
  have hWm : MeasurableSet W := hcont.measurable hCm
  set muAB : Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    (volume.restrict A).prod (volume.restrict B) with hmuABdef
  set muL1 : Measure ℝ := volume.restrict (Icc (0 : ℝ) (1 / 2)) with hmuL1def
  set muL2 : Measure ℝ := volume.restrict (Icc (1 / 2 : ℝ) 1) with hmuL2def
  -- the slices of `W` are measurable
  have hslice : ∀ q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      MeasurableSet (Prod.mk q ⁻¹' W) := fun q => measurable_prodMk_left hWm
  have hslice' : ∀ lam : ℝ, MeasurableSet ((fun q => (q, lam)) ⁻¹' W) := fun lam =>
    measurable_prodMk_right hWm
  -- ### Lower bound
  have hlow : ENNReal.ofReal (d / D) * volume A * volume B
      ≤ (muAB.prod muL1) W + (muAB.prod muL2) W := by
    rw [Measure.prod_apply hWm, Measure.prod_apply hWm,
      ← lintegral_add_left (measurable_measure_prodMk_left hWm), hmuABdef,
      Measure.prod_restrict]
    have hconst : ENNReal.ofReal (d / D) * volume A * volume B
        = ∫⁻ _ in A ×ˢ B, ENNReal.ofReal (d / D)
            ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).prod volume) := by
      rw [setLIntegral_const, Measure.prod_prod, mul_assoc]
    rw [hconst]
    refine setLIntegral_mono' (hA.prod hB) ?_
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    rw [hmuL1def, hmuL2def, Measure.restrict_apply (hslice (u, v)),
      Measure.restrict_apply (hslice (u, v))]
    exact ofReal_div_le_volume_chordFree_add hd hK hAK hBK hsep hdiam hu hv
  -- ### Upper bound on the `λ ∈ [1/2, 1]` piece: slice in `b`
  have hup2 : (muAB.prod muL2) W ≤ 2 ^ n * volume ((K \ A) \ B) * volume A * (1 / 2) := by
    rw [Measure.prod_apply_symm hWm, hmuL2def]
    have hbound : ∀ lam ∈ Icc (1 / 2 : ℝ) 1,
        muAB ((fun q => (q, lam)) ⁻¹' W)
          ≤ 2 ^ n * volume ((K \ A) \ B) * volume A := by
      intro lam hlam
      have hlam0 : lam ≠ 0 := by
        have : (0 : ℝ) < lam := by linarith [hlam.1]
        exact ne_of_gt this
      rw [hmuABdef, Measure.prod_apply (hslice' lam)]
      have hpt : ∀ u : EuclideanSpace ℝ (Fin n),
          (volume.restrict B) (Prod.mk u ⁻¹' ((fun q => (q, lam)) ⁻¹' W))
            ≤ 2 ^ n * volume ((K \ A) \ B) := by
        intro u
        have hmeasset : MeasurableSet
            (Prod.mk u ⁻¹' ((fun q => (q, lam)) ⁻¹' W)) :=
          measurable_prodMk_left (hslice' lam)
        rw [Measure.restrict_apply hmeasset]
        have hset : (Prod.mk u ⁻¹' ((fun q => (q, lam)) ⁻¹' W)) ∩ B
            = {x : EuclideanSpace ℝ (Fin n) | (1 - lam) • u + lam • x ∈ (K \ A) \ B} ∩ B :=
          rfl
        rw [hset]
        exact le_trans (volume_inter_setOf_affine_mem_le _ _ _ hlam0)
          (mul_le_mul_left (ofReal_abs_inv_pow_le_two_pow hlam.1) _)
      calc ∫⁻ u, (volume.restrict B) (Prod.mk u ⁻¹' ((fun q => (q, lam)) ⁻¹' W))
              ∂(volume.restrict A)
          ≤ ∫⁻ _, 2 ^ n * volume ((K \ A) \ B) ∂(volume.restrict A) :=
            lintegral_mono hpt
        _ = 2 ^ n * volume ((K \ A) \ B) * volume A := by
            rw [lintegral_const, Measure.restrict_apply_univ]
    calc ∫⁻ lam, muAB ((fun q => (q, lam)) ⁻¹' W) ∂(volume.restrict (Icc (1 / 2 : ℝ) 1))
        ≤ ∫⁻ _ in Icc (1 / 2 : ℝ) 1, 2 ^ n * volume ((K \ A) \ B) * volume A :=
          setLIntegral_mono' measurableSet_Icc hbound
      _ = 2 ^ n * volume ((K \ A) \ B) * volume A * (1 / 2) := by
          rw [setLIntegral_const, Real.volume_Icc]
          norm_num
          rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
          norm_num
  -- ### Upper bound on the `λ ∈ [0, 1/2]` piece: slice in `a`
  have hup1 : (muAB.prod muL1) W ≤ 2 ^ n * volume ((K \ A) \ B) * volume B * (1 / 2) := by
    rw [Measure.prod_apply_symm hWm, hmuL1def]
    have hbound : ∀ lam ∈ Icc (0 : ℝ) (1 / 2),
        muAB ((fun q => (q, lam)) ⁻¹' W)
          ≤ 2 ^ n * volume ((K \ A) \ B) * volume B := by
      intro lam hlam
      have hlam0 : (1 - lam) ≠ 0 := by
        have : (0 : ℝ) < 1 - lam := by linarith [hlam.2]
        exact ne_of_gt this
      rw [hmuABdef, Measure.prod_apply_symm (hslice' lam)]
      have hpt : ∀ v : EuclideanSpace ℝ (Fin n),
          (volume.restrict A) ((fun u => (u, v)) ⁻¹' ((fun q => (q, lam)) ⁻¹' W))
            ≤ 2 ^ n * volume ((K \ A) \ B) := by
        intro v
        have hmeasset : MeasurableSet
            ((fun u => (u, v)) ⁻¹' ((fun q => (q, lam)) ⁻¹' W)) :=
          measurable_prodMk_right (hslice' lam)
        rw [Measure.restrict_apply hmeasset]
        have hset : ((fun u => (u, v)) ⁻¹' ((fun q => (q, lam)) ⁻¹' W)) ∩ A
            = {x : EuclideanSpace ℝ (Fin n) | lam • v + (1 - lam) • x ∈ (K \ A) \ B} ∩ A := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, hWdef, and_congr_left_iff]
          intro _
          rw [add_comm]
        rw [hset]
        refine le_trans (volume_inter_setOf_affine_mem_le _ _ _ hlam0)
          (mul_le_mul_left (ofReal_abs_inv_pow_le_two_pow ?_) _)
        linarith [hlam.2]
      calc ∫⁻ v, (volume.restrict A) ((fun u => (u, v)) ⁻¹' ((fun q => (q, lam)) ⁻¹' W))
              ∂(volume.restrict B)
          ≤ ∫⁻ _, 2 ^ n * volume ((K \ A) \ B) ∂(volume.restrict B) :=
            lintegral_mono hpt
        _ = 2 ^ n * volume ((K \ A) \ B) * volume B := by
            rw [lintegral_const, Measure.restrict_apply_univ]
    calc ∫⁻ lam, muAB ((fun q => (q, lam)) ⁻¹' W) ∂(volume.restrict (Icc (0 : ℝ) (1 / 2)))
        ≤ ∫⁻ _ in Icc (0 : ℝ) (1 / 2), 2 ^ n * volume ((K \ A) \ B) * volume B :=
          setLIntegral_mono' measurableSet_Icc hbound
      _ = 2 ^ n * volume ((K \ A) \ B) * volume B * (1 / 2) := by
          rw [setLIntegral_const, Real.volume_Icc]
          norm_num
          rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
          norm_num
  -- ### Assemble
  have hAKvol : volume A ≤ volume K := measure_mono hAK
  have hBKvol : volume B ≤ volume K := measure_mono hBK
  calc ENNReal.ofReal (d / D) * volume A * volume B
      ≤ (muAB.prod muL1) W + (muAB.prod muL2) W := hlow
    _ ≤ 2 ^ n * volume ((K \ A) \ B) * volume B * (1 / 2)
        + 2 ^ n * volume ((K \ A) \ B) * volume A * (1 / 2) := add_le_add hup1 hup2
    _ ≤ 2 ^ n * volume ((K \ A) \ B) * volume K * (1 / 2)
        + 2 ^ n * volume ((K \ A) \ B) * volume K * (1 / 2) :=
        add_le_add (mul_le_mul_left (mul_le_mul_right hBKvol _) _)
          (mul_le_mul_left (mul_le_mul_right hAKvol _) _)
    _ = 2 ^ n * volume ((K \ A) \ B) * volume K := by
        rw [← mul_add]
        rw [ENNReal.add_halves]
        rw [mul_one]

/-! ### The isoperimetric inequality, in `hiso` shape -/

/-- **The isoperimetric inequality in exactly the shape of the `hiso` hypothesis** of
`Arlib.conductance_ballWalk_ge` and `Arlib.mixesWithin_lazy_ballWalk`, for any bounded
convex body `K` of positive finite volume, with `κ = (1/2)ⁿ/D`:

    κ · d · π A · π B  ≤  π (K \ A \ B),    π = uniformOn volume K.

This is `Arlib.volume_mul_volume_le_of_separated` divided through by `(vol K)³`.

**The constant is exponentially small in the dimension, and this caveat belongs with the
result wherever it is quoted.** `κ = 2⁻ⁿ/D`, so every conductance bound and mixing time
downstream is exponentially large in `n`. **Not a polynomial-time result, and not to be
quoted as one.** "Unconditional" and "efficient" are independent claims; this theorem
supplies only the first, and the type — which promises nothing beyond what is written —
shows the good half of the trade without the price.

The `2⁻ⁿ` is exactly the price of the elementary chord argument used here in place of
localization: the crude `max(λ, 1-λ) ≥ ½` where localization would give a dimension-free
constant. Consistency check, at `n = 1`, `K = [0,1]`: this gives `κ = 1/2` against the sharp
`Arlib.uniformOn_dyerFrieze_dim_one`'s `κ = 2` — strictly weaker, as it must be. A
polynomial constant in general needs the localization route, whose remaining obstruction is
(P1) in `Arlib/Convexity/PositionalCut.lean`. -/
theorem uniformOn_iso_of_convex
    {K : Set (EuclideanSpace ℝ (Fin n))} {D : ℝ}
    (hK : Convex ℝ K) (hKm : MeasurableSet K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) :
    ∀ d : ℝ, 0 < d → ∀ A B : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet A → MeasurableSet B → A ⊆ K → B ⊆ K →
      (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) →
      ENNReal.ofReal ((1 / 2 : ℝ) ^ n / D) * ENNReal.ofReal d
          * uniformOn volume K A * uniformOn volume K B
        ≤ uniformOn volume K ((K \ A) \ B) := by
  intro d hd A B hA hB hAK hBK hsep
  have hVinv : volume K * (volume K)⁻¹ = 1 := ENNReal.mul_inv_cancel hK0 hKtop
  have hCK : ((K \ A) \ B) ⊆ K := Set.Subset.trans Set.sdiff_subset Set.sdiff_subset
  have hCm : MeasurableSet ((K \ A) \ B) := (hKm.diff hA).diff hB
  have eA : uniformOn volume K A = volume A * (volume K)⁻¹ := by
    rw [uniformOn_apply volume hKm hA, Set.inter_eq_self_of_subset_left hAK, div_eq_mul_inv]
  have eB : uniformOn volume K B = volume B * (volume K)⁻¹ := by
    rw [uniformOn_apply volume hKm hB, Set.inter_eq_self_of_subset_left hBK, div_eq_mul_inv]
  have eC : uniformOn volume K ((K \ A) \ B) = volume ((K \ A) \ B) * (volume K)⁻¹ := by
    rw [uniformOn_apply volume hKm hCm, Set.inter_eq_self_of_subset_left hCK, div_eq_mul_inv]
  -- `D` is positive as soon as `A` and `B` are both nonempty; otherwise the claim is trivial
  rcases Set.eq_empty_or_nonempty A with rfl | hAne
  · simp [eA]
  rcases Set.eq_empty_or_nonempty B with rfl | hBne
  · simp [eB]
  obtain ⟨u, hu⟩ := hAne
  obtain ⟨v, hv⟩ := hBne
  have hDpos : 0 < D :=
    lt_of_lt_of_le (lt_of_lt_of_le hd (hsep u hu v hv)) (hdiam u (hAK hu) v (hBK hv))
  -- the constant, rewritten
  have hkappa : ENNReal.ofReal ((1 / 2 : ℝ) ^ n / D) * ENNReal.ofReal d
      = ((2 : ℝ≥0∞) ^ n)⁻¹ * ENNReal.ofReal (d / D) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    have harg : (1 / 2 : ℝ) ^ n / D * d = (1 / 2 : ℝ) ^ n * (d / D) := by
      field_simp
    have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2)]
      norm_num
    rw [harg, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), hhalf,
      ← ENNReal.inv_pow]
  have hmain := volume_mul_volume_le_of_separated (D := D) hd hK hKm hA hB hAK hBK hsep hdiam
  have htwo : ((2 : ℝ≥0∞) ^ n)⁻¹ * 2 ^ n = 1 :=
    ENNReal.inv_mul_cancel (by positivity) (by simp)
  rw [eA, eB, eC, hkappa]
  have lhs_eq : ((2 : ℝ≥0∞) ^ n)⁻¹ * ENNReal.ofReal (d / D) * (volume A * (volume K)⁻¹)
        * (volume B * (volume K)⁻¹)
      = ((2 : ℝ≥0∞) ^ n)⁻¹ * (ENNReal.ofReal (d / D) * volume A * volume B)
          * ((volume K)⁻¹) ^ 2 := by
    ring
  rw [lhs_eq]
  calc ((2 : ℝ≥0∞) ^ n)⁻¹ * (ENNReal.ofReal (d / D) * volume A * volume B)
        * ((volume K)⁻¹) ^ 2
      ≤ ((2 : ℝ≥0∞) ^ n)⁻¹ * (2 ^ n * volume ((K \ A) \ B) * volume K)
          * ((volume K)⁻¹) ^ 2 := by
        exact mul_le_mul_left (mul_le_mul_right hmain _) _
    _ = (((2 : ℝ≥0∞) ^ n)⁻¹ * 2 ^ n) * (volume ((K \ A) \ B) * (volume K)⁻¹)
          * (volume K * (volume K)⁻¹) := by ring
    _ = volume ((K \ A) \ B) * (volume K)⁻¹ := by
        rw [htwo, hVinv, one_mul, mul_one]

/-! ### The Euclidean unit ball -/

/-- **The isoperimetric inequality for the Euclidean unit ball, unconditionally.**

    (1/2)ⁿ⁺¹ · d · π A · π B  ≤  π (K \ A \ B),    K = ball 0 1,  π = uniformOn volume K.

This statement has *no* hypotheses beyond the ones written in it: it is a closed theorem
about a concrete body, and it discharges the `hiso` argument of
`Arlib.conductance_ballWalk_ge` and `Arlib.mixesWithin_lazy_ballWalk` at
`K = Metric.ball 0 1`, `kappa = (1/2)ⁿ⁺¹`.

**The constant is exponentially small in the dimension, and this caveat belongs with the
result wherever it is quoted.** `κ = 2⁻⁽ⁿ⁺¹⁾`, so every conductance bound and mixing time
downstream of it is exponentially large in `n`. **Nothing here is a polynomial-time result
and none of it may be quoted as one.** "Unconditional" and "efficient" are independent
claims, and this theorem supplies only the first — which is precisely why it is easy to
misread: the type promises no hypotheses, and a reader who stops at the type sees the good
half of the trade and not the price.

What it *does* settle: that the isoperimetry → conductance → Cheeger → `L²` → total
variation chain composes, and that its joint hypotheses are satisfiable by a real body — a
thing a *sharp* constant merely assumed for all bodies cannot settle. The sharp constant
`κ = 2/D` is proved only in dimension one (`Arlib.uniformOn_dyerFrieze_dim_one`); a
polynomial constant in general needs the localization route, whose remaining obstruction is
(P1) in `Arlib/Convexity/PositionalCut.lean`. -/
theorem uniformOn_iso_unitBall (n : ℕ) :
    ∀ d : ℝ, 0 < d → ∀ A B : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet A → MeasurableSet B →
      A ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 →
      B ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 →
      (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) →
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) * ENNReal.ofReal d
          * uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) A
          * uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) B
        ≤ uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
            ((Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 \ A) \ B) := by
  have hK0 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ 0 :=
    ne_of_gt (Metric.measure_ball_pos volume _ one_pos)
  have hKtop : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ⊤ :=
    ne_of_lt measure_ball_lt_top
  have hdiam : ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1,
      ∀ y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1, dist x y ≤ 2 := by
    intro x hx y hy
    have h1 : dist x 0 < 1 := by simpa [Metric.mem_ball] using hx
    have h2 : dist (0 : EuclideanSpace ℝ (Fin n)) y < 1 := by
      rw [dist_comm]; simpa [Metric.mem_ball] using hy
    calc dist x y ≤ dist x 0 + dist 0 y := dist_triangle _ _ _
      _ ≤ 2 := by linarith
  have hconst : ((1 / 2 : ℝ) ^ n / 2) = (1 / 2 : ℝ) ^ (n + 1) := by
    rw [pow_succ]; ring
  have h := uniformOn_iso_of_convex (D := 2) (convex_ball _ _) measurableSet_ball hK0 hKtop hdiam
  rw [hconst] at h
  exact h

/-! ### Axiom audit

Every declaration in this file is `sorry`-free and depends only on Lean's three standard
axioms.  Re-check with `lake build Arlib.Convexity.IsoBall`. -/

#print axioms ofReal_div_le_volume_chordFree_add
#print axioms volume_inter_setOf_affine_mem_le
#print axioms ofReal_abs_inv_pow_le_two_pow
#print axioms volume_mul_volume_le_of_separated
#print axioms uniformOn_iso_of_convex
#print axioms uniformOn_iso_unitBall

end Arlib
