/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.MeanInequalities

/-!
# One-dimensional Prékopa–Leindler inequality

The headline result is `Arlib.prekopa_leindler_one_dim`: for `lam ∈ (0,1)` and measurable,
nonnegative, integrable `f g h : ℝ → ℝ` with
`f x ^ lam * g y ^ (1 - lam) ≤ h (lam * x + (1 - lam) * y)` for all `x y`,
`(∫ x, f x) ^ lam * (∫ x, g x) ^ (1 - lam) ≤ ∫ x, h x`.

Mathlib has none of this.  The chain of results is:

* `volume_add_le_volume_add_of_isCompact`, `volume_eq_iSup_isCompact_subtype` and
  `volume_add_volume_le_volume_add` — the one-dimensional Brunn–Minkowski inequality
  `volume A + volume B ≤ volume (A + B)` for nonempty measurable `A B : Set ℝ`.
* `smul_setOf_add_smul_setOf_subset` and `measure_setOf_le_combo` — the per-level bound
  `lam * |{f ≥ t}| + (1 - lam) * |{g ≥ t}| ≤ |{h ≥ t}|`.
* `lintegral_combo_le_lintegral` and `integral_combo_le_integral` — integrating the
  per-level bound over `t ∈ (0, ∞)` by the layer cake formula.  This needs the level sets of
  `f` and `g` to be simultaneously (non)empty for a.e. `t`; without such a hypothesis the
  *arithmetic-mean* form is false.
* `rpow_mul_rpow_le_lin_combo` — weighted AM–GM, turning the arithmetic mean into the
  geometric mean.
* `prekopa_leindler_one_dim_of_same_levels`, then `prekopa_leindler_one_dim_of_lub` /
  `prekopa_leindler_one_dim_of_bddAbove` (rescale `f`, `g`, `h` so that `f` and `g` have
  supremum `1`), then `prekopa_leindler_one_dim` (truncate at height `n` and let `n → ∞`).
-/

open MeasureTheory Set Pointwise

namespace Arlib

/-- Superadditivity of Lebesgue measure under Minkowski sum, for **compact** sets:
this is the one-dimensional Brunn–Minkowski inequality in its basic form.

The proof translates `K` so that its greatest element sits at the least element of `L`;
then `K + b` and `a + L` are two subsets of `K + L` overlapping in at most one point. -/
theorem volume_add_le_volume_add_of_isCompact {K L : Set ℝ} (hK : IsCompact K)
    (hL : IsCompact L) (hKne : K.Nonempty) (hLne : L.Nonempty) :
    volume K + volume L ≤ volume (K + L) := by
  obtain ⟨a, haK, hamax⟩ := hK.exists_isGreatest hKne
  obtain ⟨b, hbL, hbmin⟩ := hL.exists_isLeast hLne
  set S : Set ℝ := K + {b} with hS
  set T : Set ℝ := {a} + L with hT
  have hSvol : volume S = volume K := by
    simp [hS, Set.add_singleton, Set.image_add_right]
  have hTvol : volume T = volume L := by
    simp [hT, Set.singleton_add, Set.image_add_left]
  have hTmeas : MeasurableSet T := by
    have : IsCompact T := by
      rw [hT, Set.singleton_add]
      exact hL.image (continuous_const.add continuous_id)
    exact this.measurableSet
  have hsub : S ∪ T ⊆ K + L := by
    refine Set.union_subset ?_ ?_
    · exact Set.add_subset_add_left (Set.singleton_subset_iff.mpr hbL)
    · exact Set.add_subset_add_right (Set.singleton_subset_iff.mpr haK)
  have hinter : S ∩ T ⊆ {a + b} := by
    rintro x ⟨hxS, hxT⟩
    rw [hS, Set.add_singleton, Set.mem_image] at hxS
    rw [hT, Set.singleton_add, Set.mem_image] at hxT
    obtain ⟨k, hk, rfl⟩ := hxS
    obtain ⟨l, hl, hkl⟩ := hxT
    have h1 : k + b ≤ a + b := by have := hamax hk; linarith
    have h2 : a + b ≤ k + b := by have := hbmin hl; linarith
    exact Set.mem_singleton_iff.mpr (le_antisymm h1 h2)
  have hzero : volume (S ∩ T) = 0 := by
    have h := measure_mono (μ := (volume : Measure ℝ)) hinter
    simpa using h
  calc volume K + volume L = volume S + volume T := by rw [hSvol, hTvol]
    _ = volume (S ∪ T) + volume (S ∩ T) := (measure_union_add_inter S hTmeas).symm
    _ = volume (S ∪ T) := by rw [hzero, add_zero]
    _ ≤ volume (K + L) := measure_mono hsub

/-- Inner regularity of Lebesgue measure on `ℝ`, packaged as a supremum over the
(nonempty) type of compact subsets. -/
theorem volume_eq_iSup_isCompact_subtype {C : Set ℝ} (hC : MeasurableSet C) :
    volume C = ⨆ (K : {K : Set ℝ // IsCompact K ∧ K ⊆ C}), volume (K : Set ℝ) := by
  rw [hC.measure_eq_iSup_isCompact volume]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun K => iSup_le fun hKC => iSup_le fun hKc => ?_
    exact le_iSup (fun K : {K : Set ℝ // IsCompact K ∧ K ⊆ C} => volume (K : Set ℝ))
      ⟨K, hKc, hKC⟩
  · exact iSup_le fun K => le_iSup_of_le (K : Set ℝ)
      (le_iSup_of_le K.2.2 (le_iSup_of_le K.2.1 le_rfl))

/-- **One-dimensional Brunn–Minkowski inequality** (superadditivity of Lebesgue measure
under Minkowski sums): for nonempty measurable `A B : Set ℝ`,
`volume A + volume B ≤ volume (A + B)`.

Note that `A + B` need not be measurable; `volume` is used here as an outer measure. -/
theorem volume_add_volume_le_volume_add {A B : Set ℝ} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAne : A.Nonempty) (hBne : B.Nonempty) :
    volume A + volume B ≤ volume (A + B) := by
  obtain ⟨a, haA⟩ := hAne
  obtain ⟨b, hbB⟩ := hBne
  have key : ∀ K L : Set ℝ, IsCompact K → K ⊆ A → IsCompact L → L ⊆ B →
      volume K + volume L ≤ volume (A + B) := by
    intro K L hKc hKA hLc hLB
    rcases K.eq_empty_or_nonempty with rfl | hKne
    · simp only [measure_empty, zero_add]
      calc volume L = volume ({a} + L) := by simp [Set.singleton_add, Set.image_add_left]
        _ ≤ volume (A + B) :=
            measure_mono (Set.add_subset_add (Set.singleton_subset_iff.2 haA) hLB)
    rcases L.eq_empty_or_nonempty with rfl | hLne
    · simp only [measure_empty, add_zero]
      calc volume K = volume (K + {b}) := by simp [Set.add_singleton, Set.image_add_right]
        _ ≤ volume (A + B) :=
            measure_mono (Set.add_subset_add hKA (Set.singleton_subset_iff.2 hbB))
    calc volume K + volume L ≤ volume (K + L) :=
          volume_add_le_volume_add_of_isCompact hKc hLc hKne hLne
      _ ≤ volume (A + B) := measure_mono (Set.add_subset_add hKA hLB)
  haveI : Nonempty {K : Set ℝ // IsCompact K ∧ K ⊆ A} := ⟨⟨∅, isCompact_empty, empty_subset _⟩⟩
  haveI : Nonempty {K : Set ℝ // IsCompact K ∧ K ⊆ B} := ⟨⟨∅, isCompact_empty, empty_subset _⟩⟩
  rw [volume_eq_iSup_isCompact_subtype hA, volume_eq_iSup_isCompact_subtype hB]
  exact ENNReal.iSup_add_iSup_le fun K L => key K L K.2.1 K.2.2 L.2.1 L.2.2

section LevelSets

variable {lam : ℝ} {f g h : ℝ → ℝ}

/-- **Level-set inclusion.** If `f x ^ lam * g y ^ (1 - lam) ≤ h (lam * x + (1 - lam) * y)`
for all `x y`, then for every `t > 0` the Minkowski combination of the level sets of `f`
and `g` at height `t` is contained in the level set of `h` at height `t`. -/
theorem smul_setOf_add_smul_setOf_subset (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hyp : ∀ x y, f x ^ lam * g y ^ (1 - lam) ≤ h (lam * x + (1 - lam) * y))
    {t : ℝ} (ht : 0 < t) :
    lam • {x : ℝ | t ≤ f x} + (1 - lam) • {y : ℝ | t ≤ g y} ⊆ {z : ℝ | t ≤ h z} := by
  rintro z ⟨u, hu, v, hv, rfl⟩
  obtain ⟨x, hx, rfl⟩ := hu
  obtain ⟨y, hy, rfl⟩ := hv
  simp only [Set.mem_setOf_eq, smul_eq_mul] at hx hy ⊢
  have h1 : t ^ lam ≤ f x ^ lam := Real.rpow_le_rpow ht.le hx hlam0
  have h2 : t ^ (1 - lam) ≤ g y ^ (1 - lam) := Real.rpow_le_rpow ht.le hy (by linarith)
  have ht1 : (0 : ℝ) ≤ t ^ lam := Real.rpow_nonneg ht.le _
  have hprod : t ^ lam * t ^ (1 - lam) = t := by
    rw [← Real.rpow_add ht]
    simp
  calc t = t ^ lam * t ^ (1 - lam) := hprod.symm
    _ ≤ f x ^ lam * g y ^ (1 - lam) :=
        mul_le_mul h1 h2 (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg (hf x) _)
    _ ≤ h (lam * x + (1 - lam) * y) := hyp x y

/-- **Level-set measure inequality**: combining the level-set inclusion with the
one-dimensional Brunn–Minkowski inequality and the scaling law for Lebesgue measure. -/
theorem measure_setOf_le_combo (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hyp : ∀ x y, f x ^ lam * g y ^ (1 - lam) ≤ h (lam * x + (1 - lam) * y))
    {t : ℝ} (ht : 0 < t) (hfne : {x : ℝ | t ≤ f x}.Nonempty)
    (hgne : {y : ℝ | t ≤ g y}.Nonempty) :
    ENNReal.ofReal lam * volume {x : ℝ | t ≤ f x}
      + ENNReal.ofReal (1 - lam) * volume {y : ℝ | t ≤ g y} ≤ volume {z : ℝ | t ≤ h z} := by
  have hSm : MeasurableSet {x : ℝ | t ≤ f x} := measurableSet_le measurable_const hfm
  have hTm : MeasurableSet {y : ℝ | t ≤ g y} := measurableSet_le measurable_const hgm
  have hlam1' : (0 : ℝ) < 1 - lam := by linarith
  have hSm' : MeasurableSet (lam • {x : ℝ | t ≤ f x}) := hSm.const_smul_of_ne_zero hlam0.ne'
  have hTm' : MeasurableSet ((1 - lam) • {y : ℝ | t ≤ g y}) := hTm.const_smul_of_ne_zero hlam1'.ne'
  have hSne' : (lam • {x : ℝ | t ≤ f x}).Nonempty := hfne.smul_set
  have hTne' : ((1 - lam) • {y : ℝ | t ≤ g y}).Nonempty := hgne.smul_set
  have hscale : ∀ (c : ℝ), 0 ≤ c → ∀ s : Set ℝ,
      volume (c • s) = ENNReal.ofReal c * volume s := by
    intro c hc s
    rw [Measure.addHaar_smul]
    simp [abs_of_nonneg hc]
  calc ENNReal.ofReal lam * volume {x : ℝ | t ≤ f x}
        + ENNReal.ofReal (1 - lam) * volume {y : ℝ | t ≤ g y}
      = volume (lam • {x : ℝ | t ≤ f x}) + volume ((1 - lam) • {y : ℝ | t ≤ g y}) := by
        rw [hscale lam hlam0.le, hscale (1 - lam) hlam1'.le]
    _ ≤ volume (lam • {x : ℝ | t ≤ f x} + (1 - lam) • {y : ℝ | t ≤ g y}) :=
        volume_add_volume_le_volume_add hSm' hTm' hSne' hTne'
    _ ≤ volume {z : ℝ | t ≤ h z} :=
        measure_mono (smul_setOf_add_smul_setOf_subset hlam0.le hlam1.le hf hg hyp ht)

end LevelSets

section ArithGeom

/-- **Weighted AM–GM for two nonnegative reals**, in the exact shape needed to close
Prékopa–Leindler: the geometric mean `a ^ lam * b ^ (1 - lam)` is bounded by the
arithmetic mean `lam * a + (1 - lam) * b`.  Here `^` is `Real.rpow`. -/
theorem rpow_mul_rpow_le_lin_combo {lam a b : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ lam * b ^ (1 - lam) ≤ lam * a + (1 - lam) * b :=
  Real.geom_mean_le_arith_mean2_weighted hlam0 (by linarith) ha hb (by ring)

end ArithGeom

section Layercake

variable {lam : ℝ} {f g h : ℝ → ℝ}

/-- Nonnegativity of `h` is automatic from the Prékopa–Leindler hypothesis: take `x = y = z`
and use `lam * z + (1 - lam) * z = z`. -/
theorem nonneg_of_prekopa_hyp (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hyp : ∀ x y, f x ^ lam * g y ^ (1 - lam) ≤ h (lam * x + (1 - lam) * y)) (z : ℝ) :
    0 ≤ h z := by
  have hz : lam * z + (1 - lam) * z = z := by ring
  have hzz := hyp z z
  rw [hz] at hzz
  exact le_trans (mul_nonneg (Real.rpow_nonneg (hf z) _) (Real.rpow_nonneg (hg z) _)) hzz

/-- **Step 4: the layer-cake integration.**  Integrating the per-level bound
`measure_setOf_le_combo` over `t ∈ (0, ∞)` and applying the layer cake formula turns it
into an inequality between Lebesgue integrals.

The hypothesis `hsame` says that `f` and `g` have the same set of "attained levels":
for almost every `t > 0`, the level set `{f ≥ t}` is nonempty exactly when `{g ≥ t}` is.
Some such hypothesis is genuinely needed — without it the statement is **false** (take
`f = 0` and `g` the indicator of `[0,1]`, so that `h = 0` is admissible while
`(1 - lam) * ∫ g > 0`).  It holds whenever `f` and `g` have the same supremum, and is
arranged by the usual normalization; see `prekopa_leindler_one_dim_of_bddAbove`. -/
theorem lintegral_combo_le_lintegral (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hfm : Measurable f) (hgm : Measurable g) (hhm : Measurable h)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hyp : ∀ x y, f x ^ lam * g y ^ (1 - lam) ≤ h (lam * x + (1 - lam) * y))
    (hsame : ∀ᵐ t : ℝ, 0 < t → ({x : ℝ | t ≤ f x}.Nonempty ↔ {y : ℝ | t ≤ g y}.Nonempty)) :
    ENNReal.ofReal lam * (∫⁻ x, ENNReal.ofReal (f x))
      + ENNReal.ofReal (1 - lam) * (∫⁻ x, ENNReal.ofReal (g x))
      ≤ ∫⁻ x, ENNReal.ofReal (h x) := by
  have hh : ∀ z, 0 ≤ h z := nonneg_of_prekopa_hyp hf hg hyp
  have hFmble : Measurable fun t : ℝ => volume {x : ℝ | t ≤ f x} :=
    Antitone.measurable fun _ _ hst => measure_mono fun _ hx => le_trans hst hx
  have key : ∀ t : ℝ, 0 < t →
      ({x : ℝ | t ≤ f x}.Nonempty ↔ {y : ℝ | t ≤ g y}.Nonempty) →
      ENNReal.ofReal lam * volume {x : ℝ | t ≤ f x}
        + ENNReal.ofReal (1 - lam) * volume {y : ℝ | t ≤ g y} ≤ volume {z : ℝ | t ≤ h z} := by
    intro t ht hst
    rcases Set.eq_empty_or_nonempty {x : ℝ | t ≤ f x} with he | hne
    · have h1 : ¬ ({x : ℝ | t ≤ f x}).Nonempty := by rw [he]; exact Set.not_nonempty_empty
      have h2 : {y : ℝ | t ≤ g y} = ∅ :=
        Set.not_nonempty_iff_eq_empty.1 fun hc => h1 (hst.2 hc)
      simp [he, h2]
    · exact measure_setOf_le_combo hlam0 hlam1 hfm hgm hf hg hyp ht hne (hst.1 hne)
  have cakeF : ∫⁻ x, ENNReal.ofReal (f x) = ∫⁻ t in Ioi (0 : ℝ), volume {x : ℝ | t ≤ f x} :=
    lintegral_eq_lintegral_meas_le volume (Filter.Eventually.of_forall hf) hfm.aemeasurable
  have cakeG : ∫⁻ x, ENNReal.ofReal (g x) = ∫⁻ t in Ioi (0 : ℝ), volume {y : ℝ | t ≤ g y} :=
    lintegral_eq_lintegral_meas_le volume (Filter.Eventually.of_forall hg) hgm.aemeasurable
  have cakeH : ∫⁻ x, ENNReal.ofReal (h x) = ∫⁻ t in Ioi (0 : ℝ), volume {z : ℝ | t ≤ h z} :=
    lintegral_eq_lintegral_meas_le volume (Filter.Eventually.of_forall hh) hhm.aemeasurable
  rw [cakeF, cakeG, cakeH]
  calc ENNReal.ofReal lam * (∫⁻ t in Ioi (0 : ℝ), volume {x : ℝ | t ≤ f x})
        + ENNReal.ofReal (1 - lam) * (∫⁻ t in Ioi (0 : ℝ), volume {y : ℝ | t ≤ g y})
      = ∫⁻ t in Ioi (0 : ℝ), (ENNReal.ofReal lam * volume {x : ℝ | t ≤ f x}
          + ENNReal.ofReal (1 - lam) * volume {y : ℝ | t ≤ g y}) := by
        rw [lintegral_add_left (hFmble.const_mul _),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), volume {z : ℝ | t ≤ h z} := by
        refine lintegral_mono_ae ?_
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi, ae_restrict_of_ae hsame]
          with t ht hst
        exact key t ht (hst ht)

/-- **Step 4, Bochner form.**  The same inequality as `lintegral_combo_le_lintegral`, stated
for the Bochner integral under integrability hypotheses on `f`, `g` and `h`. -/
theorem integral_combo_le_integral (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hfm : Measurable f) (hgm : Measurable g) (hhm : Measurable h)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfi : Integrable f) (hgi : Integrable g) (hhi : Integrable h)
    (hyp : ∀ x y, f x ^ lam * g y ^ (1 - lam) ≤ h (lam * x + (1 - lam) * y))
    (hsame : ∀ᵐ t : ℝ, 0 < t → ({x : ℝ | t ≤ f x}.Nonempty ↔ {y : ℝ | t ≤ g y}.Nonempty)) :
    lam * (∫ x, f x) + (1 - lam) * (∫ x, g x) ≤ ∫ x, h x := by
  have hh : ∀ z, 0 ≤ h z := nonneg_of_prekopa_hyp hf hg hyp
  have hA : (∫⁻ x, ENNReal.ofReal (f x)) ≠ ⊤ :=
    ((hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hf)).1 hfi.2).ne
  have hB : (∫⁻ x, ENNReal.ofReal (g x)) ≠ ⊤ :=
    ((hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hg)).1 hgi.2).ne
  have hC : (∫⁻ x, ENNReal.ofReal (h x)) ≠ ⊤ :=
    ((hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hh)).1 hhi.2).ne
  have hmono := ENNReal.toReal_mono hC
    (lintegral_combo_le_lintegral hlam0 hlam1 hfm hgm hhm hf hg hyp hsame)
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hlam0.le,
      ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 1 - lam)] at hmono
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf)
        hfm.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg)
        hgm.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hh)
        hhm.aestronglyMeasurable]
  exact hmono

/-- **One-dimensional Prékopa–Leindler inequality.**

Let `lam ∈ (0,1)` and let `f g h : ℝ → ℝ` be measurable, nonnegative and integrable with
`f x ^ lam * g y ^ (1 - lam) ≤ h (lam * x + (1 - lam) * y)` for all `x y` (`^` is `Real.rpow`).
Assume moreover that `f` and `g` attain the same levels (`hsame`); this is the usual
normalization `sSup (range f) = sSup (range g)`, and some such hypothesis is necessary — see
the docstring of `lintegral_combo_le_lintegral` for a counterexample without it.

Then `(∫ f) ^ lam * (∫ g) ^ (1 - lam) ≤ ∫ h`. -/
theorem prekopa_leindler_one_dim_of_same_levels (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hfm : Measurable f) (hgm : Measurable g) (hhm : Measurable h)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfi : Integrable f) (hgi : Integrable g) (hhi : Integrable h)
    (hyp : ∀ x y, f x ^ lam * g y ^ (1 - lam) ≤ h (lam * x + (1 - lam) * y))
    (hsame : ∀ᵐ t : ℝ, 0 < t → ({x : ℝ | t ≤ f x}.Nonempty ↔ {y : ℝ | t ≤ g y}.Nonempty)) :
    (∫ x, f x) ^ lam * (∫ x, g x) ^ (1 - lam) ≤ ∫ x, h x :=
  le_trans
    (rpow_mul_rpow_le_lin_combo hlam0.le hlam1.le (integral_nonneg hf) (integral_nonneg hg))
    (integral_combo_le_integral hlam0 hlam1 hfm hgm hhm hf hg hfi hgi hhi hyp hsame)

/-- Characterization of the (nonempty) level sets of a normalized function `F / P`, where
`P` is the least upper bound of `F`: for `t ≠ 1` the set `{F / P ≥ t}` is nonempty exactly
when `t < 1`.  The value `t = 1` is genuinely exceptional (it depends on whether the
supremum is attained), which is why `lintegral_combo_le_lintegral` only asks for its
hypothesis almost everywhere. -/
theorem nonempty_setOf_le_div_iff {F : ℝ → ℝ} {P : ℝ} (hP : 0 < P) (hub : ∀ x, F x ≤ P)
    (hlub : ∀ s : ℝ, s < P → ∃ x, s < F x) {t : ℝ} (ht1 : t ≠ 1) :
    {x : ℝ | t ≤ F x / P}.Nonempty ↔ t < 1 := by
  constructor
  · rintro ⟨x, hx⟩
    simp only [Set.mem_setOf_eq, le_div_iff₀ hP] at hx
    have h1 : t * P ≤ P := le_trans hx (hub x)
    have h2 : t ≤ 1 := by nlinarith
    exact lt_of_le_of_ne h2 ht1
  · intro ht
    obtain ⟨x, hx⟩ := hlub (t * P) (by nlinarith)
    exact ⟨x, by simpa only [Set.mem_setOf_eq, le_div_iff₀ hP] using hx.le⟩

/-- **One-dimensional Prékopa–Leindler inequality, normalized form.**  Here `M` and `N` are
least upper bounds for `f` and `g` respectively (`hfM`/`hfM'` and `hgN`/`hgN'`).  No
"same supremum" hypothesis is needed: it is arranged by rescaling `f`, `g` and `h`. -/
theorem prekopa_leindler_one_dim_of_lub (hlam0 : 0 < lam) (hlam1 : lam < 1)
    {M N : ℝ} (hM : 0 < M) (hN : 0 < N)
    (hfM : ∀ x, f x ≤ M) (hgN : ∀ y, g y ≤ N)
    (hfM' : ∀ s : ℝ, s < M → ∃ x, s < f x) (hgN' : ∀ s : ℝ, s < N → ∃ y, s < g y)
    (hfm : Measurable f) (hgm : Measurable g) (hhm : Measurable h)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfi : Integrable f) (hgi : Integrable g) (hhi : Integrable h)
    (hyp : ∀ x y, f x ^ lam * g y ^ (1 - lam) ≤ h (lam * x + (1 - lam) * y)) :
    (∫ x, f x) ^ lam * (∫ x, g x) ^ (1 - lam) ≤ ∫ x, h x := by
  have hKpos : (0 : ℝ) < M ^ lam * N ^ (1 - lam) :=
    mul_pos (Real.rpow_pos_of_pos hM _) (Real.rpow_pos_of_pos hN _)
  have hyp' : ∀ x y, (f x / M) ^ lam * (g y / N) ^ (1 - lam)
      ≤ h (lam * x + (1 - lam) * y) / (M ^ lam * N ^ (1 - lam)) := by
    intro x y
    rw [Real.div_rpow (hf x) hM.le, Real.div_rpow (hg y) hN.le, div_mul_div_comm]
    gcongr
    exact hyp x y
  have hne1 : ∀ᵐ t : ℝ, t ≠ 1 := by
    rw [MeasureTheory.ae_iff]
    simp
  have hsame' : ∀ᵐ t : ℝ, 0 < t →
      ({x : ℝ | t ≤ f x / M}.Nonempty ↔ {y : ℝ | t ≤ g y / N}.Nonempty) := by
    filter_upwards [hne1] with t ht1 _
    rw [nonempty_setOf_le_div_iff hM hfM hfM' ht1, nonempty_setOf_le_div_iff hN hgN hgN' ht1]
  have main := prekopa_leindler_one_dim_of_same_levels (f := fun x => f x / M) (g := fun y => g y / N)
    (h := fun z => h z / (M ^ lam * N ^ (1 - lam))) hlam0 hlam1
    (hfm.div_const M) (hgm.div_const N) (hhm.div_const _)
    (fun x => div_nonneg (hf x) hM.le) (fun y => div_nonneg (hg y) hN.le)
    (hfi.div_const M) (hgi.div_const N) (hhi.div_const _) hyp' hsame'
  have eL : ((∫ x, f x) / M) ^ lam * ((∫ x, g x) / N) ^ (1 - lam)
      = (∫ x, f x) ^ lam * (∫ x, g x) ^ (1 - lam) / (M ^ lam * N ^ (1 - lam)) := by
    rw [Real.div_rpow (integral_nonneg hf) hM.le, Real.div_rpow (integral_nonneg hg) hN.le,
      div_mul_div_comm]
  rw [integral_div, integral_div, integral_div, eL] at main
  have hmul := mul_le_mul_of_nonneg_right main hKpos.le
  rwa [div_mul_cancel₀ _ hKpos.ne', div_mul_cancel₀ _ hKpos.ne'] at hmul

/-- **One-dimensional Prékopa–Leindler inequality** for bounded `f` and `g`.

Let `lam ∈ (0,1)` and let `f g h : ℝ → ℝ` be measurable, nonnegative and integrable, with
`f` and `g` bounded above, satisfying
`f x ^ lam * g y ^ (1 - lam) ≤ h (lam * x + (1 - lam) * y)` for all `x y` (`^` is
`Real.rpow`).  Then `(∫ f) ^ lam * (∫ g) ^ (1 - lam) ≤ ∫ h`. -/
theorem prekopa_leindler_one_dim_of_bddAbove (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hfm : Measurable f) (hgm : Measurable g) (hhm : Measurable h)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfi : Integrable f) (hgi : Integrable g) (hhi : Integrable h)
    (hyp : ∀ x y, f x ^ lam * g y ^ (1 - lam) ≤ h (lam * x + (1 - lam) * y))
    (hfb : BddAbove (Set.range f)) (hgb : BddAbove (Set.range g)) :
    (∫ x, f x) ^ lam * (∫ x, g x) ^ (1 - lam) ≤ ∫ x, h x := by
  have hh : ∀ z, 0 ≤ h z := nonneg_of_prekopa_hyp hf hg hyp
  by_cases hfz : ∀ x, f x = 0
  · have hI : (∫ x, f x) = 0 := by simp [hfz]
    rw [hI, Real.zero_rpow hlam0.ne', zero_mul]
    exact integral_nonneg hh
  by_cases hgz : ∀ y, g y = 0
  · have hI : (∫ x, g x) = 0 := by simp [hgz]
    rw [hI, Real.zero_rpow (by linarith : (1 : ℝ) - lam ≠ 0), mul_zero]
    exact integral_nonneg hh
  obtain ⟨x₀, hx₀⟩ := not_forall.1 hfz
  obtain ⟨y₀, hy₀⟩ := not_forall.1 hgz
  have hfM : ∀ x, f x ≤ sSup (Set.range f) := fun x => le_csSup hfb (Set.mem_range_self x)
  have hgN : ∀ y, g y ≤ sSup (Set.range g) := fun y => le_csSup hgb (Set.mem_range_self y)
  have hM : 0 < sSup (Set.range f) :=
    lt_of_lt_of_le (lt_of_le_of_ne (hf x₀) (Ne.symm hx₀)) (hfM x₀)
  have hN : 0 < sSup (Set.range g) :=
    lt_of_lt_of_le (lt_of_le_of_ne (hg y₀) (Ne.symm hy₀)) (hgN y₀)
  have hfM' : ∀ s : ℝ, s < sSup (Set.range f) → ∃ x, s < f x := by
    intro s hs
    obtain ⟨a, ⟨x, rfl⟩, has⟩ := exists_lt_of_lt_csSup ⟨f x₀, Set.mem_range_self x₀⟩ hs
    exact ⟨x, has⟩
  have hgN' : ∀ s : ℝ, s < sSup (Set.range g) → ∃ y, s < g y := by
    intro s hs
    obtain ⟨a, ⟨y, rfl⟩, has⟩ := exists_lt_of_lt_csSup ⟨g y₀, Set.mem_range_self y₀⟩ hs
    exact ⟨y, has⟩
  exact prekopa_leindler_one_dim_of_lub hlam0 hlam1 hM hN hfM hgN hfM' hgN'
    hfm hgm hhm hf hg hfi hgi hhi hyp

/-- Truncating a nonnegative integrable function at height `n` and letting `n → ∞`
recovers its integral (dominated convergence, with the function itself as the bound). -/
theorem tendsto_integral_min_natCast {F : ℝ → ℝ} (hFm : Measurable F) (hF : ∀ x, 0 ≤ F x)
    (hFi : Integrable F) :
    Filter.Tendsto (fun n : ℕ => ∫ x, min (F x) (n : ℝ)) Filter.atTop (nhds (∫ x, F x)) := by
  refine tendsto_integral_of_dominated_convergence F
    (fun n => (hFm.min measurable_const).aestronglyMeasurable) hFi (fun n => ?_) ?_
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hF x) (Nat.cast_nonneg n))]
    exact min_le_left _ _
  · filter_upwards with x
    obtain ⟨N, hN⟩ := exists_nat_ge (F x)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    exact (min_eq_left (le_trans hN (Nat.cast_le.2 hn))).symm

/-- **One-dimensional Prékopa–Leindler inequality.**

Let `lam ∈ (0,1)` and let `f g h : ℝ → ℝ` be measurable, nonnegative and integrable with
`f x ^ lam * g y ^ (1 - lam) ≤ h (lam * x + (1 - lam) * y)` for all `x y`, where `^` is
`Real.rpow`.  Then
`(∫ x, f x) ^ lam * (∫ x, g x) ^ (1 - lam) ≤ ∫ x, h x`.

This is the base case of the induction that produces Prékopa–Leindler on `ℝⁿ`. -/
theorem prekopa_leindler_one_dim (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hfm : Measurable f) (hgm : Measurable g) (hhm : Measurable h)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfi : Integrable f) (hgi : Integrable g) (hhi : Integrable h)
    (hyp : ∀ x y, f x ^ lam * g y ^ (1 - lam) ≤ h (lam * x + (1 - lam) * y)) :
    (∫ x, f x) ^ lam * (∫ x, g x) ^ (1 - lam) ≤ ∫ x, h x := by
  have hbdd : ∀ (F : ℝ → ℝ) (n : ℕ), BddAbove (Set.range fun x => min (F x) (n : ℝ)) :=
    fun F n => ⟨(n : ℝ), by rintro _ ⟨x, rfl⟩; exact min_le_right _ _⟩
  have hint : ∀ (F : ℝ → ℝ), Measurable F → (∀ x, 0 ≤ F x) → Integrable F → ∀ n : ℕ,
      Integrable fun x => min (F x) (n : ℝ) := by
    intro F hFm hF hFi n
    refine hFi.mono (hFm.min measurable_const).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_min (hF x) (Nat.cast_nonneg n)),
      abs_of_nonneg (hF x)]
    exact min_le_left _ _
  have step : ∀ n : ℕ,
      (∫ x, min (f x) (n : ℝ)) ^ lam * (∫ x, min (g x) (n : ℝ)) ^ (1 - lam) ≤ ∫ x, h x := by
    intro n
    have hfn : ∀ x, 0 ≤ min (f x) (n : ℝ) := fun x => le_min (hf x) (Nat.cast_nonneg n)
    have hgn : ∀ y, 0 ≤ min (g y) (n : ℝ) := fun y => le_min (hg y) (Nat.cast_nonneg n)
    refine prekopa_leindler_one_dim_of_bddAbove hlam0 hlam1
      (hfm.min measurable_const) (hgm.min measurable_const) hhm hfn hgn
      (hint f hfm hf hfi n) (hint g hgm hg hgi n) hhi ?_ (hbdd f n) (hbdd g n)
    intro x y
    refine le_trans (mul_le_mul
      (Real.rpow_le_rpow (hfn x) (min_le_left _ _) hlam0.le)
      (Real.rpow_le_rpow (hgn y) (min_le_left _ _) (by linarith))
      (Real.rpow_nonneg (hgn y) _) (Real.rpow_nonneg (hf x) _)) (hyp x y)
  exact le_of_tendsto
    (((tendsto_integral_min_natCast hfm hf hfi).rpow_const (Or.inr hlam0.le)).mul
      ((tendsto_integral_min_natCast hgm hg hgi).rpow_const (Or.inr (by linarith))))
    (Filter.Eventually.of_forall step)

end Layercake

end Arlib
