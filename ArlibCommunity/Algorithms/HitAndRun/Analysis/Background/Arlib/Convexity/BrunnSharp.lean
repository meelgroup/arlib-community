/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.PrekopaLeindlerN

/-!
# The sharp (`1/n`-concave) Brunn–Minkowski inequality, and Brunn's theorem

`Arlib.brunn_minkowski_pi` (in `Arlib.Convexity.PrekopaLeindlerN`) is the *multiplicative*
Brunn–Minkowski inequality
`volume A ^ lam * volume B ^ (1 - lam) ≤ volume (lam • A + (1 - lam) • B)`.
This file upgrades it to the **sharp**, `1/n`-concave form

`lam * volume A ^ (1/n) + (1 - lam) * volume B ^ (1/n) ≤ volume (lam • A + (1-lam) • B) ^ (1/n)`

(`Arlib.brunn_minkowski_sharp`), and deduces **Brunn's theorem** in sharp form: for a convex
`K ⊆ ℝ^(m+1)` the function `t ↦ volume (slice K t) ^ (1/m)` is concave along the first
coordinate (`Arlib.brunn_slice_sharp`, `Arlib.brunn_slice_concaveOn`).

Mathlib (v4.32) has no Brunn–Minkowski inequality in any form.

## Statement conventions

Everything is stated in `ℝ≥0∞`, with `^` denoting `ENNReal.rpow`.  This is deliberate:
`volume` is `ℝ≥0∞`-valued and `⊤` genuinely occurs (unbounded `A`), while
`ENNReal.toReal ⊤ = 0` would silently turn a true statement into a false one.  In `ℝ≥0∞` the
sharp inequality needs **no finiteness hypothesis at all** — `⊤ ^ (1/n) = ⊤` for `n ≠ 0`, and
both sides behave correctly.  A real-valued restatement,
`Arlib.brunn_minkowski_sharp_toReal`, is provided with the finiteness hypotheses spelled out.

## Hypotheses, and why each is needed

* `n ≠ 0`.  For `n = 0` the exponent `1/n` is `1/0 = 0` and `x ^ (0:ℝ) = 1`, so the claim would
  read `lam + (1 - lam) ≤ 1` … which is fine, but every intermediate step (`(x ^ n) ^ (1/n) = x`)
  breaks; we simply exclude it.
* `A.Nonempty`, `B.Nonempty`.  **These are not removable.**  With `A = ∅`, `B` the unit cube
  and `lam = 1/2`, the Minkowski sum `lam • A + (1 - lam) • B` is empty, so the right-hand side
  is `0` while the left-hand side is `1/2`.  (The *multiplicative* form has no such problem,
  since `volume ∅ ^ lam = 0` kills its left-hand side; this is exactly the place where the
  sharp form is strictly stronger and strictly more delicate.)
* Measurability of `A` and `B`.  The Minkowski sum itself need **not** be measurable; as in
  `Arlib.brunn_minkowski_pi`, `volume` on the right-hand side is used as an outer measure.

## Proof

The classical AM–GM normalisation.  Write `a = volume A ^ (1/n)`, `b = volume B ^ (1/n)`
(finite and positive after the degenerate cases are dispatched), and normalise
`A' = a⁻¹ • A`, `B' = b⁻¹ • B`, so that `volume A' = volume B' = 1` by homogeneity
(`Measure.addHaar_smul`).  With `s = lam * a`, `t = (1 - lam) * b` and `θ = s / (s + t)`,
`lam • A + (1 - lam) • B = (s + t) • (θ • A' + (1 - θ) • B')`,
and the multiplicative inequality applied to `A'`, `B'` with weight `θ` gives
`1 = volume A' ^ θ * volume B' ^ (1 - θ) ≤ volume (θ • A' + (1 - θ) • B')`.
Homogeneity again turns this into `(s + t) ^ n ≤ volume (lam • A + (1 - lam) • B)`.

Degenerate cases (`lam ∈ {0, 1}`, `volume A = 0`, `volume B = 0`, `volume A = ⊤`,
`volume B = ⊤`) are all handled by the one-sided translation bounds
`Arlib.ofReal_mul_volume_rpow_le` / `Arlib.ofReal_one_sub_mul_volume_rpow_le`, which say that
`lam • A + (1 - lam) • B` contains a translate of `lam • A` (resp. of `(1 - lam) • B`).
-/

open MeasureTheory Set Pointwise
open scoped ENNReal

namespace Arlib

/-! ### Homogeneity and translation invariance of Lebesgue measure on `Fin n → ℝ` -/

section Homogeneity

variable {n : ℕ}

/-- Lebesgue measure on `Fin n → ℝ` is `n`-homogeneous: `volume (c • A) = |c ^ n| * volume A`. -/
lemma volume_smul_set (c : ℝ) (A : Set (Fin n → ℝ)) :
    volume (c • A) = ENNReal.ofReal |c ^ n| * volume A := by
  rw [Measure.addHaar_smul, Module.finrank_fin_fun]

/-- Homogeneity of Lebesgue measure, for a nonnegative scaling factor. -/
lemma volume_smul_set_of_nonneg {c : ℝ} (hc : 0 ≤ c) (A : Set (Fin n → ℝ)) :
    volume (c • A) = ENNReal.ofReal (c ^ n) * volume A := by
  rw [volume_smul_set, abs_of_nonneg (pow_nonneg hc n)]

/-- Translation invariance, in Minkowski-sum form. -/
lemma volume_singleton_add (v : Fin n → ℝ) (A : Set (Fin n → ℝ)) :
    volume ({v} + A) = volume A := by
  rw [Set.singleton_add, Set.image_add_left, measure_preimage_add]

end Homogeneity

/-! ### Two arithmetic helpers -/

/-- `(x ^ n) ^ (1/n) = x` for `x ≥ 0`, `n ≠ 0` (inner `^` is monoid power, outer is `rpow`). -/
private lemma real_pow_rpow_inv {n : ℕ} {x : ℝ} (hx : 0 ≤ x) (hn : n ≠ 0) :
    (x ^ n) ^ ((n : ℝ)⁻¹) = x := by
  rw [← Real.rpow_natCast x n, ← Real.rpow_mul hx,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn), Real.rpow_one]

/-- Extraction of a positive real `n`-th root of a finite nonzero element of `ℝ≥0∞`. -/
private lemma exists_pos_root {n : ℕ} (hn : n ≠ 0) {v : ℝ≥0∞} (h0 : v ≠ 0) (htop : v ≠ ⊤) :
    ∃ a : ℝ, 0 < a ∧ v ^ ((n : ℝ)⁻¹) = ENNReal.ofReal a ∧ ENNReal.ofReal (a ^ n) = v := by
  have hnn : (0 : ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
  refine ⟨v.toReal ^ ((n : ℝ)⁻¹), Real.rpow_pos_of_pos (ENNReal.toReal_pos h0 htop) _, ?_, ?_⟩
  · rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hnn, ENNReal.ofReal_toReal htop]
  · rw [Real.rpow_inv_natCast_pow ENNReal.toReal_nonneg hn, ENNReal.ofReal_toReal htop]

/-! ### The one-sided (translation) bounds

These carry all the degenerate cases, and are of independent interest: they say that the
Minkowski combination contains a translate of each scaled piece. -/

/-- `lam • A + (1 - lam) • B` contains a translate of `lam • A`, hence
`lam * volume A ^ (1/n) ≤ volume (lam • A + (1 - lam) • B) ^ (1/n)`.  Needs `B` nonempty. -/
lemma ofReal_mul_volume_rpow_le {n : ℕ} (hn : n ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    {A B : Set (Fin n → ℝ)} (hB : B.Nonempty) :
    ENNReal.ofReal lam * volume A ^ ((n : ℝ)⁻¹)
      ≤ volume (lam • A + (1 - lam) • B) ^ ((n : ℝ)⁻¹) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hninv : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hnR
  obtain ⟨b, hb⟩ := hB
  have hsub : lam • A + ({(1 - lam) • b} : Set (Fin n → ℝ)) ⊆ lam • A + (1 - lam) • B :=
    add_subset_add_left (Set.singleton_subset_iff.mpr (Set.smul_mem_smul_set hb))
  have hvol : ENNReal.ofReal (lam ^ n) * volume A ≤ volume (lam • A + (1 - lam) • B) := by
    calc ENNReal.ofReal (lam ^ n) * volume A
        = volume (lam • A) := (volume_smul_set_of_nonneg hlam A).symm
      _ = volume (lam • A + ({(1 - lam) • b} : Set (Fin n → ℝ))) := by
          rw [add_comm, volume_singleton_add]
      _ ≤ _ := measure_mono hsub
  calc ENNReal.ofReal lam * volume A ^ ((n : ℝ)⁻¹)
      = (ENNReal.ofReal (lam ^ n) * volume A) ^ ((n : ℝ)⁻¹) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hninv.le,
          ENNReal.ofReal_rpow_of_nonneg (pow_nonneg hlam n) hninv.le,
          real_pow_rpow_inv hlam hn]
    _ ≤ _ := ENNReal.rpow_le_rpow hvol hninv.le

/-- `lam • A + (1 - lam) • B` contains a translate of `(1 - lam) • B`, hence
`(1 - lam) * volume B ^ (1/n) ≤ volume (lam • A + (1 - lam) • B) ^ (1/n)`.  Needs `A` nonempty. -/
lemma ofReal_one_sub_mul_volume_rpow_le {n : ℕ} (hn : n ≠ 0) {lam : ℝ} (hlam : lam ≤ 1)
    {A B : Set (Fin n → ℝ)} (hA : A.Nonempty) :
    ENNReal.ofReal (1 - lam) * volume B ^ ((n : ℝ)⁻¹)
      ≤ volume (lam • A + (1 - lam) • B) ^ ((n : ℝ)⁻¹) := by
  have h := ofReal_mul_volume_rpow_le hn (by linarith : (0 : ℝ) ≤ 1 - lam) (A := B) (B := A) hA
  rwa [show (1 : ℝ) - (1 - lam) = lam by ring, add_comm] at h

/-! ### The sharp Brunn–Minkowski inequality -/

/-- **The sharp (`1/n`-concave) Brunn–Minkowski inequality**, with the exponent written as
`(n : ℝ)⁻¹`.  See `Arlib.brunn_minkowski_sharp` for the `1/n` form. -/
theorem brunn_minkowski_sharp_inv {n : ℕ} (hn : n ≠ 0) {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    {A B : Set (Fin n → ℝ)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
    ENNReal.ofReal lam * volume A ^ ((n : ℝ)⁻¹)
        + ENNReal.ofReal (1 - lam) * volume B ^ ((n : ℝ)⁻¹)
      ≤ volume (lam • A + (1 - lam) • B) ^ ((n : ℝ)⁻¹) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hninv : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hnR
  -- `lam = 0`
  rcases eq_or_lt_of_le hlam0 with hl0 | hl0
  · subst hl0
    rw [zero_smul_set hAne]
    simp
  -- `lam = 1`
  rcases eq_or_lt_of_le hlam1 with hl1 | hl1
  · subst hl1
    rw [show (1 : ℝ) - 1 = 0 by ring, zero_smul_set hBne]
    simp
  -- `volume A = 0`
  by_cases hA0 : volume A = 0
  · have hz : ENNReal.ofReal lam * volume A ^ ((n : ℝ)⁻¹) = 0 := by
      rw [hA0, ENNReal.zero_rpow_of_pos hninv, mul_zero]
    rw [hz, zero_add]
    exact ofReal_one_sub_mul_volume_rpow_le hn hlam1 hAne
  -- `volume B = 0`
  by_cases hB0 : volume B = 0
  · have hz : ENNReal.ofReal (1 - lam) * volume B ^ ((n : ℝ)⁻¹) = 0 := by
      rw [hB0, ENNReal.zero_rpow_of_pos hninv, mul_zero]
    rw [hz, add_zero]
    exact ofReal_mul_volume_rpow_le hn hlam0 hBne
  -- `volume A = ⊤`
  by_cases hAtop : volume A = ⊤
  · have hle := ofReal_mul_volume_rpow_le hn hlam0 (A := A) hBne
    rw [hAtop, ENNReal.top_rpow_of_pos hninv,
      ENNReal.mul_top (ENNReal.ofReal_pos.mpr hl0).ne', top_le_iff] at hle
    rw [hle]
    exact le_top
  -- `volume B = ⊤`
  by_cases hBtop : volume B = ⊤
  · have hle := ofReal_one_sub_mul_volume_rpow_le hn hlam1 (B := B) hAne
    rw [hBtop, ENNReal.top_rpow_of_pos hninv,
      ENNReal.mul_top (ENNReal.ofReal_pos.mpr (by linarith : (0 : ℝ) < 1 - lam)).ne',
      top_le_iff] at hle
    rw [hle]
    exact le_top
  -- the main case: `0 < lam < 1` and both volumes finite and nonzero
  obtain ⟨a, ha_pos, ha_vol, ha_pow⟩ := exists_pos_root hn hA0 hAtop
  obtain ⟨b, hb_pos, hb_vol, hb_pow⟩ := exists_pos_root hn hB0 hBtop
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have hb_ne : b ≠ 0 := ne_of_gt hb_pos
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = lam * a := ⟨_, rfl⟩
  obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = (1 - lam) * b := ⟨_, rfl⟩
  have hs_pos : 0 < s := by rw [hs_def]; exact mul_pos hl0 ha_pos
  have ht_pos : 0 < t := by rw [ht_def]; exact mul_pos (by linarith) hb_pos
  have hst_pos : 0 < s + t := by linarith
  have hst_ne : s + t ≠ 0 := ne_of_gt hst_pos
  obtain ⟨th, hth_def⟩ : ∃ th : ℝ, th = s / (s + t) := ⟨_, rfl⟩
  have hth0 : 0 < th := by rw [hth_def]; exact div_pos hs_pos hst_pos
  have hth1 : th < 1 := by rw [hth_def, div_lt_one hst_pos]; linarith
  -- the normalised bodies have volume `1`
  have hA'vol : volume (a⁻¹ • A) = 1 := by
    rw [volume_smul_set_of_nonneg (inv_nonneg.mpr ha_pos.le) A, ← ha_pow,
      ← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr ha_pos.le) n), inv_pow,
      inv_mul_cancel₀ (pow_ne_zero n ha_ne), ENNReal.ofReal_one]
  have hB'vol : volume (b⁻¹ • B) = 1 := by
    rw [volume_smul_set_of_nonneg (inv_nonneg.mpr hb_pos.le) B, ← hb_pow,
      ← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr hb_pos.le) n), inv_pow,
      inv_mul_cancel₀ (pow_ne_zero n hb_ne), ENNReal.ofReal_one]
  -- the multiplicative inequality on the normalised bodies
  have hmul := brunn_minkowski_pi hth0 hth1 (hA.const_smul₀ a⁻¹) (hB.const_smul₀ b⁻¹)
  rw [hA'vol, hB'vol, ENNReal.one_rpow, ENNReal.one_rpow, one_mul] at hmul
  -- the rescaling identity
  have hsa : s * a⁻¹ = lam := by rw [hs_def]; field_simp
  have htb : t * b⁻¹ = 1 - lam := by rw [ht_def]; field_simp
  have h1 : (s + t) * th = s := by rw [hth_def]; field_simp
  have h2 : (s + t) * (1 - th) = t := by rw [hth_def]; field_simp; ring
  have key1 : (s + t) * (th * a⁻¹) = lam := by rw [← mul_assoc, h1, hsa]
  have key2 : (s + t) * ((1 - th) * b⁻¹) = 1 - lam := by rw [← mul_assoc, h2, htb]
  have hCeq : (s + t) • (th • (a⁻¹ • A) + (1 - th) • (b⁻¹ • B)) = lam • A + (1 - lam) • B := by
    simp only [smul_add, smul_smul, key1, key2]
  -- homogeneity turns the multiplicative bound into the sharp one
  have hCvol : ENNReal.ofReal ((s + t) ^ n) ≤ volume (lam • A + (1 - lam) • B) := by
    rw [← hCeq, volume_smul_set_of_nonneg hst_pos.le]
    calc ENNReal.ofReal ((s + t) ^ n)
        = ENNReal.ofReal ((s + t) ^ n) * 1 := (mul_one _).symm
      _ ≤ ENNReal.ofReal ((s + t) ^ n) * volume (th • (a⁻¹ • A) + (1 - th) • (b⁻¹ • B)) :=
          mul_le_mul' le_rfl hmul
  have hfinal : ENNReal.ofReal (s + t) ≤ volume (lam • A + (1 - lam) • B) ^ ((n : ℝ)⁻¹) := by
    have h := ENNReal.rpow_le_rpow hCvol hninv.le
    rwa [ENNReal.ofReal_rpow_of_nonneg (pow_nonneg hst_pos.le n) hninv.le,
      real_pow_rpow_inv hst_pos.le hn] at h
  refine le_trans (le_of_eq ?_) hfinal
  rw [ha_vol, hb_vol, ← ENNReal.ofReal_mul hlam0,
    ← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 1 - lam),
    ← ENNReal.ofReal_add (mul_nonneg hlam0 ha_pos.le)
      (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - lam) hb_pos.le),
    hs_def, ht_def]

/-- **The sharp (`1/n`-concave) Brunn–Minkowski inequality in `ℝⁿ`.**

For `lam ∈ [0,1]` and *nonempty measurable* `A B : Set (Fin n → ℝ)` with `n ≠ 0`,
`lam * volume A ^ (1/n) + (1 - lam) * volume B ^ (1/n) ≤ volume (lam • A + (1-lam) • B) ^ (1/n)`
in `ℝ≥0∞` (`^` is `ENNReal.rpow`).

No finiteness hypothesis is needed: the statement is correct in `ℝ≥0∞` even when a volume is
`⊤`.  Nonemptiness of `A` and `B` **is** needed — see the module docstring.

As in `Arlib.brunn_minkowski_pi`, the Minkowski sum need not be measurable and `volume` is
being used as an outer measure on the right. -/
theorem brunn_minkowski_sharp {n : ℕ} (hn : n ≠ 0) {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    {A B : Set (Fin n → ℝ)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
    ENNReal.ofReal lam * volume A ^ (1 / (n : ℝ))
        + ENNReal.ofReal (1 - lam) * volume B ^ (1 / (n : ℝ))
      ≤ volume (lam • A + (1 - lam) • B) ^ (1 / (n : ℝ)) := by
  simpa only [one_div] using brunn_minkowski_sharp_inv hn hlam0 hlam1 hA hB hAne hBne

/-- The sharp Brunn–Minkowski inequality with the exponent written as `1 / finrank`. -/
theorem brunn_minkowski_sharp_finrank {n : ℕ} (hn : n ≠ 0) {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    {A B : Set (Fin n → ℝ)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
    ENNReal.ofReal lam * volume A ^ (1 / (Module.finrank ℝ (Fin n → ℝ) : ℝ))
        + ENNReal.ofReal (1 - lam) * volume B ^ (1 / (Module.finrank ℝ (Fin n → ℝ) : ℝ))
      ≤ volume (lam • A + (1 - lam) • B) ^ (1 / (Module.finrank ℝ (Fin n → ℝ) : ℝ)) := by
  simpa only [Module.finrank_fin_fun] using
    brunn_minkowski_sharp hn hlam0 hlam1 hA hB hAne hBne

/-- **The sharp Brunn–Minkowski inequality, real-valued form.**

Every finiteness hypothesis is stated explicitly, rather than being hidden inside
`ENNReal.toReal` (which sends `⊤` to `0` and would silently make the statement false):
`hAfin`, `hBfin` for the two bodies, and `hCfin` for the Minkowski combination.  Prefer the
`ℝ≥0∞`-valued `Arlib.brunn_minkowski_sharp`, which needs none of them. -/
theorem brunn_minkowski_sharp_toReal {n : ℕ} (hn : n ≠ 0) {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    {A B : Set (Fin n → ℝ)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAfin : volume A ≠ ⊤) (hBfin : volume B ≠ ⊤)
    (hCfin : volume (lam • A + (1 - lam) • B) ≠ ⊤) :
    lam * (volume A).toReal ^ (1 / (n : ℝ)) + (1 - lam) * (volume B).toReal ^ (1 / (n : ℝ))
      ≤ (volume (lam • A + (1 - lam) • B)).toReal ^ (1 / (n : ℝ)) := by
  have hninv : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  have hxne : ENNReal.ofReal lam * volume A ^ (1 / (n : ℝ)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg hninv hAfin)
  have hyne : ENNReal.ofReal (1 - lam) * volume B ^ (1 / (n : ℝ)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg hninv hBfin)
  have h := ENNReal.toReal_mono (ENNReal.rpow_ne_top_of_nonneg hninv hCfin)
    (brunn_minkowski_sharp hn hlam0 hlam1 hA hB hAne hBne)
  rwa [ENNReal.toReal_add hxne hyne, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hlam0, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 1 - lam),
    ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at h

/-! ### Brunn's theorem: sections of a convex body -/

section Brunn

variable {m : ℕ}

/-- The slice of `K ⊆ ℝ^(m+1)` at first coordinate `t`, viewed as a subset of `ℝ^m`. -/
def slice (K : Set (Fin (m + 1) → ℝ)) (t : ℝ) : Set (Fin m → ℝ) :=
  {y | (Fin.cons t y : Fin (m + 1) → ℝ) ∈ K}

@[simp] lemma mem_slice {K : Set (Fin (m + 1) → ℝ)} {t : ℝ} {y : Fin m → ℝ} :
    y ∈ slice K t ↔ (Fin.cons t y : Fin (m + 1) → ℝ) ∈ K := Iff.rfl

lemma measurableSet_slice {K : Set (Fin (m + 1) → ℝ)} (hK : MeasurableSet K) (t : ℝ) :
    MeasurableSet (slice K t) := by
  have hmeas : Measurable (fun y : Fin m → ℝ => (Fin.cons t y : Fin (m + 1) → ℝ)) := by fun_prop
  exact hmeas hK

/-- Convexity of `K` makes its slices *Minkowski-superadditive* along the first coordinate. -/
lemma smul_add_slice_subset {K : Set (Fin (m + 1) → ℝ)} (hK : Convex ℝ K)
    {lam t₁ t₂ : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    lam • slice K t₁ + (1 - lam) • slice K t₂ ⊆ slice K (lam * t₁ + (1 - lam) * t₂) := by
  intro z hz
  simp only [Set.mem_add, Set.mem_smul_set] at hz
  obtain ⟨u, ⟨y₁, hy₁, rfl⟩, v, ⟨y₂, hy₂, rfl⟩, rfl⟩ := hz
  have hy₁' : (Fin.cons t₁ y₁ : Fin (m + 1) → ℝ) ∈ K := hy₁
  have hy₂' : (Fin.cons t₂ y₂ : Fin (m + 1) → ℝ) ∈ K := hy₂
  have hmem := hK hy₁' hy₂' h0 (by linarith : (0 : ℝ) ≤ 1 - lam) (by ring)
  have heq : lam • (Fin.cons t₁ y₁ : Fin (m + 1) → ℝ)
        + (1 - lam) • (Fin.cons t₂ y₂ : Fin (m + 1) → ℝ)
      = Fin.cons (lam * t₁ + (1 - lam) * t₂) (lam • y₁ + (1 - lam) • y₂) := by
    ext i
    refine Fin.cases ?_ ?_ i <;> simp
  rw [heq] at hmem
  exact hmem

/-- **Brunn's theorem, sharp form.**  For a convex measurable `K ⊆ ℝ^(m+1)`, the slice-volume
function `t ↦ volume (slice K t) ^ (1/m)` is concave (in `ℝ≥0∞`) on the set of `t` with
nonempty slice. -/
theorem brunn_slice_sharp {m : ℕ} (hm : m ≠ 0) {K : Set (Fin (m + 1) → ℝ)}
    (hKconv : Convex ℝ K) (hKmeas : MeasurableSet K)
    {lam t₁ t₂ : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hne1 : (slice K t₁).Nonempty) (hne2 : (slice K t₂).Nonempty) :
    ENNReal.ofReal lam * volume (slice K t₁) ^ (1 / (m : ℝ))
        + ENNReal.ofReal (1 - lam) * volume (slice K t₂) ^ (1 / (m : ℝ))
      ≤ volume (slice K (lam * t₁ + (1 - lam) * t₂)) ^ (1 / (m : ℝ)) := by
  have hninv : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
  refine le_trans (brunn_minkowski_sharp hm h0 h1 (measurableSet_slice hKmeas t₁)
    (measurableSet_slice hKmeas t₂) hne1 hne2) ?_
  exact ENNReal.rpow_le_rpow (measure_mono (smul_add_slice_subset hKconv h0 h1)) hninv

/-- **Brunn's theorem, as a `ConcaveOn` statement.**  For a convex measurable
`K ⊆ ℝ^(m+1)` and a convex set `S ⊆ ℝ` of first coordinates on which the slice is nonempty and
of finite volume, `t ↦ volume (slice K t).toReal ^ (1/m)` is concave on `S`.

The finiteness hypothesis `hfin` is mandatory and is stated explicitly: `ENNReal.toReal ⊤ = 0`,
so without it the real-valued function is not the slice volume. -/
theorem brunn_slice_concaveOn {m : ℕ} (hm : m ≠ 0) {K : Set (Fin (m + 1) → ℝ)}
    (hKconv : Convex ℝ K) (hKmeas : MeasurableSet K) {S : Set ℝ} (hS : Convex ℝ S)
    (hne : ∀ t ∈ S, (slice K t).Nonempty) (hfin : ∀ t ∈ S, volume (slice K t) ≠ ⊤) :
    ConcaveOn ℝ S (fun t => (volume (slice K t)).toReal ^ (1 / (m : ℝ))) := by
  have hminv : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
  refine ⟨hS, ?_⟩
  intro x hx y hy p q hp hq hpq
  have hq' : q = 1 - p := by linarith
  have hp1 : p ≤ 1 := by linarith
  have hmemS : p * x + (1 - p) * y ∈ S := by
    have hmem := hS hx hy hp hq hpq
    simpa [smul_eq_mul, hq'] using hmem
  have key := brunn_slice_sharp hm hKconv hKmeas (lam := p) (t₁ := x) (t₂ := y)
    hp hp1 (hne x hx) (hne y hy)
  have hxne : ENNReal.ofReal p * volume (slice K x) ^ (1 / (m : ℝ)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hminv (hfin x hx))
  have hyne : ENNReal.ofReal (1 - p) * volume (slice K y) ^ (1 / (m : ℝ)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hminv (hfin y hy))
  have h := ENNReal.toReal_mono
    (ENNReal.rpow_ne_top_of_nonneg hminv (hfin _ hmemS)) key
  rw [ENNReal.toReal_add hxne hyne, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 1 - p),
    ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at h
  simpa [smul_eq_mul, hq'] using h

end Brunn

/-! ### Non-vacuity, and sharpness of the hypotheses

The theorems above quantify over plain measurable nonempty sets, so they cannot be vacuous;
the following witness nevertheless exhibits a *nondegenerate* instance (two unit cubes, of
finite positive volume), so that the reader can see the statement has content beyond the
`volume = 0` / `volume = ⊤` corners. -/

/-- Non-vacuity witness for `Arlib.brunn_minkowski_sharp`: the unit cube in `ℝⁿ` satisfies
every hypothesis, and has finite positive volume. -/
example {n : ℕ} (hn : n ≠ 0) :
    ENNReal.ofReal (1 / 2 : ℝ)
          * volume (Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) 1) ^ (1 / (n : ℝ))
        + ENNReal.ofReal (1 - 1 / 2 : ℝ)
          * volume (Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) 1) ^ (1 / (n : ℝ))
      ≤ volume ((1 / 2 : ℝ) • (Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) 1)
          + (1 - 1 / 2 : ℝ) • (Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) 1)) ^ (1 / (n : ℝ)) :=
  brunn_minkowski_sharp hn (by norm_num) (by norm_num)
    (MeasurableSet.univ_pi fun _ => measurableSet_Icc)
    (MeasurableSet.univ_pi fun _ => measurableSet_Icc)
    ⟨0, fun i _ => by norm_num⟩ ⟨0, fun i _ => by norm_num⟩

/-- The unit cube has volume `1`, so the witness above is genuinely nondegenerate. -/
example {n : ℕ} : volume (Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) 1) = 1 := by
  rw [volume_pi_pi]
  simp [Real.volume_Icc]

end Arlib

/-! ### Axiom check -/

#print axioms Arlib.brunn_minkowski_sharp
#print axioms Arlib.brunn_minkowski_sharp_inv
#print axioms Arlib.brunn_minkowski_sharp_finrank
#print axioms Arlib.brunn_minkowski_sharp_toReal
#print axioms Arlib.brunn_slice_sharp
#print axioms Arlib.brunn_slice_concaveOn
#print axioms Arlib.ofReal_mul_volume_rpow_le
#print axioms Arlib.ofReal_one_sub_mul_volume_rpow_le
#print axioms Arlib.volume_smul_set
#print axioms Arlib.volume_singleton_add
#print axioms Arlib.smul_add_slice_subset
#print axioms Arlib.measurableSet_slice
