/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Group.Integral
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.OneDimIsoperimetry
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.NeedleProfile

/-!
# Cousins–Vempala's inequality `(1d-1)`

This file proves the *first* of the two one-dimensional inequalities that the Localization
Lemma reduces Cousins–Vempala's Theorem 3.4 (`thm:iso`) to, namely `(1d-1)` of
`1409.6011/vol3_journal.tex:498`:

  `∫_a^b h·ℓ^{n−1} · ∫_u^v h·ℓ^{n−1} ≥ (d_h(u,v)/(4√n)) · ∫_a^u h·ℓ^{n−1} · ∫_v^b h·ℓ^{n−1}`

for a one-dimensional log-concave `h` with support `[a,b]` and `a ≤ u ≤ v ≤ b`.  Cousins and
Vempala attribute it to Lemma 3.8 of Kannan–Lovász–Simonovits 1997 and give no proof; the
proof below is self-contained.

## Affine versus concave profiles

Cousins–Vempala state `(1d-1)` for `ℓ` **affine** ("a nonnegative linear function
`l : [0,1] → ℝ₊`").  The localization machinery of this repository delivers a profile that
is only known to satisfy "`W ^ (1/m)` concave", and `Arlib.exists_convex_slice_profile_not_affine`
**refutes** the concave-to-affine upgrade.  The main theorem `Arlib.kls38_concave` is therefore
stated for `ℓ` merely **concave and nonnegative**; affineness is never used.  The affine form
is recovered as the corollary `Arlib.kls38_affine`, in exactly the shape of the `h1d1` binder
of `Arlib.gaussianRestricted_isoperimetry` (`Arlib.Convexity.SharpIsoperimetry`).

## The constant

`(1d-1)` is proved with the paper's constant: `4√n`, no correction.  The slack in the chain
below is a factor of about `1.36`, and it is genuinely needed — the extremal configuration is
the Gamma weight `t^{n−1}e^{−Mt}` cut at its mode, where the two sides differ by a factor
`√(2π)/4·(1 + o(1)) ≈ 0.63`.  So `√n` is not an artefact: an `n`-free constant is false.

## Where the `√n` comes from

`W = ℓ^m·g` (`m = n − 1`) is log-concave, and for the density distance of `W` itself the
inequality holds with constant `1` and no `√n` at all (`Arlib.densDist_mul_mass_le`): one line
of the division-free one-dimensional Prékopa inequality.  What `(1d-1)` asks for is the
density distance of `g` *alone*, and the profile `ℓ^m` can cancel a large variation of `g`.
The proof splits on whether it does:

* **Weight branch.**  If `d_g(u,v)·W v ≤ 4√n·(W u − W v)` (or its mirror image), the
  Prékopa comparison `Arlib.massRight_sub_mul_le` finishes immediately.
* **Profile branch** (`Arlib.kls38_case2_left`).  Otherwise the profile is doing the
  cancelling, and it can only do so at a definite rate: `ℓ` concave forces `ℓ` to lie below
  the backward extension of its chord (`Arlib.concaveOn_le_chord_left`), so `ℓ^m` decays at
  least like `(1 − s/q)^m ≤ exp(−ms/q − ms²/(2q²))` to the left of `u`, where `q` is the
  distance back to the chord's zero.  Multiplying by the exponential bound on `g`
  (`Arlib.logConcaveOn_le_exp_left`) dominates `W` on `[a,u]` by a Gaussian of width `q/√m`
  (`Arlib.needleWeight_le_gaussian_left`), whose total mass is `q·√(2π/m)`
  (`Arlib.needleMass_left_le`).  The `√m ≈ √n` in the denominator of that mass is the `√n`
  of `(1d-1)`.

## Main results

* `Arlib.kls38_concave` — **`(1d-1)`**, for a concave profile.
* `Arlib.kls38_affine` — `(1d-1)` for an affine profile, in the exact shape of the `h1d1`
  binder of `Arlib.gaussianRestricted_isoperimetry`.
* `Arlib.kls38_concave_witness` — non-vacuity: `n = 2`, `ℓ t = 1 − t²` (concave, **not**
  affine), `g t = 1 − t`, on `[0,1]` cut at `1/4, 1/2`; every hypothesis holds, the left-hand
  side is `8567/1769472 > 0` and the inequality is strict.
* `Arlib.densDist_mul_mass_le` — the same inequality for the density distance of the whole
  needle weight, with constant `1` in place of `1/(4√n)`; and
  `Arlib.logRatio_mul_mass_le`, its sharper log-ratio form.
* `Arlib.massRight_sub_mul_le`, `Arlib.massLeft_sub_mul_le` — the division-free form of the
  one-dimensional Prékopa inequalities of `Arlib.Convexity.OneDimIsoperimetry`.
* `Arlib.kls38_case2_left`, `Arlib.kls38_case2_right` — the profile branch and its reflection.
* `Arlib.kls38_constant_bound` — the single numerical inequality the whole chain reduces to,
  `√(2πm)·exp(m/(2(4S−1)²) + 1/(4S)) ≤ 4S − 1` for `S = √(m+1)`.
* Supporting analysis: `Arlib.one_sub_pow_le_exp`, `Arlib.integral_exp_linear_sub_mul_sq`,
  `Arlib.logConcaveOn_min_le`, `Arlib.logConcaveOn_zero_side`, `Arlib.concaveOn_reflect`,
  `Arlib.logConcaveOn_reflect`.

## Relation to the paper

No discrepancy was found in `(1d-1)` itself: the printed statement — constant `4√n`,
`d_h` normalised as `|h(u) − h(v)|/max{h(u),h(v)}` (`Arlib.densDist`) — is what is proved.
Two remarks nonetheless.

1. `d_h ≤ 1` (`Arlib.densDist_le_one`), so `(1d-1)` never gives a coefficient above
   `1/(4√n)`; this is the cap already recorded in `Arlib.Convexity.SharpIsoperimetry`.
2. The paper's "follows directly from Lemma 3.8 in [KLS97]" hides the whole profile branch.
   Nothing weaker than the Gaussian-width estimate above will do: the cross-ratio inequality
   of Lovász–Simonovits, which is what one first reaches for, is off by a factor `√n`
   precisely on the Gamma extremal.

## References

Cousins and Vempala, *Gaussian Cooling and O\*(n³) Algorithms for Volume and Gaussian
Volume*, §3 (`1409.6011/vol3_journal.tex:467–508`).

Kannan, Lovász and Simonovits, *Random walks and an `O*(n⁵)` volume algorithm for convex
bodies*, Random Structures Algorithms **11** (1997), Lemma 3.8.
-/

namespace Arlib

open MeasureTheory Set

/-! ### Division-free one-dimensional Prékopa

`Arlib.massLeft_mul_le` and `Arlib.massRight_mul_le` compare a value of `w` with a tail
mass.  Splitting the tail at the second point turns them into statements about the
*middle* mass `∫_u^v w`, which is the shape every argument below uses. -/

section SubMul

variable {a b : ℝ} {w : ℝ → ℝ}

/-- **Right form.** For log-concave `w ≥ 0` on `[a,b]` and `a ≤ u ≤ v ≤ b`,

  `(w u − w v) · ∫_v^b w ≤ w v · ∫_u^v w`.

Equivalently `∫_v^b w ≤ (∫_u^v w) / (w u / w v − 1)`: a weight that drops by a factor
`w u / w v` across `[u,v]` cannot carry much mass beyond `v`.  This is
`Arlib.massRight_mul_le` with the tail `∫_u^b w` split at `v`. -/
theorem massRight_sub_mul_le (hw : LogConcaveOn (Set.Icc a b) w)
    (hw0 : ∀ t ∈ Set.Icc a b, 0 ≤ w t) (hint : IntervalIntegrable w volume a b)
    {u v : ℝ} (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    (w u - w v) * (∫ t in v..b, w t) ≤ w v * ∫ t in u..v, w t := by
  have hsplit : (∫ t in u..v, w t) + (∫ t in v..b, w t) = ∫ t in u..b, w t :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_of_subinterval hint hau huv hvb)
      (intervalIntegrable_of_subinterval hint (hau.trans huv) hvb le_rfl)
  have h := massRight_mul_le hw hw0 hint hau huv hvb
  rw [← hsplit] at h
  nlinarith [h]

/-- **Left form.** For log-concave `w ≥ 0` on `[a,b]` and `a ≤ u ≤ v ≤ b`,

  `(w v − w u) · ∫_a^u w ≤ w u · ∫_u^v w`.

This is `Arlib.massLeft_mul_le` with the tail `∫_a^v w` split at `u`. -/
theorem massLeft_sub_mul_le (hw : LogConcaveOn (Set.Icc a b) w)
    (hw0 : ∀ t ∈ Set.Icc a b, 0 ≤ w t) (hint : IntervalIntegrable w volume a b)
    {u v : ℝ} (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    (w v - w u) * (∫ t in a..u, w t) ≤ w u * ∫ t in u..v, w t := by
  have hsplit : (∫ t in a..u, w t) + (∫ t in u..v, w t) = ∫ t in a..v, w t :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_of_subinterval hint le_rfl hau (huv.trans hvb))
      (intervalIntegrable_of_subinterval hint hau huv hvb)
  have h := massLeft_mul_le hw hw0 hint hau huv hvb
  rw [← hsplit] at h
  nlinarith [h]

end SubMul

/-! ### `(1d-1)` for the density distance of the needle weight -/

section DensDistWeight

variable {a b : ℝ} {w : ℝ → ℝ}

/-- **`(1d-1)` with `d_w` in place of `d_h`, and constant `1` in place of `1/(4√n)`.**

For a log-concave `w ≥ 0` on `[a,b]` and `a ≤ u ≤ v ≤ b`,

  `d_w(u,v) · (∫_a^u w) · (∫_v^b w) ≤ (∫_a^b w) · (∫_u^v w)`

where `d_w(u,v) = |w u − w v| / max (w u) (w v)` is `Arlib.densDist`.

The proof is two lines of `Arlib.massRight_sub_mul_le`: assuming `w v ≤ w u` (the other
case is symmetric) one has `d_w(u,v) = (w u − w v)/w u`, so

  `d_w(u,v) · ∫_v^b w = ((w u − w v) · ∫_v^b w)/w u ≤ (w v · ∫_u^v w)/w u ≤ ∫_u^v w`,

and the remaining factor `∫_a^u w` is at most `∫_a^b w`.

Note the constant is `1`, *better* than the `1/(4√n)` of `(1d-1)`; the content of `(1d-1)`
is that the same holds with `d_w` replaced by `d_h`, where `w = h·ℓ^{n−1}` and `h` alone is
the density.  Those two distances are genuinely different: the profile factor `ℓ^{n−1}` can
cancel a large variation of `h`, and that is where the `√n` of `(1d-1)` comes from. -/
theorem densDist_mul_mass_le (hw : LogConcaveOn (Set.Icc a b) w)
    (hw0 : ∀ t ∈ Set.Icc a b, 0 ≤ w t) (hint : IntervalIntegrable w volume a b)
    {u v : ℝ} (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    densDist w u v * ((∫ t in a..u, w t) * ∫ t in v..b, w t)
      ≤ (∫ t in a..b, w t) * ∫ t in u..v, w t := by
  have hub : u ≤ b := huv.trans hvb
  have hav : a ≤ v := hau.trans huv
  have hA : 0 ≤ ∫ t in a..u, w t :=
    intervalIntegral.integral_nonneg hau fun t ht => hw0 t ⟨ht.1, ht.2.trans hub⟩
  have hB : 0 ≤ ∫ t in u..v, w t :=
    intervalIntegral.integral_nonneg huv fun t ht => hw0 t ⟨hau.trans ht.1, ht.2.trans hvb⟩
  have hC : 0 ≤ ∫ t in v..b, w t :=
    intervalIntegral.integral_nonneg hvb fun t ht => hw0 t ⟨hav.trans ht.1, ht.2⟩
  have hsplit : (∫ t in a..u, w t) + (∫ t in u..v, w t) + (∫ t in v..b, w t)
      = ∫ t in a..b, w t := by
    rw [intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_of_subinterval hint le_rfl hau hub)
        (intervalIntegrable_of_subinterval hint hau huv hvb),
      intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_of_subinterval hint le_rfl hav hvb)
        (intervalIntegrable_of_subinterval hint hav hvb le_rfl)]
  have hwu : 0 ≤ w u := hw0 u ⟨hau, hub⟩
  have hwv : 0 ≤ w v := hw0 v ⟨hav, hvb⟩
  rcases le_total (w v) (w u) with hle | hle
  · rcases eq_or_lt_of_le hwu with hzero | hupos
    · have hv0 : w v = 0 := le_antisymm (hle.trans hzero.symm.le) hwv
      have : densDist w u v = 0 := by
        rw [densDist, hv0, ← hzero]; norm_num
      rw [this, zero_mul]
      nlinarith
    · have hdd : densDist w u v = (w u - w v) / w u := by
        rw [densDist, max_eq_left hle, abs_of_nonneg (by linarith)]
      have key : densDist w u v * (∫ t in v..b, w t) ≤ ∫ t in u..v, w t := by
        rw [hdd, div_mul_eq_mul_div, div_le_iff₀ hupos]
        have := massRight_sub_mul_le hw hw0 hint hau huv hvb
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left key hA]
  · rcases eq_or_lt_of_le hwv with hzero | hvpos
    · have hu0 : w u = 0 := le_antisymm (hle.trans hzero.symm.le) hwu
      have : densDist w u v = 0 := by
        rw [densDist, hu0, ← hzero]; norm_num
      rw [this, zero_mul]
      nlinarith
    · have hdd : densDist w u v = (w v - w u) / w v := by
        rw [densDist, max_eq_right hle, abs_of_nonpos (by linarith), neg_sub]
      have key : densDist w u v * (∫ t in a..u, w t) ≤ ∫ t in u..v, w t := by
        rw [hdd, div_mul_eq_mul_div, div_le_iff₀ hvpos]
        have := massLeft_sub_mul_le hw hw0 hint hau huv hvb
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left key hC]

/-- **The log-ratio strengthening of `Arlib.densDist_mul_mass_le`.**

For log-concave `w ≥ 0` on `[a,b]` and `a ≤ u ≤ v ≤ b`,

  `|log (w u) − log (w v)| · (∫_a^u w) · (∫_v^b w) ≤ (∫_a^b w) · (∫_u^v w)`.

This is sharper than `Arlib.densDist_mul_mass_le` wherever both values are positive, since
`d_w(u,v) = 1 − min/max ≤ log (max/min)`; at a zero value of `w` the two statements are
incomparable, but both sides vanish there. -/
theorem logRatio_mul_mass_le (hw : LogConcaveOn (Set.Icc a b) w)
    (hw0 : ∀ t ∈ Set.Icc a b, 0 ≤ w t) (hint : IntervalIntegrable w volume a b)
    {u v : ℝ} (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    |Real.log (w u) - Real.log (w v)| * ((∫ t in a..u, w t) * ∫ t in v..b, w t)
      ≤ (∫ t in a..b, w t) * ∫ t in u..v, w t := by
  have hub : u ≤ b := huv.trans hvb
  have hav : a ≤ v := hau.trans huv
  have hA : 0 ≤ ∫ t in a..u, w t :=
    intervalIntegral.integral_nonneg hau fun t ht => hw0 t ⟨ht.1, ht.2.trans hub⟩
  have hB : 0 ≤ ∫ t in u..v, w t :=
    intervalIntegral.integral_nonneg huv fun t ht => hw0 t ⟨hau.trans ht.1, ht.2.trans hvb⟩
  have hC : 0 ≤ ∫ t in v..b, w t :=
    intervalIntegral.integral_nonneg hvb fun t ht => hw0 t ⟨hav.trans ht.1, ht.2⟩
  have hsplit : (∫ t in a..u, w t) + (∫ t in u..v, w t) + (∫ t in v..b, w t)
      = ∫ t in a..b, w t := by
    rw [intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_of_subinterval hint le_rfl hau hub)
        (intervalIntegrable_of_subinterval hint hau huv hvb),
      intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_of_subinterval hint le_rfl hav hvb)
        (intervalIntegrable_of_subinterval hint hav hvb le_rfl)]
  have hwu : 0 ≤ w u := hw0 u ⟨hau, hub⟩
  have hwv : 0 ≤ w v := hw0 v ⟨hav, hvb⟩
  have hright := massRight_sub_mul_le hw hw0 hint hau huv hvb
  have hleft := massLeft_sub_mul_le hw hw0 hint hau huv hvb
  rcases eq_or_lt_of_le hwu with hu0 | hupos
  · rcases eq_or_lt_of_le hwv with hv0 | hvpos
    · rw [← hu0, ← hv0]; simp; nlinarith
    · -- `w u = 0 < w v` forces the left mass to vanish.
      have hA0 : (∫ t in a..u, w t) = 0 := by nlinarith
      rw [hA0]; simp; nlinarith
  · rcases eq_or_lt_of_le hwv with hv0 | hvpos
    · -- `w v = 0 < w u` forces the right mass to vanish.
      have hC0 : (∫ t in v..b, w t) = 0 := by nlinarith
      rw [hC0]; simp; nlinarith
    · -- Both values positive: compare the log ratio with the relative gap.
      have hlog : ∀ x y : ℝ, 0 < x → 0 < y → (Real.log x - Real.log y) * y ≤ x - y := by
        intro x y hx hy
        have h1 : Real.log x - Real.log y = Real.log (x / y) := (Real.log_div hx.ne' hy.ne').symm
        have h2 : Real.log (x / y) ≤ x / y - 1 := Real.log_le_sub_one_of_pos (div_pos hx hy)
        have h3 : (x / y - 1) * y = x - y := by field_simp
        nlinarith [mul_le_mul_of_nonneg_right (h1 ▸ h2) hy.le]
      rcases abs_cases (Real.log (w u) - Real.log (w v)) with ⟨habs, _⟩ | ⟨habs, _⟩
      · rw [habs]
        have hkey : (Real.log (w u) - Real.log (w v)) * (∫ t in v..b, w t)
            ≤ ∫ t in u..v, w t := by
          have h1 := hlog (w u) (w v) hupos hvpos
          nlinarith [mul_le_mul_of_nonneg_right h1 hC]
        nlinarith [mul_le_mul_of_nonneg_left hkey hA]
      · rw [habs]
        have hkey : (Real.log (w v) - Real.log (w u)) * (∫ t in a..u, w t)
            ≤ ∫ t in u..v, w t := by
          have h1 := hlog (w v) (w u) hvpos hupos
          nlinarith [mul_le_mul_of_nonneg_right h1 hA]
        nlinarith [mul_le_mul_of_nonneg_left hkey hC]

end DensDistWeight

/-! ### The needle weight of `(1d-1)`

`(1d-1)` is about the weight `t ↦ ℓ t ^ (n−1) · h t` with `ℓ ≥ 0` concave (Cousins–Vempala
write `ℓ` affine; see the file header) and `h ≥ 0` log-concave.  That weight is log-concave,
so everything above applies to it. -/

section Profile

/-- **A nonnegative concave profile raised to a power, times a log-concave weight, is
log-concave.**  Affineness of the profile is not used. -/
theorem logConcaveOn_pow_mul_of_concaveOn {E : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E} {l g : E → ℝ} (hl : ConcaveOn ℝ s l) (hl0 : ∀ ⦃x⦄, x ∈ s → 0 ≤ l x)
    (hg : LogConcaveOn s g) (hg0 : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (k : ℕ) :
    LogConcaveOn s (fun t => l t ^ k * g t) :=
  (logConcaveOn_pow_of_concaveOn hl hl0 k).mul hg (fun _ hx => pow_nonneg (hl0 hx) k) hg0

variable {a b : ℝ} {l g : ℝ → ℝ}

/-- **`(1d-1)` for the needle weight, with the density distance of the *whole* weight.**

For `ℓ ≥ 0` concave and `g ≥ 0` log-concave on `[a,b]`, writing `W = ℓ^k · g`,

  `d_W(u,v) · (∫_a^u W)(∫_v^b W) ≤ (∫_a^b W)(∫_u^v W)`.

This is `Arlib.densDist_mul_mass_le` at `w = W`.  It is *not* `(1d-1)`: the paper's
distance is `d_g`, of the density alone. -/
theorem densDist_profile_mul_mass_le (hl : ConcaveOn ℝ (Set.Icc a b) l)
    (hl0 : ∀ t ∈ Set.Icc a b, 0 ≤ l t) (hg : LogConcaveOn (Set.Icc a b) g)
    (hg0 : ∀ t ∈ Set.Icc a b, 0 ≤ g t) (k : ℕ)
    (hint : IntervalIntegrable (fun t => l t ^ k * g t) volume a b)
    {u v : ℝ} (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    densDist (fun t => l t ^ k * g t) u v
        * ((∫ t in a..u, l t ^ k * g t) * ∫ t in v..b, l t ^ k * g t)
      ≤ (∫ t in a..b, l t ^ k * g t) * ∫ t in u..v, l t ^ k * g t :=
  densDist_mul_mass_le (logConcaveOn_pow_mul_of_concaveOn hl hl0 hg hg0 k)
    (fun t ht => mul_nonneg (pow_nonneg (hl0 t ht) k) (hg0 t ht)) hint hau huv hvb

end Profile

/-! ### Non-vacuity

Every hypothesis above is satisfiable *simultaneously with a strictly positive left-hand
side and a strict inequality*, with a profile `ℓ` that is genuinely concave and **not**
affine — so nothing here is the vacuous `0 ≤ something`, and nothing here secretly assumes
the affine profile that `Arlib.exists_convex_slice_profile_not_affine` refutes. -/

section Witness

/-- `1 − t²` is concave on `[0,1]`. -/
theorem concaveOn_one_sub_sq_Icc :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun t : ℝ => 1 - t ^ 2) := by
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun t : ℝ => t ^ 2) :=
    (convexOn_pow 2).subset (fun x hx => hx.1) (convex_Icc _ _)
  have h := hconv.neg.add_const 1
  have heq : ((-fun t : ℝ => t ^ 2) + fun _ => (1 : ℝ)) = fun t : ℝ => 1 - t ^ 2 := by
    funext t
    simp only [Pi.add_apply, Pi.neg_apply]
    ring
  rwa [heq] at h

/-- `1 − t²` is not affine: it disagrees with every `c₀ + c₁t` at one of `0, 1, −1`. -/
theorem one_sub_sq_not_affine_Icc :
    ¬ ∃ c₀ c₁ : ℝ, ∀ t : ℝ, 1 - t ^ 2 = c₀ + c₁ * t := by
  rintro ⟨c₀, c₁, h⟩
  have h0 := h 0
  have h1 := h 1
  have h2 := h (-1)
  norm_num at h0 h1 h2
  linarith

/-- **Non-vacuity of `Arlib.densDist_profile_mul_mass_le`** (hence of
`Arlib.densDist_mul_mass_le`, which it instantiates).

Profile `ℓ t = 1 − t²` — concave and *not* affine — with `k = 1`, density `g ≡ 1`, on
`[0,1]`, cut at `u = 1/4`, `v = 1/2`.  The weight is `W t = 1 − t²`, and the inequality
delivered is `47/4608 ≤ 41/288`, both sides strictly positive and the inequality strict. -/
theorem densDist_profile_mul_mass_witness :
    ∃ (l g : ℝ → ℝ) (k : ℕ) (a b u v : ℝ),
      ConcaveOn ℝ (Set.Icc a b) l ∧ (∀ t ∈ Set.Icc a b, 0 ≤ l t) ∧
        (¬ ∃ c₀ c₁ : ℝ, ∀ t : ℝ, l t = c₀ + c₁ * t) ∧
        LogConcaveOn (Set.Icc a b) g ∧ (∀ t ∈ Set.Icc a b, 0 ≤ g t) ∧
        IntervalIntegrable (fun t => l t ^ k * g t) volume a b ∧
        a ≤ u ∧ u ≤ v ∧ v ≤ b ∧
        0 < densDist (fun t => l t ^ k * g t) u v
              * ((∫ t in a..u, l t ^ k * g t) * ∫ t in v..b, l t ^ k * g t) ∧
        densDist (fun t => l t ^ k * g t) u v
              * ((∫ t in a..u, l t ^ k * g t) * ∫ t in v..b, l t ^ k * g t)
          < (∫ t in a..b, l t ^ k * g t) * ∫ t in u..v, l t ^ k * g t := by
  have hI : ∀ p q : ℝ, (∫ t in p..q, (1 - t ^ 2) ^ (1 : ℕ) * (1 : ℝ))
      = (q - p) - (q ^ 3 - p ^ 3) / 3 := by
    intro p q
    have : (fun t : ℝ => (1 - t ^ 2) ^ (1 : ℕ) * (1 : ℝ)) = fun t : ℝ => 1 - t ^ 2 := by
      funext t; ring
    rw [this, intervalIntegral.integral_sub intervalIntegrable_const
      (intervalIntegral.intervalIntegrable_pow 2)]
    simp [integral_pow]
    ring
  have hcont : Continuous (fun t : ℝ => (1 - t ^ 2) ^ (1 : ℕ) * (1 : ℝ)) := by fun_prop
  refine ⟨fun t => 1 - t ^ 2, fun _ => 1, 1, 0, 1, 1 / 4, 1 / 2,
    concaveOn_one_sub_sq_Icc, fun t ht => by nlinarith [ht.1, ht.2],
    one_sub_sq_not_affine_Icc, logConcaveOn_const (convex_Icc 0 1) zero_le_one,
    fun _ _ => zero_le_one, hcont.intervalIntegrable _ _,
    by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [hI, hI]
    have hd : densDist (fun t : ℝ => (1 - t ^ 2) ^ (1 : ℕ) * (1 : ℝ)) (1 / 4) (1 / 2)
        = 1 / 5 := by
      rw [densDist]; norm_num
    rw [hd]; norm_num
  · rw [hI, hI, hI]
    have hd : densDist (fun t : ℝ => (1 - t ^ 2) ^ (1 : ℕ) * (1 : ℝ)) (1 / 4) (1 / 2)
        = 1 / 5 := by
      rw [densDist]; norm_num
    rw [hd]; norm_num

end Witness

/-! ### An analytic toolkit for the `√n`

The density distance of `(1d-1)` is that of `h` *alone*, while the mass inequalities of the
previous sections see only the product `W = ℓ^m·h`.  The profile can cancel a large
variation of `h`, and the estimate that limits how much it can cancel is a Laplace-type
bound: on `[a,u]` the weight is dominated by `W u · exp(β·(u−t) − α·(u−t)²)` with
`α = m/(2q²)` for a length `q ≥ u − a` read off from the profile, and a Gaussian of that
width has mass `q·√(2π/m)`.  That is where the `√m ≈ √n` comes from. -/

section Analytic

/-- `1 − x ≤ exp(−x − x²/2)` for `x ≥ 0`: the function `(1−x)·exp(x + x²/2)` has derivative
`−x²·exp(x + x²/2) ≤ 0` everywhere, hence is at most its value `1` at `0`. -/
theorem one_sub_le_exp_neg_sub_sq_half {x : ℝ} (hx : 0 ≤ x) :
    1 - x ≤ Real.exp (-x - x ^ 2 / 2) := by
  have hderiv : ∀ y : ℝ, HasDerivAt (fun t : ℝ => (1 - t) * Real.exp (t + t ^ 2 / 2))
      (-(y ^ 2) * Real.exp (y + y ^ 2 / 2)) y := by
    intro y
    have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) y := by
      simpa using (hasDerivAt_id y).const_sub 1
    have hp : HasDerivAt (fun t : ℝ => t ^ 2 / 2) y y := by
      have := (hasDerivAt_pow 2 y).div_const 2
      simpa using this
    have hid : HasDerivAt (fun t : ℝ => t) 1 y := hasDerivAt_id y
    have h2 : HasDerivAt (fun t : ℝ => t + t ^ 2 / 2) (1 + y) y := hid.add hp
    have h3 : HasDerivAt (fun t : ℝ => Real.exp (t + t ^ 2 / 2))
        (Real.exp (y + y ^ 2 / 2) * (1 + y)) y := h2.exp
    have h4 := h1.mul h3
    have heq : -1 * Real.exp (y + y ^ 2 / 2) + (1 - y) * (Real.exp (y + y ^ 2 / 2) * (1 + y))
        = -(y ^ 2) * Real.exp (y + y ^ 2 / 2) := by ring
    rwa [heq] at h4
  have hanti : Antitone (fun t : ℝ => (1 - t) * Real.exp (t + t ^ 2 / 2)) :=
    antitone_of_deriv_nonpos (fun y => (hderiv y).differentiableAt) fun y => by
      rw [(hderiv y).deriv]
      have := (Real.exp_pos (y + y ^ 2 / 2)).le
      nlinarith [sq_nonneg y]
  have h := hanti hx
  simp only at h
  have hpos : 0 < Real.exp (x + x ^ 2 / 2) := Real.exp_pos _
  have hinv : Real.exp (-x - x ^ 2 / 2) = 1 / Real.exp (x + x ^ 2 / 2) := by
    rw [eq_div_iff hpos.ne', ← Real.exp_add]
    norm_num
  rw [hinv, le_div_iff₀ hpos]
  norm_num at h
  linarith

/-- `(1 − x)^m ≤ exp(−m·x − m·x²/2)` for `0 ≤ x ≤ 1`. -/
theorem one_sub_pow_le_exp {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (m : ℕ) :
    (1 - x) ^ m ≤ Real.exp (-(m * x) - m * x ^ 2 / 2) := by
  have h1 : (1 - x) ^ m ≤ (Real.exp (-x - x ^ 2 / 2)) ^ m :=
    pow_le_pow_left₀ (by linarith) (one_sub_le_exp_neg_sub_sq_half hx) m
  have h2 : (Real.exp (-x - x ^ 2 / 2)) ^ m = Real.exp (-(m * x) - m * x ^ 2 / 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  linarith [h1, h2.le, h2.ge]

/-- **The Gaussian integral with a linear term.**  For `α > 0`,

  `∫_ℝ exp(β·s − α·s²) ds = exp(β²/(4α)) · √(π/α)`. -/
theorem integral_exp_linear_sub_mul_sq {α β : ℝ} (hα : 0 < α) :
    (∫ s : ℝ, Real.exp (β * s - α * s ^ 2))
      = Real.exp (β ^ 2 / (4 * α)) * Real.sqrt (Real.pi / α) := by
  have key : ∀ s : ℝ, Real.exp (β * s - α * s ^ 2)
      = Real.exp (β ^ 2 / (4 * α)) * (fun y : ℝ => Real.exp (-α * y ^ 2)) (s - β / (2 * α)) := by
    intro s
    simp only
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  simp_rw [key]
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_sub_right_eq_self (fun y : ℝ => Real.exp (-α * y ^ 2)) (β / (2 * α)),
    integral_gaussian]

/-- Integrability of the integrand of `Arlib.integral_exp_linear_sub_mul_sq`. -/
theorem integrable_exp_linear_sub_mul_sq {α β : ℝ} (hα : 0 < α) :
    MeasureTheory.Integrable (fun s : ℝ => Real.exp (β * s - α * s ^ 2)) := by
  have key : (fun s : ℝ => Real.exp (β * s - α * s ^ 2))
      = fun s : ℝ => Real.exp (β ^ 2 / (4 * α))
          * (fun y : ℝ => Real.exp (-α * y ^ 2)) (s - β / (2 * α)) := by
    funext s
    simp only
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [key]
  exact ((integrable_exp_neg_mul_sq hα).comp_sub_right _).const_mul _

end Analytic

/-! ### Extrapolating a chord to the left

Both factors of the needle weight are controlled on `[a,u]` by their values at the two cut
points `u < v`: a concave `ℓ` lies below the *extension* of the chord through `(u,ℓ u)` and
`(v,ℓ v)`, and a log-concave `g` lies below the corresponding exponential. -/

section Extrapolate

variable {a b u v : ℝ}

/-- **A concave function lies below the backward extension of a chord.**  For
`a ≤ t ≤ u < v ≤ b` and `ℓ` concave on `[a,b]`,

  `(v − u) · ℓ t ≤ (v − u) · ℓ u − (u − t) · (ℓ v − ℓ u)`. -/
theorem concaveOn_le_chord_left {l : ℝ → ℝ} (hl : ConcaveOn ℝ (Set.Icc a b) l)
    {t : ℝ} (hat : a ≤ t) (htu : t ≤ u) (huv : u < v) (hvb : v ≤ b) :
    (v - u) * l t ≤ (v - u) * l u - (u - t) * (l v - l u) := by
  rcases eq_or_lt_of_le htu with rfl | htu'
  · simp
  have hvt : 0 < v - t := by linarith
  have hA : (0 : ℝ) ≤ (v - u) / (v - t) := div_nonneg (by linarith) hvt.le
  have hB : (0 : ℝ) ≤ (u - t) / (v - t) := div_nonneg (by linarith) hvt.le
  have hAB : (v - u) / (v - t) + (u - t) / (v - t) = 1 := by field_simp; ring
  have hmt : t ∈ Set.Icc a b := ⟨hat, by linarith⟩
  have hmv : v ∈ Set.Icc a b := ⟨by linarith, hvb⟩
  have hcomb : ((v - u) / (v - t)) • t + ((u - t) / (v - t)) • v = u := by
    simp only [smul_eq_mul]
    field_simp
    ring
  have hstep := hl.2 hmt hmv hA hB hAB
  rw [hcomb] at hstep
  simp only [smul_eq_mul] at hstep
  have hmul := mul_le_mul_of_nonneg_left hstep hvt.le
  have hexp : (v - t) * ((v - u) / (v - t) * l t + (u - t) / (v - t) * l v)
      = (v - u) * l t + (u - t) * l v := by field_simp
  rw [hexp] at hmul
  linarith

/-- **A log-concave function lies below the backward extension of an exponential chord.**
For `a ≤ t ≤ u < v ≤ b`, `g` log-concave and positive at `u` and `v`,

  `g t ≤ g u · exp((u − t) · (log (g u) − log (g v)) / (v − u))`. -/
theorem logConcaveOn_le_exp_left {g : ℝ → ℝ} (hg : LogConcaveOn (Set.Icc a b) g)
    (hg0 : ∀ s ∈ Set.Icc a b, 0 ≤ g s) {t : ℝ} (hat : a ≤ t) (htu : t ≤ u) (huv : u < v)
    (hvb : v ≤ b) (hgu : 0 < g u) (hgv : 0 < g v) :
    g t ≤ g u * Real.exp ((u - t) * (Real.log (g u) - Real.log (g v)) / (v - u)) := by
  have hvt : 0 < v - t := by linarith
  have hA : (0 : ℝ) ≤ (v - u) / (v - t) := div_nonneg (by linarith) hvt.le
  have hB : (0 : ℝ) ≤ (u - t) / (v - t) := div_nonneg (by linarith) hvt.le
  have hAB : (v - u) / (v - t) + (u - t) / (v - t) = 1 := by field_simp; ring
  have hmt : t ∈ Set.Icc a b := ⟨hat, by linarith⟩
  have hmv : v ∈ Set.Icc a b := ⟨by linarith, hvb⟩
  have hcomb : ((v - u) / (v - t)) • t + ((u - t) / (v - t)) • v = u := by
    simp only [smul_eq_mul]
    field_simp
    ring
  have hstep := hg.2 hmt hmv hA hB hAB
  rw [hcomb] at hstep
  have hgt : 0 ≤ g t := hg0 t hmt
  rcases eq_or_lt_of_le hgt with h0 | hgtpos
  · rw [← h0]
    positivity
  -- Both values positive: take logarithms of the geometric-mean inequality.
  have hlog : (v - u) / (v - t) * Real.log (g t) + (u - t) / (v - t) * Real.log (g v)
      ≤ Real.log (g u) := by
    have hprodpos : 0 < g t ^ ((v - u) / (v - t)) * g v ^ ((u - t) / (v - t)) :=
      mul_pos (Real.rpow_pos_of_pos hgtpos _) (Real.rpow_pos_of_pos hgv _)
    have := Real.log_le_log hprodpos hstep
    rwa [Real.log_mul (Real.rpow_pos_of_pos hgtpos _).ne' (Real.rpow_pos_of_pos hgv _).ne',
      Real.log_rpow hgtpos, Real.log_rpow hgv] at this
  have hmul := mul_le_mul_of_nonneg_left hlog hvt.le
  have hexp : (v - t) * ((v - u) / (v - t) * Real.log (g t)
        + (u - t) / (v - t) * Real.log (g v))
      = (v - u) * Real.log (g t) + (u - t) * Real.log (g v) := by field_simp
  rw [hexp] at hmul
  have hvu : (0 : ℝ) < v - u := by linarith
  have hgoal : Real.log (g t) * (v - u)
      ≤ (Real.log (g u) + (u - t) * (Real.log (g u) - Real.log (g v)) / (v - u)) * (v - u) := by
    rw [add_mul, div_mul_cancel₀ _ hvu.ne']
    linarith
  have hlogt : Real.log (g t)
      ≤ Real.log (g u) + (u - t) * (Real.log (g u) - Real.log (g v)) / (v - u) :=
    le_of_mul_le_mul_right hgoal hvu
  calc g t = Real.exp (Real.log (g t)) := (Real.exp_log hgtpos).symm
    _ ≤ Real.exp (Real.log (g u) + (u - t) * (Real.log (g u) - Real.log (g v)) / (v - u)) :=
        Real.exp_le_exp.mpr hlogt
    _ = g u * Real.exp ((u - t) * (Real.log (g u) - Real.log (g v)) / (v - u)) := by
        rw [Real.exp_add, Real.exp_log hgu]

end Extrapolate

/-! ### Gaussian domination of the needle weight on `[a,u]`

Combining the two extrapolations with `Arlib.one_sub_pow_le_exp` dominates `W = ℓ^m·g`
on `[a,u]` by a Gaussian of width `q/√m`, where `q = ℓ u·(v−u)/(ℓ v − ℓ u)` is the distance
from `u` back to the zero of the chord through `(u,ℓ u)` and `(v,ℓ v)`.  Integrating gives
the mass bound carrying the `√m`. -/

section GaussianDomination

variable {a b u v : ℝ} {l g : ℝ → ℝ} {m : ℕ}

/-- **Pointwise Gaussian domination.**  For `t ∈ [a,u]`,

  `ℓ t ^ m · g t ≤ (ℓ u ^ m · g u) · exp(β·(u−t) − (m/(2q²))·(u−t)²)`

whenever `β ≥ 0` dominates the excess log-slope `δ − m/q`. -/
theorem needleWeight_le_gaussian_left (hl : ConcaveOn ℝ (Set.Icc a b) l)
    (hl0 : ∀ s ∈ Set.Icc a b, 0 ≤ l s) (hg : LogConcaveOn (Set.Icc a b) g)
    (hg0 : ∀ s ∈ Set.Icc a b, 0 ≤ g s) (_hau : a ≤ u) (huv : u < v) (hvb : v ≤ b)
    (hlu : 0 < l u) (hlv : l u < l v) (hgu : 0 < g u) (hgv : 0 < g v)
    {q β : ℝ} (hq : q = l u * (v - u) / (l v - l u)) (_hβ0 : 0 ≤ β)
    (hβ : (Real.log (g u) - Real.log (g v)) / (v - u) - m / q ≤ β)
    {t : ℝ} (hat : a ≤ t) (htu : t ≤ u) :
    l t ^ m * g t
      ≤ (l u ^ m * g u) * Real.exp (β * (u - t) - (m / (2 * q ^ 2)) * (u - t) ^ 2) := by
  have hvu : (0 : ℝ) < v - u := by linarith
  have hqpos : 0 < q := by
    rw [hq]; positivity
  have hs : 0 ≤ u - t := by linarith
  have hmt : t ∈ Set.Icc a b := ⟨hat, by linarith⟩
  -- the profile
  have hchord := concaveOn_le_chord_left hl hat htu huv hvb
  have hdpos : (0 : ℝ) < l v - l u := by linarith
  have hlt : l t ≤ l u * (1 - (u - t) / q) := by
    have hkey : l u * (1 - (u - t) / q) = l u - (u - t) * (l v - l u) / (v - u) := by
      rw [hq]
      field_simp
      try ring
    rw [hkey]
    have hmul : l t * (v - u) ≤ (l u - (u - t) * (l v - l u) / (v - u)) * (v - u) := by
      rw [sub_mul, div_mul_cancel₀ _ hvu.ne']
      linarith
    exact le_of_mul_le_mul_right hmul hvu
  have hltn : 0 ≤ l t := hl0 t hmt
  have hx0 : 0 ≤ (u - t) / q := div_nonneg hs hqpos.le
  have hx1 : (u - t) / q ≤ 1 := by nlinarith [hltn, hlt, hlu]
  have hpow : l t ^ m ≤ l u ^ m * Real.exp (-(m * ((u - t) / q)) - m * ((u - t) / q) ^ 2 / 2) := by
    calc l t ^ m ≤ (l u * (1 - (u - t) / q)) ^ m := pow_le_pow_left₀ hltn hlt m
      _ = l u ^ m * (1 - (u - t) / q) ^ m := by rw [mul_pow]
      _ ≤ l u ^ m * Real.exp (-(m * ((u - t) / q)) - m * ((u - t) / q) ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left (one_sub_pow_le_exp hx0 hx1 m) (pow_nonneg hlu.le m)
  -- the density
  have hdens := logConcaveOn_le_exp_left hg hg0 hat htu huv hvb hgu hgv
  -- combine
  have hprod : l t ^ m * g t
      ≤ (l u ^ m * Real.exp (-(m * ((u - t) / q)) - m * ((u - t) / q) ^ 2 / 2))
        * (g u * Real.exp ((u - t) * (Real.log (g u) - Real.log (g v)) / (v - u))) :=
    mul_le_mul hpow hdens (hg0 t hmt) (by positivity)
  refine hprod.trans ?_
  have hexp : (l u ^ m * Real.exp (-(m * ((u - t) / q)) - m * ((u - t) / q) ^ 2 / 2))
        * (g u * Real.exp ((u - t) * (Real.log (g u) - Real.log (g v)) / (v - u)))
      = (l u ^ m * g u) * Real.exp (-(m * ((u - t) / q)) - m * ((u - t) / q) ^ 2 / 2
          + (u - t) * (Real.log (g u) - Real.log (g v)) / (v - u)) := by
    rw [Real.exp_add]; ring
  rw [hexp]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hsq : m * ((u - t) / q) ^ 2 / 2 = (m / (2 * q ^ 2)) * (u - t) ^ 2 := by
    field_simp
    try ring
  have hlin : (u - t) * (Real.log (g u) - Real.log (g v)) / (v - u) - m * ((u - t) / q)
      = ((Real.log (g u) - Real.log (g v)) / (v - u) - m / q) * (u - t) := by
    field_simp
    try ring
  nlinarith [mul_le_mul_of_nonneg_right hβ hs, hsq, hlin]

/-- **The mass to the left of `u` is at most a Gaussian mass of width `q/√m`.** -/
theorem needleMass_left_le (hl : ConcaveOn ℝ (Set.Icc a b) l)
    (hl0 : ∀ s ∈ Set.Icc a b, 0 ≤ l s) (hg : LogConcaveOn (Set.Icc a b) g)
    (hg0 : ∀ s ∈ Set.Icc a b, 0 ≤ g s) (hau : a ≤ u) (huv : u < v) (hvb : v ≤ b)
    (hlu : 0 < l u) (hlv : l u < l v) (hgu : 0 < g u) (hgv : 0 < g v) (hm : 1 ≤ m)
    (hint : IntervalIntegrable (fun t => l t ^ m * g t) volume a b)
    {q β : ℝ} (hq : q = l u * (v - u) / (l v - l u)) (hβ0 : 0 ≤ β)
    (hβ : (Real.log (g u) - Real.log (g v)) / (v - u) - m / q ≤ β) :
    (∫ t in a..u, l t ^ m * g t)
      ≤ (l u ^ m * g u) * (Real.exp (β ^ 2 * q ^ 2 / (2 * m)) * (q * Real.sqrt (2 * Real.pi / m))) := by
  have hvu : (0 : ℝ) < v - u := by linarith
  have hqpos : 0 < q := by rw [hq]; positivity
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  set α : ℝ := (m : ℝ) / (2 * q ^ 2) with hα
  have hαpos : 0 < α := by rw [hα]; positivity
  have hcont : Continuous (fun t : ℝ => Real.exp (β * (u - t) - α * (u - t) ^ 2)) := by fun_prop
  have hmono : (∫ t in a..u, l t ^ m * g t)
      ≤ ∫ t in a..u, (l u ^ m * g u) * Real.exp (β * (u - t) - α * (u - t) ^ 2) := by
    refine intervalIntegral.integral_mono_on hau
      (intervalIntegrable_of_subinterval hint le_rfl hau (by linarith)) ?_ ?_
    · exact (hcont.const_mul _).intervalIntegrable _ _
    · intro t ht
      exact needleWeight_le_gaussian_left hl hl0 hg hg0 hau huv hvb hlu hlv hgu hgv hq hβ0 hβ
        ht.1 ht.2
  refine hmono.trans ?_
  rw [intervalIntegral.integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hshift : (∫ t in a..u, Real.exp (β * (u - t) - α * (u - t) ^ 2))
      = ∫ x in (0 : ℝ)..(u - a), Real.exp (β * x - α * x ^ 2) := by
    have := intervalIntegral.integral_comp_sub_left
      (a := a) (b := u) (fun x : ℝ => Real.exp (β * x - α * x ^ 2)) u
    simpa using this
  rw [hshift, intervalIntegral.integral_of_le (by linarith : (0 : ℝ) ≤ u - a)]
  have hle : (∫ x in Set.Ioc (0 : ℝ) (u - a), Real.exp (β * x - α * x ^ 2))
      ≤ ∫ x : ℝ, Real.exp (β * x - α * x ^ 2) :=
    setIntegral_le_integral (integrable_exp_linear_sub_mul_sq hαpos)
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
  refine hle.trans ?_
  rw [integral_exp_linear_sub_mul_sq hαpos]
  have h1 : β ^ 2 / (4 * α) = β ^ 2 * q ^ 2 / (2 * m) := by
    rw [hα]; field_simp; try ring
  have h2 : Real.pi / α = q ^ 2 * (2 * Real.pi / m) := by
    rw [hα]; field_simp; try ring
  rw [h1, h2, Real.sqrt_mul (by positivity), Real.sqrt_sq hqpos.le]

end GaussianDomination

/-! ### Two structural facts about log-concave weights -/

section Structural

variable {a b u v : ℝ} {w : ℝ → ℝ}

/-- **Quasi-concavity.**  A log-concave `w ≥ 0` is at least `min (w u) (w v)` between
`u` and `v`. -/
theorem logConcaveOn_min_le (hw : LogConcaveOn (Set.Icc a b) w)
    (hw0 : ∀ s ∈ Set.Icc a b, 0 ≤ w s) (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b)
    {t : ℝ} (hut : u ≤ t) (htv : t ≤ v) : min (w u) (w v) ≤ w t := by
  rcases eq_or_lt_of_le huv with rfl | huv'
  · have : t = u := le_antisymm htv hut
    subst this
    simp
  have hvu : (0 : ℝ) < v - u := by linarith
  have hmu : u ∈ Set.Icc a b := ⟨hau, by linarith⟩
  have hmv : v ∈ Set.Icc a b := ⟨by linarith, hvb⟩
  have hmt : t ∈ Set.Icc a b := ⟨by linarith, by linarith⟩
  have hminn : 0 ≤ min (w u) (w v) := le_min (hw0 u hmu) (hw0 v hmv)
  rcases eq_or_lt_of_le hminn with hmz | hmpos
  · rw [← hmz]; exact hw0 t hmt
  have hA : (0 : ℝ) ≤ (v - t) / (v - u) := div_nonneg (by linarith) hvu.le
  have hB : (0 : ℝ) ≤ (t - u) / (v - u) := div_nonneg (by linarith) hvu.le
  have hAB : (v - t) / (v - u) + (t - u) / (v - u) = 1 := by field_simp; ring
  have hcomb : ((v - t) / (v - u)) • u + ((t - u) / (v - u)) • v = t := by
    simp only [smul_eq_mul]
    field_simp
    ring
  have hstep := hw.2 hmu hmv hA hB hAB
  rw [hcomb] at hstep
  refine le_trans ?_ hstep
  have h1 : min (w u) (w v) ^ ((v - t) / (v - u)) ≤ w u ^ ((v - t) / (v - u)) :=
    Real.rpow_le_rpow hminn (min_le_left _ _) hA
  have h2 : min (w u) (w v) ^ ((t - u) / (v - u)) ≤ w v ^ ((t - u) / (v - u)) :=
    Real.rpow_le_rpow hminn (min_le_right _ _) hB
  calc min (w u) (w v)
      = min (w u) (w v) ^ ((v - t) / (v - u)) * min (w u) (w v) ^ ((t - u) / (v - u)) := by
        rw [← Real.rpow_add hmpos, hAB, Real.rpow_one]
    _ ≤ w u ^ ((v - t) / (v - u)) * w v ^ ((t - u) / (v - u)) :=
        mul_le_mul h1 h2 (Real.rpow_nonneg hminn _) (Real.rpow_nonneg (hw0 u hmu) _)

/-- The middle mass is at least the width times the smaller endpoint value. -/
theorem width_mul_min_le_mass (hw : LogConcaveOn (Set.Icc a b) w)
    (hw0 : ∀ s ∈ Set.Icc a b, 0 ≤ w s) (hint : IntervalIntegrable w volume a b)
    (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    (v - u) * min (w u) (w v) ≤ ∫ t in u..v, w t := by
  have hmono : (∫ _t in u..v, min (w u) (w v)) ≤ ∫ t in u..v, w t := by
    refine intervalIntegral.integral_mono_on huv intervalIntegrable_const
      (intervalIntegrable_of_subinterval hint hau huv hvb) ?_
    intro t ht
    exact logConcaveOn_min_le hw hw0 hau huv hvb ht.1 ht.2
  rwa [intervalIntegral.integral_const, smul_eq_mul] at hmono

/-- **A log-concave weight vanishing at `u` vanishes on one whole side of `u`**: its
positivity set is convex, so it cannot straddle `u`. -/
theorem logConcaveOn_zero_side (hw : LogConcaveOn (Set.Icc a b) w)
    (hw0 : ∀ s ∈ Set.Icc a b, 0 ≤ w s) (hau : a ≤ u) (hub : u ≤ b) (h0 : w u = 0) :
    (∀ t ∈ Set.Icc a u, w t = 0) ∨ ∀ t ∈ Set.Icc u b, w t = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨x, hx, hxne⟩, ⟨y, hy, hyne⟩⟩ := hcon
  have hmx : x ∈ Set.Icc a b := ⟨hx.1, hx.2.trans hub⟩
  have hmy : y ∈ Set.Icc a b := ⟨hau.trans hy.1, hy.2⟩
  have hxpos : 0 < w x := lt_of_le_of_ne (hw0 x hmx) (Ne.symm hxne)
  have hypos : 0 < w y := lt_of_le_of_ne (hw0 y hmy) (Ne.symm hyne)
  have hxu : x < u := by
    rcases eq_or_lt_of_le hx.2 with rfl | h
    · exact absurd h0 hxne
    · exact h
  have huy : u < y := by
    rcases eq_or_lt_of_le hy.1 with rfl | h
    · exact absurd h0 hyne
    · exact h
  have hyx : (0 : ℝ) < y - x := by linarith
  have hA : (0 : ℝ) ≤ (y - u) / (y - x) := div_nonneg (by linarith) hyx.le
  have hB : (0 : ℝ) ≤ (u - x) / (y - x) := div_nonneg (by linarith) hyx.le
  have hAB : (y - u) / (y - x) + (u - x) / (y - x) = 1 := by field_simp; ring
  have hcomb : ((y - u) / (y - x)) • x + ((u - x) / (y - x)) • y = u := by
    simp only [smul_eq_mul]
    field_simp
    ring
  have hstep := hw.2 hmx hmy hA hB hAB
  rw [hcomb, h0] at hstep
  have : 0 < w x ^ ((y - u) / (y - x)) * w y ^ ((u - x) / (y - x)) :=
    mul_pos (Real.rpow_pos_of_pos hxpos _) (Real.rpow_pos_of_pos hypos _)
  linarith

end Structural

/-! ### The numerical constant

The chain below reduces `(1d-1)` to a single inequality between explicit constants.  With
`S = √(m+1)` it reads `√(2πm)·exp(m/(2(4S−1)²) + 1/(4S)) ≤ 4S − 1`, whose two sides are in
ratio at most about `0.735`. -/

section Constant

/-- `√(m+1) ≥ 1.41` for `m ≥ 1`. -/
theorem sqrt_succ_ge {m : ℕ} (hm : 1 ≤ m) : (1.41 : ℝ) ≤ Real.sqrt ((m : ℝ) + 1) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [show (1.41 : ℝ) = Real.sqrt (1.41 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_le_sqrt (by norm_num; linarith)

/-- **The constant bound.**  `√(2πm)·exp(m/(2(4S−1)² ) + 1/(4S)) ≤ 4S − 1` for `S = √(m+1)`
and `m ≥ 1`, stated with `√(2πm)` written as `m·√(2π/m)`. -/
theorem kls38_constant_bound {m : ℕ} (hm : 1 ≤ m) :
    (m : ℝ) * Real.sqrt (2 * Real.pi / m)
        * Real.exp ((m : ℝ) / (2 * (4 * Real.sqrt ((m : ℝ) + 1) - 1) ^ 2)
            + 1 / (4 * Real.sqrt ((m : ℝ) + 1)))
      ≤ 4 * Real.sqrt ((m : ℝ) + 1) - 1 := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  set S : ℝ := Real.sqrt ((m : ℝ) + 1) with hS
  have hS141 : (1.41 : ℝ) ≤ S := sqrt_succ_ge hm
  have hSsq : S ^ 2 = (m : ℝ) + 1 := Real.sq_sqrt (by linarith)
  have hSpos : 0 < S := by linarith
  have h4S : (0 : ℝ) < 4 * S - 1 := by linarith
  -- the exponent is at most `11/50`
  have hbound1 : (m : ℝ) / (2 * (4 * S - 1) ^ 2) ≤ 1 / 25 := by
    rw [div_le_iff₀ (show (0 : ℝ) < 2 * (4 * S - 1) ^ 2 by positivity)]
    nlinarith [hSsq, hS141, sq_nonneg (7 * S - 8)]
  have hbound2 : (1 : ℝ) / (4 * S) ≤ 9 / 50 := by
    rw [div_le_iff₀ (show (0 : ℝ) < 4 * S by positivity)]
    linarith
  have hz : (m : ℝ) / (2 * (4 * S - 1) ^ 2) + 1 / (4 * S) ≤ 11 / 50 := by linarith
  have hz0 : (0 : ℝ) ≤ (m : ℝ) / (2 * (4 * S - 1) ^ 2) + 1 / (4 * S) := by positivity
  -- `exp z ≤ 1/(1 − z) ≤ 50/39`
  have hexp : Real.exp ((m : ℝ) / (2 * (4 * S - 1) ^ 2) + 1 / (4 * S)) ≤ 50 / 39 := by
    set z : ℝ := (m : ℝ) / (2 * (4 * S - 1) ^ 2) + 1 / (4 * S) with hzdef
    have hlow : 1 - z ≤ Real.exp (-z) := by
      have := Real.add_one_le_exp (-z)
      linarith
    have hzlt : (0 : ℝ) < 1 - z := by linarith
    have hpos : 0 < Real.exp z := Real.exp_pos _
    have hinv : Real.exp (-z) = 1 / Real.exp z := by
      rw [Real.exp_neg]; ring
    rw [hinv] at hlow
    have : Real.exp z * (1 - z) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hlow hpos.le
      rwa [mul_one_div, div_self hpos.ne'] at this
    nlinarith [this, hz, hzlt, hpos]
  -- `m·√(2π/m) = √(2π)·√m ≤ 2.5067·S`
  have hsqrt : (m : ℝ) * Real.sqrt (2 * Real.pi / m) ≤ 2.51 * S := by
    have hpi : Real.pi ≤ 3.15 := Real.pi_lt_d2.le
    have h2pi : Real.sqrt (2 * Real.pi) ≤ 2.51 := by
      rw [show (2.51 : ℝ) = Real.sqrt (2.51 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num; linarith)
    have hdiv : Real.sqrt (2 * Real.pi / m) = Real.sqrt (2 * Real.pi) / Real.sqrt m :=
      Real.sqrt_div (by positivity) _
    have hmsqrt : Real.sqrt (m : ℝ) ≤ S := by
      rw [hS]; exact Real.sqrt_le_sqrt (by linarith)
    have hmsqrtpos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmpos
    have hmm : (m : ℝ) / Real.sqrt m = Real.sqrt m := by
      rw [div_eq_iff hmsqrtpos.ne']
      exact (Real.mul_self_sqrt hmpos.le).symm
    calc (m : ℝ) * Real.sqrt (2 * Real.pi / m)
        = (m : ℝ) / Real.sqrt m * Real.sqrt (2 * Real.pi) := by rw [hdiv]; ring
      _ = Real.sqrt m * Real.sqrt (2 * Real.pi) := by rw [hmm]
      _ ≤ S * 2.51 := mul_le_mul hmsqrt h2pi (Real.sqrt_nonneg _) hSpos.le
      _ = 2.51 * S := by ring
  have hfin : 2.51 * S * (50 / 39) ≤ 4 * S - 1 := by nlinarith [hS141]
  calc (m : ℝ) * Real.sqrt (2 * Real.pi / m)
          * Real.exp ((m : ℝ) / (2 * (4 * S - 1) ^ 2) + 1 / (4 * S))
      ≤ 2.51 * S * (50 / 39) := by
        apply mul_le_mul hsqrt hexp (Real.exp_pos _).le (by positivity)
    _ ≤ 4 * S - 1 := hfin

end Constant

/-! ### The profile-dominated branch

If the *weight* barely changes across `[u,v]` while the *density* changes a lot, the
mass-comparison of `Arlib.massRight_sub_mul_le` is useless and the profile must be doing the
cancelling.  This is the branch where the Gaussian domination is used, and where `√n`
appears. -/

section Case2

set_option maxHeartbeats 1000000 in
/-- **The `√n` branch of `(1d-1)`, left form.**  Under the hypothesis that the weight
comparison of `Arlib.massRight_sub_mul_le` fails — `4√(m+1)·(W u − W v) < d_g(u,v)·W v` —
the left mass obeys

  `d_g(u,v) · ∫_a^u W ≤ 4√(m+1) · ∫_u^v W`,  `W = ℓ^m·g`. -/
theorem kls38_case2_left {a b u v : ℝ} {l g : ℝ → ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hl : ConcaveOn ℝ (Set.Icc a b) l) (hl0 : ∀ s ∈ Set.Icc a b, 0 ≤ l s)
    (hg : LogConcaveOn (Set.Icc a b) g) (hg0 : ∀ s ∈ Set.Icc a b, 0 ≤ g s)
    (hint : IntervalIntegrable (fun t => l t ^ m * g t) volume a b)
    (hau : a ≤ u) (huv : u < v) (hvb : v ≤ b)
    (hgvu : g v ≤ g u) (hgv : 0 < g v) (hlu : 0 < l u) (hlv : 0 < l v)
    (hcase : 4 * Real.sqrt ((m : ℝ) + 1) * (l u ^ m * g u - l v ^ m * g v)
      < densDist g u v * (l v ^ m * g v)) :
    densDist g u v * (∫ t in a..u, l t ^ m * g t)
      ≤ 4 * Real.sqrt ((m : ℝ) + 1) * ∫ t in u..v, l t ^ m * g t := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  set S : ℝ := Real.sqrt ((m : ℝ) + 1) with hSdef
  have hS141 : (1.41 : ℝ) ≤ S := sqrt_succ_ge hm
  have hSpos : 0 < S := by linarith
  have h4S1 : (0 : ℝ) < 4 * S - 1 := by linarith
  have hgu : 0 < g u := lt_of_lt_of_le hgv hgvu
  have hWu : 0 < l u ^ m * g u := by positivity
  have hWv : 0 < l v ^ m * g v := by positivity
  have hep : (0 : ℝ) < v - u := by linarith
  have hW : LogConcaveOn (Set.Icc a b) (fun t => l t ^ m * g t) :=
    logConcaveOn_pow_mul_of_concaveOn hl (fun _ hx => hl0 _ hx) hg (fun _ hx => hg0 _ hx) m
  have hW0 : ∀ t ∈ Set.Icc a b, 0 ≤ l t ^ m * g t :=
    fun t ht => mul_nonneg (pow_nonneg (hl0 t ht) m) (hg0 t ht)
  have hAnn : (0 : ℝ) ≤ ∫ t in a..u, l t ^ m * g t :=
    intervalIntegral.integral_nonneg hau fun t ht =>
      hW0 t ⟨ht.1, ht.2.trans (huv.le.trans hvb)⟩
  have hBnn : (0 : ℝ) ≤ ∫ t in u..v, l t ^ m * g t :=
    intervalIntegral.integral_nonneg huv.le fun t ht =>
      hW0 t ⟨hau.trans ht.1, ht.2.trans hvb⟩
  have hd : densDist g u v = (g u - g v) / g u := by
    rw [densDist, max_eq_left hgvu, abs_of_nonneg (by linarith)]
  have hd0 : 0 ≤ densDist g u v := by rw [hd]; positivity
  have hd1 : densDist g u v ≤ 1 := by rw [hd, div_le_one hgu]; linarith
  rcases eq_or_lt_of_le hd0 with hdz | hdpos
  · rw [← hdz, zero_mul]; positivity
  set Δ : ℝ := Real.log (g u) - Real.log (g v) with hΔdef
  set ω : ℝ := Real.log (l u ^ m * g u) - Real.log (l v ^ m * g v) with hωdef
  have hΔ0 : 0 ≤ Δ := by rw [hΔdef, sub_nonneg]; exact Real.log_le_log hgv hgvu
  have hdΔ : densDist g u v ≤ Δ := by
    have h := Real.log_le_sub_one_of_pos (div_pos hgv hgu)
    rw [Real.log_div hgv.ne' hgu.ne'] at h
    have h2 : (g u - g v) / g u = 1 - g v / g u := by field_simp
    rw [hd, h2, hΔdef]
    linarith
  have hωle : ω * (l v ^ m * g v) ≤ l u ^ m * g u - l v ^ m * g v := by
    have h := Real.log_le_sub_one_of_pos (div_pos hWu hWv)
    rw [Real.log_div hWu.ne' hWv.ne'] at h
    have h2 : (l u ^ m * g u / (l v ^ m * g v) - 1) * (l v ^ m * g v)
        = l u ^ m * g u - l v ^ m * g v := by field_simp
    have h3 := mul_le_mul_of_nonneg_right h hWv.le
    rw [h2] at h3
    rw [hωdef]
    exact h3
  have hcase' : 4 * S * ω < densDist g u v := by
    have h2 : 4 * S * ω * (l v ^ m * g v) < densDist g u v * (l v ^ m * g v) := by
      calc 4 * S * ω * (l v ^ m * g v) = 4 * S * (ω * (l v ^ m * g v)) := by ring
        _ ≤ 4 * S * (l u ^ m * g u - l v ^ m * g v) :=
            mul_le_mul_of_nonneg_left hωle (by positivity)
        _ < densDist g u v * (l v ^ m * g v) := hcase
    exact lt_of_mul_lt_mul_right h2 hWv.le
  have h4Sw : 4 * S * ω < Δ := lt_of_lt_of_le hcase' hdΔ
  have hlog_split : Δ - ω = m * (Real.log (l v) - Real.log (l u)) := by
    rw [hΔdef, hωdef, Real.log_mul (by positivity) hgu.ne',
      Real.log_mul (by positivity) hgv.ne', Real.log_pow, Real.log_pow]
    ring
  have hθpos : 0 < Δ - ω := by
    rcases le_total 0 ω with hw0 | hw0
    · nlinarith [h4Sw, mul_nonneg hw0 h4S1.le]
    · linarith
  have hluv : l u < l v := by
    have hll : Real.log (l u) < Real.log (l v) := by nlinarith [hlog_split, hθpos, hmpos]
    exact (Real.log_lt_log_iff hlu hlv).mp hll
  have hdlv : (0 : ℝ) < l v - l u := by linarith
  set q : ℝ := l u * (v - u) / (l v - l u) with hqdef
  have hqpos : 0 < q := by rw [hqdef]; positivity
  have hq2 : q * (l v - l u) = l u * (v - u) := by rw [hqdef]; field_simp
  have hθle : (Δ - ω) * q ≤ m * (v - u) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hlv hlu)
    rw [Real.log_div hlv.ne' hlu.ne'] at h
    have h2 : (l v / l u - 1) * l u = l v - l u := by field_simp
    have h3 := mul_le_mul_of_nonneg_right h hlu.le
    rw [h2] at h3
    have h4 := mul_le_mul_of_nonneg_left h3 (mul_nonneg hmpos.le hqpos.le)
    have hmul : (m : ℝ) * ((Real.log (l v) - Real.log (l u)) * l u) * q
        ≤ (m : ℝ) * (l v - l u) * q := by
      calc (m : ℝ) * ((Real.log (l v) - Real.log (l u)) * l u) * q
          = (m : ℝ) * q * ((Real.log (l v) - Real.log (l u)) * l u) := by ring
        _ ≤ (m : ℝ) * q * (l v - l u) := h4
        _ = (m : ℝ) * (l v - l u) * q := by ring
    have hfinal : l u * ((Δ - ω) * q) ≤ l u * ((m : ℝ) * (v - u)) := by
      calc l u * ((Δ - ω) * q)
          = (m : ℝ) * ((Real.log (l v) - Real.log (l u)) * l u) * q := by
            rw [hlog_split]; ring
        _ ≤ (m : ℝ) * (l v - l u) * q := hmul
        _ = (m : ℝ) * (q * (l v - l u)) := by ring
        _ = (m : ℝ) * (l u * (v - u)) := by rw [hq2]
        _ = l u * ((m : ℝ) * (v - u)) := by ring
    exact le_of_mul_le_mul_left hfinal hlu
  have hcq : Δ * q * (4 * S - 1) ≤ 4 * S * m * (v - u) := by
    have hstep1 : 4 * S * ω * q < Δ * q := mul_lt_mul_of_pos_right h4Sw hqpos
    have hstep2 : 4 * S * ((Δ - ω) * q) ≤ 4 * S * ((m : ℝ) * (v - u)) :=
      mul_le_mul_of_nonneg_left hθle (by positivity)
    nlinarith [hstep1, hstep2]
  set β : ℝ := max (Δ / (v - u) - m / q) 0 with hβdef
  have hβ0 : 0 ≤ β := le_max_right _ _
  have hβge : Δ / (v - u) - m / q ≤ β := le_max_left _ _
  have hβq : β * q * (4 * S - 1) ≤ m := by
    rcases max_cases (Δ / (v - u) - m / q) 0 with ⟨he, _⟩ | ⟨he, _⟩
    · have hexp : (Δ / (v - u) - m / q) * q = Δ * q / (v - u) - m := by
        field_simp
        try ring
      rw [hβdef, he, hexp]
      have hkey : Δ * q / (v - u) * (4 * S - 1) ≤ 4 * S * m := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hep]
        linarith [hcq]
      nlinarith [hkey, hmpos, h4S1]
    · rw [hβdef, he, zero_mul, zero_mul]
      linarith
  have hmass := needleMass_left_le hl hl0 hg hg0 hau huv hvb hlu hluv hgu hgv hm hint
    (q := q) (β := β) hqdef hβ0 hβge
  have hbq0 : (0 : ℝ) ≤ β * q := mul_nonneg hβ0 hqpos.le
  have hEle : Real.exp (β ^ 2 * q ^ 2 / (2 * m))
      ≤ Real.exp ((m : ℝ) / (2 * (4 * S - 1) ^ 2)) := by
    apply Real.exp_le_exp.mpr
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hsq : (β * q * (4 * S - 1)) * (β * q * (4 * S - 1)) ≤ (m : ℝ) * (m : ℝ) :=
      mul_self_le_mul_self (mul_nonneg hbq0 h4S1.le) hβq
    nlinarith [hsq]
  have hRnn : (0 : ℝ) ≤ Real.sqrt (2 * Real.pi / m) := Real.sqrt_nonneg _
  have hAle : (∫ t in a..u, l t ^ m * g t)
      ≤ (l u ^ m * g u) * (Real.exp ((m : ℝ) / (2 * (4 * S - 1) ^ 2))
          * (q * Real.sqrt (2 * Real.pi / m))) := by
    refine hmass.trans (mul_le_mul_of_nonneg_left ?_ hWu.le)
    exact mul_le_mul_of_nonneg_right hEle (by positivity)
  have hminW : (l u ^ m * g u) * Real.exp (-(1 / (4 * S)))
      ≤ min (l u ^ m * g u) (l v ^ m * g v) := by
    refine le_min ?_ ?_
    · have hx : Real.exp (-(1 / (4 * S))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
      nlinarith [hx, hWu]
    · have hWveq : l v ^ m * g v = (l u ^ m * g u) * Real.exp (-ω) := by
        rw [hωdef, neg_sub, Real.exp_sub, Real.exp_log hWu, Real.exp_log hWv]
        field_simp
      rw [hWveq]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hWu.le
      have hwle : ω ≤ 1 / (4 * S) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [hcase', hd1]
      linarith
  have hBge : (v - u) * ((l u ^ m * g u) * Real.exp (-(1 / (4 * S))))
      ≤ ∫ t in u..v, l t ^ m * g t :=
    le_trans (mul_le_mul_of_nonneg_left hminW hep.le)
      (width_mul_min_le_mass hW hW0 hint hau huv.le hvb)
  have hGpos : 0 < Real.exp (-(1 / (4 * S))) := Real.exp_pos _
  have hconst' : (m : ℝ) * Real.sqrt (2 * Real.pi / m)
        * Real.exp ((m : ℝ) / (2 * (4 * S - 1) ^ 2))
      ≤ (4 * S - 1) * Real.exp (-(1 / (4 * S))) := by
    have hconst := kls38_constant_bound hm
    rw [Real.exp_add] at hconst
    have hz2pos : 0 < Real.exp (1 / (4 * S)) := Real.exp_pos _
    have hneg : Real.exp (-(1 / (4 * S))) = 1 / Real.exp (1 / (4 * S)) := by
      rw [Real.exp_neg]; ring
    rw [hneg, mul_one_div, le_div_iff₀ hz2pos]
    calc (m : ℝ) * Real.sqrt (2 * Real.pi / m)
            * Real.exp ((m : ℝ) / (2 * (4 * S - 1) ^ 2)) * Real.exp (1 / (4 * S))
        = (m : ℝ) * Real.sqrt (2 * Real.pi / m)
            * (Real.exp ((m : ℝ) / (2 * (4 * S - 1) ^ 2)) * Real.exp (1 / (4 * S))) := by ring
      _ ≤ 4 * S - 1 := hconst
  -- assemble, division-free
  have hfin : (4 * S - 1) * (densDist g u v * ∫ t in a..u, l t ^ m * g t)
      ≤ (4 * S - 1) * (4 * S * ∫ t in u..v, l t ^ m * g t) := by
    have hWER : (0 : ℝ) ≤ (l u ^ m * g u) * Real.exp ((m : ℝ) / (2 * (4 * S - 1) ^ 2))
        * Real.sqrt (2 * Real.pi / m) := by positivity
    have hstep1 : densDist g u v * (∫ t in a..u, l t ^ m * g t)
        ≤ Δ * ((l u ^ m * g u) * (Real.exp ((m : ℝ) / (2 * (4 * S - 1) ^ 2))
            * (q * Real.sqrt (2 * Real.pi / m)))) :=
      le_trans (mul_le_mul_of_nonneg_right hdΔ hAnn)
        (mul_le_mul_of_nonneg_left hAle (le_trans hd0 hdΔ))
    have hstep2 : (Δ * q * (4 * S - 1)) * ((l u ^ m * g u)
          * Real.exp ((m : ℝ) / (2 * (4 * S - 1) ^ 2)) * Real.sqrt (2 * Real.pi / m))
        ≤ (4 * S * m * (v - u)) * ((l u ^ m * g u)
          * Real.exp ((m : ℝ) / (2 * (4 * S - 1) ^ 2)) * Real.sqrt (2 * Real.pi / m)) :=
      mul_le_mul_of_nonneg_right hcq hWER
    have hstep3 : ((m : ℝ) * Real.sqrt (2 * Real.pi / m)
            * Real.exp ((m : ℝ) / (2 * (4 * S - 1) ^ 2)))
          * (4 * S * (v - u) * (l u ^ m * g u))
        ≤ ((4 * S - 1) * Real.exp (-(1 / (4 * S))))
          * (4 * S * (v - u) * (l u ^ m * g u)) :=
      mul_le_mul_of_nonneg_right hconst' (by positivity)
    have hstep4 : (4 * S - 1) * (4 * S * ((v - u)
          * ((l u ^ m * g u) * Real.exp (-(1 / (4 * S))))))
        ≤ (4 * S - 1) * (4 * S * ∫ t in u..v, l t ^ m * g t) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBge (by positivity)) h4S1.le
    calc (4 * S - 1) * (densDist g u v * ∫ t in a..u, l t ^ m * g t)
        ≤ (4 * S - 1) * (Δ * ((l u ^ m * g u)
            * (Real.exp ((m : ℝ) / (2 * (4 * S - 1) ^ 2))
              * (q * Real.sqrt (2 * Real.pi / m))))) :=
          mul_le_mul_of_nonneg_left hstep1 h4S1.le
      _ = (Δ * q * (4 * S - 1)) * ((l u ^ m * g u)
            * Real.exp ((m : ℝ) / (2 * (4 * S - 1) ^ 2)) * Real.sqrt (2 * Real.pi / m)) := by
          ring
      _ ≤ (4 * S * m * (v - u)) * ((l u ^ m * g u)
            * Real.exp ((m : ℝ) / (2 * (4 * S - 1) ^ 2)) * Real.sqrt (2 * Real.pi / m)) :=
          hstep2
      _ = ((m : ℝ) * Real.sqrt (2 * Real.pi / m)
            * Real.exp ((m : ℝ) / (2 * (4 * S - 1) ^ 2)))
          * (4 * S * (v - u) * (l u ^ m * g u)) := by ring
      _ ≤ ((4 * S - 1) * Real.exp (-(1 / (4 * S))))
          * (4 * S * (v - u) * (l u ^ m * g u)) := hstep3
      _ = (4 * S - 1) * (4 * S * ((v - u)
            * ((l u ^ m * g u) * Real.exp (-(1 / (4 * S)))))) := by ring
      _ ≤ (4 * S - 1) * (4 * S * ∫ t in u..v, l t ^ m * g t) := hstep4
  exact le_of_mul_le_mul_left hfin h4S1

end Case2

/-! ### Reflection

The configuration `a ≤ u ≤ v ≤ b` is symmetric under `t ↦ a + b − t`, which swaps the two
outer masses and the two cut points and leaves `d_g(u,v)` alone.  That turns the left form
of the `√n` branch into its right form. -/

section Reflect

variable {a b : ℝ}

/-- Concavity is preserved by the reflection `t ↦ a + b − t` of `[a,b]`. -/
theorem concaveOn_reflect {l : ℝ → ℝ} (hl : ConcaveOn ℝ (Set.Icc a b) l) :
    ConcaveOn ℝ (Set.Icc a b) (fun t => l (a + b - t)) := by
  refine ⟨convex_Icc a b, fun x hx y hy p r hp hr hpr => ?_⟩
  have hx' : a + b - x ∈ Set.Icc a b := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hy' : a + b - y ∈ Set.Icc a b := ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have h := hl.2 hx' hy' hp hr hpr
  have heq : p • (a + b - x) + r • (a + b - y) = a + b - (p • x + r • y) := by
    simp only [smul_eq_mul]
    linear_combination (a + b) * hpr
  rwa [heq] at h

/-- Log-concavity is preserved by the reflection `t ↦ a + b − t` of `[a,b]`. -/
theorem logConcaveOn_reflect {g : ℝ → ℝ} (hg : LogConcaveOn (Set.Icc a b) g) :
    LogConcaveOn (Set.Icc a b) (fun t => g (a + b - t)) := by
  refine ⟨convex_Icc a b, fun x hx y hy p r hp hr hpr => ?_⟩
  have hx' : a + b - x ∈ Set.Icc a b := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hy' : a + b - y ∈ Set.Icc a b := ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have h := hg.2 hx' hy' hp hr hpr
  have heq : p • (a + b - x) + r • (a + b - y) = a + b - (p • x + r • y) := by
    simp only [smul_eq_mul]
    linear_combination (a + b) * hpr
  rwa [heq] at h

end Reflect

/-! ### The right form of the `√n` branch -/

section Case2Right

/-- **The `√n` branch of `(1d-1)`, right form** — `Arlib.kls38_case2_left` reflected. -/
theorem kls38_case2_right {a b u v : ℝ} {l g : ℝ → ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hl : ConcaveOn ℝ (Set.Icc a b) l) (hl0 : ∀ s ∈ Set.Icc a b, 0 ≤ l s)
    (hg : LogConcaveOn (Set.Icc a b) g) (hg0 : ∀ s ∈ Set.Icc a b, 0 ≤ g s)
    (hint : IntervalIntegrable (fun t => l t ^ m * g t) volume a b)
    (hau : a ≤ u) (huv : u < v) (hvb : v ≤ b)
    (hguv : g u ≤ g v) (hgu : 0 < g u) (hlu : 0 < l u) (hlv : 0 < l v)
    (hcase : 4 * Real.sqrt ((m : ℝ) + 1) * (l v ^ m * g v - l u ^ m * g u)
      < densDist g u v * (l u ^ m * g u)) :
    densDist g u v * (∫ t in v..b, l t ^ m * g t)
      ≤ 4 * Real.sqrt ((m : ℝ) + 1) * ∫ t in u..v, l t ^ m * g t := by
  have hab : a ≤ b := hau.trans (huv.le.trans hvb)
  set L : ℝ → ℝ := fun t => l (a + b - t) with hL
  set G : ℝ → ℝ := fun t => g (a + b - t) with hG
  have hmemrefl : ∀ t ∈ Set.Icc a b, a + b - t ∈ Set.Icc a b :=
    fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hLc : ConcaveOn ℝ (Set.Icc a b) L := concaveOn_reflect hl
  have hL0 : ∀ s ∈ Set.Icc a b, 0 ≤ L s := fun s hs => hl0 _ (hmemrefl s hs)
  have hGc : LogConcaveOn (Set.Icc a b) G := logConcaveOn_reflect hg
  have hG0 : ∀ s ∈ Set.Icc a b, 0 ≤ G s := fun s hs => hg0 _ (hmemrefl s hs)
  have hintR : IntervalIntegrable (fun t => L t ^ m * G t) volume a b := by
    have h := hint.comp_sub_left (a + b)
    have he1 : a + b - a = b := by ring
    have he2 : a + b - b = a := by ring
    rw [he1, he2] at h
    exact h.symm
  have hval : ∀ t : ℝ, L t ^ m * G t = l (a + b - t) ^ m * g (a + b - t) := fun _ => rfl
  -- reflected cut points
  have h1 : a ≤ a + b - v := by linarith
  have h2 : a + b - v < a + b - u := by linarith
  have h3 : a + b - u ≤ b := by linarith
  have hGu : G (a + b - v) = g v := by rw [hG]; norm_num
  have hGv : G (a + b - u) = g u := by rw [hG]; norm_num
  have hLu : L (a + b - v) = l v := by rw [hL]; norm_num
  have hLv : L (a + b - u) = l u := by rw [hL]; norm_num
  have hdd : densDist G (a + b - v) (a + b - u) = densDist g u v := by
    rw [densDist, densDist, hGu, hGv, abs_sub_comm, max_comm]
  have hcase' : 4 * Real.sqrt ((m : ℝ) + 1)
      * (L (a + b - v) ^ m * G (a + b - v) - L (a + b - u) ^ m * G (a + b - u))
      < densDist G (a + b - v) (a + b - u) * (L (a + b - u) ^ m * G (a + b - u)) := by
    rw [hGu, hGv, hLu, hLv, hdd]
    exact hcase
  have hmain := kls38_case2_left hm hLc hL0 hGc hG0 hintR h1 h2 h3
    (by rw [hGu, hGv]; exact hguv) (by rw [hGv]; exact hgu)
    (by rw [hLu]; exact hlv) (by rw [hLv]; exact hlu) hcase'
  rw [hdd] at hmain
  -- translate the two integrals back
  have hIleft : (∫ t in a..(a + b - v), L t ^ m * G t) = ∫ t in v..b, l t ^ m * g t := by
    have h := intervalIntegral.integral_comp_sub_left (a := a) (b := a + b - v)
      (fun x : ℝ => l x ^ m * g x) (a + b)
    rw [show a + b - (a + b - v) = v by ring, show a + b - a = b by ring] at h
    exact h
  have hImid : (∫ t in (a + b - v)..(a + b - u), L t ^ m * G t)
      = ∫ t in u..v, l t ^ m * g t := by
    have h := intervalIntegral.integral_comp_sub_left (a := a + b - v) (b := a + b - u)
      (fun x : ℝ => l x ^ m * g x) (a + b)
    rw [show a + b - (a + b - v) = v by ring, show a + b - (a + b - u) = u by ring] at h
    exact h
  rw [hIleft, hImid] at hmain
  exact hmain

end Case2Right

/-! ### `(1d-1)` -/

section Main

set_option maxHeartbeats 1000000 in
/-- **Cousins–Vempala's inequality `(1d-1)`** (`1409.6011/vol3_journal.tex:498`), for a
**concave** profile.

For `ℓ ≥ 0` concave and `g ≥ 0` log-concave on `[a,b]`, `n ≥ 1` and `a ≤ u ≤ v ≤ b`,

  `d_g(u,v) · (∫_a^u ℓ^{n−1}g)(∫_v^b ℓ^{n−1}g)
      ≤ 4√n · (∫_a^b ℓ^{n−1}g)(∫_u^v ℓ^{n−1}g)`,

which is `(1d-1)` written without dividing by `4√n`.  Affineness of `ℓ` is never used. -/
theorem kls38_concave {n : ℕ} (hn : 0 < n) {a b u v : ℝ} {l g : ℝ → ℝ}
    (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b)
    (hg0 : ∀ t ∈ Set.Icc a b, 0 ≤ g t) (hgc : LogConcaveOn (Set.Icc a b) g)
    (hl0 : ∀ t ∈ Set.Icc a b, 0 ≤ l t) (hlc : ConcaveOn ℝ (Set.Icc a b) l)
    (hint : IntervalIntegrable (fun t => l t ^ (n - 1) * g t) volume a b) :
    densDist g u v * ((∫ t in a..u, l t ^ (n - 1) * g t)
        * ∫ t in v..b, l t ^ (n - 1) * g t)
      ≤ 4 * Real.sqrt n * ((∫ t in a..b, l t ^ (n - 1) * g t)
        * ∫ t in u..v, l t ^ (n - 1) * g t) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hint ⊢
  rw [show ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 by push_cast; ring]
  set S : ℝ := Real.sqrt ((m : ℝ) + 1) with hSdef
  have hS1 : (1 : ℝ) ≤ S := by
    have hcast : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have h : Real.sqrt 1 ≤ Real.sqrt ((m : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    rw [Real.sqrt_one] at h
    rw [hSdef]
    exact h
  have hSpos : 0 < S := by linarith
  have hub : u ≤ b := huv.trans hvb
  have hav : a ≤ v := hau.trans huv
  have hW : LogConcaveOn (Set.Icc a b) (fun t => l t ^ m * g t) :=
    logConcaveOn_pow_mul_of_concaveOn hlc (fun _ hx => hl0 _ hx) hgc (fun _ hx => hg0 _ hx) m
  have hW0 : ∀ t ∈ Set.Icc a b, 0 ≤ l t ^ m * g t :=
    fun t ht => mul_nonneg (pow_nonneg (hl0 t ht) m) (hg0 t ht)
  have hA : (0 : ℝ) ≤ ∫ t in a..u, l t ^ m * g t :=
    intervalIntegral.integral_nonneg hau fun t ht => hW0 t ⟨ht.1, ht.2.trans hub⟩
  have hB : (0 : ℝ) ≤ ∫ t in u..v, l t ^ m * g t :=
    intervalIntegral.integral_nonneg huv fun t ht => hW0 t ⟨hau.trans ht.1, ht.2.trans hvb⟩
  have hC : (0 : ℝ) ≤ ∫ t in v..b, l t ^ m * g t :=
    intervalIntegral.integral_nonneg hvb fun t ht => hW0 t ⟨hav.trans ht.1, ht.2⟩
  have hsplit : (∫ t in a..u, l t ^ m * g t) + (∫ t in u..v, l t ^ m * g t)
      + (∫ t in v..b, l t ^ m * g t) = ∫ t in a..b, l t ^ m * g t := by
    rw [intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_of_subinterval hint le_rfl hau hub)
        (intervalIntegrable_of_subinterval hint hau huv hvb),
      intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_of_subinterval hint le_rfl hav hvb)
        (intervalIntegrable_of_subinterval hint hav hvb le_rfl)]
  have hd0 : 0 ≤ densDist g u v :=
    div_nonneg (abs_nonneg _) (le_max_of_le_left (hg0 u ⟨hau, hub⟩))
  -- it suffices to bound one of the two outer masses
  have hred : ((densDist g u v * (∫ t in a..u, l t ^ m * g t)
          ≤ 4 * S * ∫ t in u..v, l t ^ m * g t) ∨
        (densDist g u v * (∫ t in v..b, l t ^ m * g t)
          ≤ 4 * S * ∫ t in u..v, l t ^ m * g t)) →
      densDist g u v * ((∫ t in a..u, l t ^ m * g t) * ∫ t in v..b, l t ^ m * g t)
        ≤ 4 * S * ((∫ t in a..b, l t ^ m * g t) * ∫ t in u..v, l t ^ m * g t) := by
    have h4SB : (0 : ℝ) ≤ 4 * S * ∫ t in u..v, l t ^ m * g t :=
      mul_nonneg (by positivity) hB
    have hAT : (∫ t in a..u, l t ^ m * g t) ≤ ∫ t in a..b, l t ^ m * g t := by linarith
    have hCT : (∫ t in v..b, l t ^ m * g t) ≤ ∫ t in a..b, l t ^ m * g t := by linarith
    rintro (h | h)
    · calc densDist g u v * ((∫ t in a..u, l t ^ m * g t) * ∫ t in v..b, l t ^ m * g t)
          = densDist g u v * (∫ t in a..u, l t ^ m * g t) * ∫ t in v..b, l t ^ m * g t := by
            ring
        _ ≤ (4 * S * ∫ t in u..v, l t ^ m * g t) * ∫ t in v..b, l t ^ m * g t :=
            mul_le_mul_of_nonneg_right h hC
        _ ≤ (4 * S * ∫ t in u..v, l t ^ m * g t) * ∫ t in a..b, l t ^ m * g t :=
            mul_le_mul_of_nonneg_left hCT h4SB
        _ = 4 * S * ((∫ t in a..b, l t ^ m * g t) * ∫ t in u..v, l t ^ m * g t) := by ring
    · calc densDist g u v * ((∫ t in a..u, l t ^ m * g t) * ∫ t in v..b, l t ^ m * g t)
          = densDist g u v * (∫ t in v..b, l t ^ m * g t) * ∫ t in a..u, l t ^ m * g t := by
            ring
        _ ≤ (4 * S * ∫ t in u..v, l t ^ m * g t) * ∫ t in a..u, l t ^ m * g t :=
            mul_le_mul_of_nonneg_right h hA
        _ ≤ (4 * S * ∫ t in u..v, l t ^ m * g t) * ∫ t in a..b, l t ^ m * g t :=
            mul_le_mul_of_nonneg_left hAT h4SB
        _ = 4 * S * ((∫ t in a..b, l t ^ m * g t) * ∫ t in u..v, l t ^ m * g t) := by ring
  refine hred ?_
  -- `m = 0`: the weight is `g` itself
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [pow_zero, one_mul] at hint hA hB hC ⊢
    have hgu : 0 ≤ g u := hg0 u ⟨hau, hub⟩
    have hgv : 0 ≤ g v := hg0 v ⟨hav, hvb⟩
    rcases le_total (g v) (g u) with hle | hle
    · right
      have hstep : densDist g u v * (∫ t in v..b, g t) ≤ ∫ t in u..v, g t := by
        rcases eq_or_lt_of_le hgu with hz | hpos
        · have hz0 : densDist g u v = 0 := by
            rw [densDist, ← hz, le_antisymm (hle.trans hz.symm.le) hgv]; norm_num
          rw [hz0, zero_mul]; exact hB
        · have hdeq : densDist g u v = (g u - g v) / g u := by
            rw [densDist, max_eq_left hle, abs_of_nonneg (by linarith)]
          rw [hdeq, div_mul_eq_mul_div, div_le_iff₀ hpos]
          nlinarith [massRight_sub_mul_le hgc hg0 hint hau huv hvb, hB, hle]
      nlinarith [hstep, hB, hS1]
    · left
      have hstep : densDist g u v * (∫ t in a..u, g t) ≤ ∫ t in u..v, g t := by
        rcases eq_or_lt_of_le hgv with hz | hpos
        · have hz0 : densDist g u v = 0 := by
            rw [densDist, ← hz, le_antisymm (hle.trans hz.symm.le) hgu]; norm_num
          rw [hz0, zero_mul]; exact hB
        · have hdeq : densDist g u v = (g v - g u) / g v := by
            rw [densDist, max_eq_right hle, abs_of_nonpos (by linarith), neg_sub]
          rw [hdeq, div_mul_eq_mul_div, div_le_iff₀ hpos]
          nlinarith [massLeft_sub_mul_le hgc hg0 hint hau huv hvb, hB, hle]
      nlinarith [hstep, hB, hS1]
  -- `m ≥ 1`
  rcases eq_or_lt_of_le huv with rfl | huv'
  · left
    rw [densDist_self, zero_mul]
    exact mul_nonneg (by positivity) hB
  by_cases hAz : (∫ t in a..u, l t ^ m * g t) = 0
  · left; rw [hAz, mul_zero]; exact mul_nonneg (by positivity) hB
  by_cases hCz : (∫ t in v..b, l t ^ m * g t) = 0
  · right; rw [hCz, mul_zero]; exact mul_nonneg (by positivity) hB
  -- both outer masses are positive, so the weight is positive at both cut points
  have hzeroA : (∀ t ∈ Set.Icc a u, l t ^ m * g t = 0) →
      (∫ t in a..u, l t ^ m * g t) = 0 := by
    intro h
    have hcong : (∫ t in a..u, l t ^ m * g t) = ∫ _t in a..u, (0 : ℝ) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hau] at ht
      exact h t ht
    simpa using hcong
  have hzeroA' : (∀ t ∈ Set.Icc a v, l t ^ m * g t = 0) →
      (∫ t in a..u, l t ^ m * g t) = 0 := fun h =>
    hzeroA fun t ht => h t ⟨ht.1, ht.2.trans huv⟩
  have hzeroC' : (∀ t ∈ Set.Icc v b, l t ^ m * g t = 0) →
      (∫ t in v..b, l t ^ m * g t) = 0 := by
    intro h
    have hcong : (∫ t in v..b, l t ^ m * g t) = ∫ _t in v..b, (0 : ℝ) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hvb] at ht
      exact h t ht
    simpa using hcong
  have hzeroC : (∀ t ∈ Set.Icc u b, l t ^ m * g t = 0) →
      (∫ t in v..b, l t ^ m * g t) = 0 := fun h =>
    hzeroC' fun t ht => h t ⟨huv.trans ht.1, ht.2⟩
  have hWu : 0 < l u ^ m * g u := by
    rcases eq_or_lt_of_le (hW0 u ⟨hau, hub⟩) with hz | h
    · rcases logConcaveOn_zero_side hW hW0 hau hub hz.symm with hleft | hright
      · exact absurd (hzeroA hleft) hAz
      · exact absurd (hzeroC hright) hCz
    · exact h
  have hWv : 0 < l v ^ m * g v := by
    rcases eq_or_lt_of_le (hW0 v ⟨hav, hvb⟩) with hz | h
    · rcases logConcaveOn_zero_side hW hW0 hav hvb hz.symm with hleft | hright
      · exact absurd (hzeroA' hleft) hAz
      · exact absurd (hzeroC' hright) hCz
    · exact h
  have hgu : 0 < g u := by
    rcases eq_or_lt_of_le (hg0 u ⟨hau, hub⟩) with hz | h
    · rw [← hz, mul_zero] at hWu; exact absurd hWu (lt_irrefl 0)
    · exact h
  have hgv : 0 < g v := by
    rcases eq_or_lt_of_le (hg0 v ⟨hav, hvb⟩) with hz | h
    · rw [← hz, mul_zero] at hWv; exact absurd hWv (lt_irrefl 0)
    · exact h
  have hlu : 0 < l u := by
    rcases eq_or_lt_of_le (hl0 u ⟨hau, hub⟩) with hz | h
    · rw [← hz, zero_pow (by omega : m ≠ 0), zero_mul] at hWu
      exact absurd hWu (lt_irrefl 0)
    · exact h
  have hlv : 0 < l v := by
    rcases eq_or_lt_of_le (hl0 v ⟨hav, hvb⟩) with hz | h
    · rw [← hz, zero_pow (by omega : m ≠ 0), zero_mul] at hWv
      exact absurd hWv (lt_irrefl 0)
    · exact h
  rcases le_total (g v) (g u) with hgle | hgle
  · by_cases hcase : densDist g u v * (l v ^ m * g v)
        ≤ 4 * S * (l u ^ m * g u - l v ^ m * g v)
    · right
      have hmr := massRight_sub_mul_le hW hW0 hint hau huv hvb
      have hkey : densDist g u v * (∫ t in v..b, l t ^ m * g t) * (l v ^ m * g v)
          ≤ 4 * S * (∫ t in u..v, l t ^ m * g t) * (l v ^ m * g v) := by
        calc densDist g u v * (∫ t in v..b, l t ^ m * g t) * (l v ^ m * g v)
            = densDist g u v * (l v ^ m * g v) * (∫ t in v..b, l t ^ m * g t) := by ring
          _ ≤ 4 * S * (l u ^ m * g u - l v ^ m * g v) * (∫ t in v..b, l t ^ m * g t) :=
              mul_le_mul_of_nonneg_right hcase hC
          _ = 4 * S * ((l u ^ m * g u - l v ^ m * g v) * (∫ t in v..b, l t ^ m * g t)) := by
              ring
          _ ≤ 4 * S * ((l v ^ m * g v) * ∫ t in u..v, l t ^ m * g t) :=
              mul_le_mul_of_nonneg_left hmr (by positivity)
          _ = 4 * S * (∫ t in u..v, l t ^ m * g t) * (l v ^ m * g v) := by ring
      exact le_of_mul_le_mul_right hkey hWv
    · rw [not_le] at hcase
      left
      exact kls38_case2_left hm hlc hl0 hgc hg0 hint hau huv' hvb hgle hgv hlu hlv hcase
  · by_cases hcase : densDist g u v * (l u ^ m * g u)
        ≤ 4 * S * (l v ^ m * g v - l u ^ m * g u)
    · left
      have hml := massLeft_sub_mul_le hW hW0 hint hau huv hvb
      have hkey : densDist g u v * (∫ t in a..u, l t ^ m * g t) * (l u ^ m * g u)
          ≤ 4 * S * (∫ t in u..v, l t ^ m * g t) * (l u ^ m * g u) := by
        calc densDist g u v * (∫ t in a..u, l t ^ m * g t) * (l u ^ m * g u)
            = densDist g u v * (l u ^ m * g u) * (∫ t in a..u, l t ^ m * g t) := by ring
          _ ≤ 4 * S * (l v ^ m * g v - l u ^ m * g u) * (∫ t in a..u, l t ^ m * g t) :=
              mul_le_mul_of_nonneg_right hcase hA
          _ = 4 * S * ((l v ^ m * g v - l u ^ m * g u) * (∫ t in a..u, l t ^ m * g t)) := by
              ring
          _ ≤ 4 * S * ((l u ^ m * g u) * ∫ t in u..v, l t ^ m * g t) :=
              mul_le_mul_of_nonneg_left hml (by positivity)
          _ = 4 * S * (∫ t in u..v, l t ^ m * g t) * (l u ^ m * g u) := by ring
      exact le_of_mul_le_mul_right hkey hWu
    · rw [not_le] at hcase
      right
      exact kls38_case2_right hm hlc hl0 hgc hg0 hint hau huv' hvb hgle hgu hlu hlv hcase

end Main

/-! ### The affine form, and non-vacuity -/

section Affine

/-- **`(1d-1)` for an affine profile**, i.e. exactly as Cousins–Vempala state it and exactly
in the shape of the `h1d1` binder of `Arlib.gaussianRestricted_isoperimetry`.  An affine
function is concave, so this is `Arlib.kls38_concave` with no extra work; the concave form
is the one that can actually be wired to this repository's localization output. -/
theorem kls38_affine {n : ℕ} (hn : 0 < n) : ∀ (g l : ℝ → ℝ) (α β u v : ℝ), α ≤ u → u ≤ v →
    v ≤ β → (∀ t ∈ Set.Icc α β, 0 ≤ g t) → LogConcaveOn (Set.Icc α β) g →
    (∀ t ∈ Set.Icc α β, 0 ≤ l t) → (∃ c₀ c₁ : ℝ, ∀ t, l t = c₀ + c₁ * t) →
    IntervalIntegrable (fun t => l t ^ (n - 1) * g t) volume α β →
    densDist g u v * ((∫ t in α..u, l t ^ (n - 1) * g t) *
          ∫ t in v..β, l t ^ (n - 1) * g t)
      ≤ 4 * Real.sqrt n * ((∫ t in α..β, l t ^ (n - 1) * g t) *
          ∫ t in u..v, l t ^ (n - 1) * g t) := by
  intro g l α β u v hαu huv hvβ hg0 hgc hl0 haff hint
  obtain ⟨c₀, c₁, hleq⟩ := haff
  have hlc : ConcaveOn ℝ (Set.Icc α β) l := by
    refine ⟨convex_Icc α β, fun x _ y _ p r hp hr hpr => ?_⟩
    simp only [hleq, smul_eq_mul]
    have heq : p * (c₀ + c₁ * x) + r * (c₀ + c₁ * y) = c₀ + c₁ * (p * x + r * y) := by
      linear_combination c₀ * hpr
    linarith
  exact kls38_concave hn hαu huv hvβ hg0 hgc hl0 hlc hint

/-- Temporary compatibility probe. -/
theorem kls38_h1d1_probe {n : ℕ} (hn : 0 < n) :
    ∀ (g l : ℝ → ℝ) (α β u v : ℝ), α ≤ u → u ≤ v → v ≤ β →
      (∀ t ∈ Set.Icc α β, 0 ≤ g t) → LogConcaveOn (Set.Icc α β) g →
      (∀ t ∈ Set.Icc α β, 0 ≤ l t) → (∃ c₀ c₁ : ℝ, ∀ t, l t = c₀ + c₁ * t) →
      IntervalIntegrable (fun t => l t ^ (n - 1) * g t) volume α β →
      densDist g u v * ((∫ t in α..u, l t ^ (n - 1) * g t) *
            (∫ t in v..β, l t ^ (n - 1) * g t))
        ≤ 4 * Real.sqrt n * ((∫ t in α..β, l t ^ (n - 1) * g t) *
            (∫ t in u..v, l t ^ (n - 1) * g t)) := kls38_affine hn

end Affine

section MainWitness

/-- **Non-vacuity of `Arlib.kls38_concave`.**

`n = 2`, profile `ℓ t = 1 − t²` (concave, and *not* affine), density `g t = 1 − t`
(log-concave and non-constant, so `d_g(u,v) = 1/3 > 0`), on `[0,1]` cut at `u = 1/4`,
`v = 1/2`.  Every hypothesis holds simultaneously, the left-hand side is strictly positive
(`8567/1769472 ≈ 0.00484`), and the inequality is strict (the right-hand side exceeds
`0.31`).  So `(1d-1)` as proved here is not the vacuous `0 ≤ something`. -/
theorem kls38_concave_witness :
    ∃ (n : ℕ) (l g : ℝ → ℝ) (a b u v : ℝ),
      0 < n ∧ a ≤ u ∧ u ≤ v ∧ v ≤ b ∧
        (∀ t ∈ Set.Icc a b, 0 ≤ g t) ∧ LogConcaveOn (Set.Icc a b) g ∧
        (∀ t ∈ Set.Icc a b, 0 ≤ l t) ∧ ConcaveOn ℝ (Set.Icc a b) l ∧
        (¬ ∃ c₀ c₁ : ℝ, ∀ t : ℝ, l t = c₀ + c₁ * t) ∧
        IntervalIntegrable (fun t => l t ^ (n - 1) * g t) volume a b ∧
        0 < densDist g u v * ((∫ t in a..u, l t ^ (n - 1) * g t)
              * ∫ t in v..b, l t ^ (n - 1) * g t) ∧
        densDist g u v * ((∫ t in a..u, l t ^ (n - 1) * g t)
              * ∫ t in v..b, l t ^ (n - 1) * g t)
          < 4 * Real.sqrt n * ((∫ t in a..b, l t ^ (n - 1) * g t)
              * ∫ t in u..v, l t ^ (n - 1) * g t) := by
  have hcont : Continuous (fun t : ℝ => (1 - t ^ 2) ^ ((2 : ℕ) - 1) * (1 - t)) := by fun_prop
  have key : ∀ p q : ℝ, (∫ t in p..q, (1 - t ^ 2) ^ ((2 : ℕ) - 1) * (1 - t))
      = (q - q ^ 2 / 2 - q ^ 3 / 3 + q ^ 4 / 4) - (p - p ^ 2 / 2 - p ^ 3 / 3 + p ^ 4 / 4) := by
    intro p q
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => t - t ^ 2 / 2 - t ^ 3 / 3 + t ^ 4 / 4) (fun x _ => ?_)
      (hcont.intervalIntegrable _ _)
    have e1 : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
    have e2 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) ((2 : ℕ) * x ^ (2 - 1) / 2) x :=
      (hasDerivAt_pow 2 x).div_const 2
    have e3 : HasDerivAt (fun t : ℝ => t ^ 3 / 3) ((3 : ℕ) * x ^ (3 - 1) / 3) x :=
      (hasDerivAt_pow 3 x).div_const 3
    have e4 : HasDerivAt (fun t : ℝ => t ^ 4 / 4) ((4 : ℕ) * x ^ (4 - 1) / 4) x :=
      (hasDerivAt_pow 4 x).div_const 4
    have h := ((e1.sub e2).sub e3).add e4
    have hfun : (((fun t : ℝ => t) - fun t : ℝ => t ^ 2 / 2) - fun t : ℝ => t ^ 3 / 3)
          + (fun t : ℝ => t ^ 4 / 4)
        = fun t : ℝ => t - t ^ 2 / 2 - t ^ 3 / 3 + t ^ 4 / 4 := by
      funext t
      simp only [Pi.add_apply, Pi.sub_apply]
    rw [hfun] at h
    convert h using 1
    push_cast
    ring
  have hconcg : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun t : ℝ => 1 - t) := by
    refine ⟨convex_Icc 0 1, fun x _ y _ p r hp hr hpr => ?_⟩
    simp only [smul_eq_mul]
    have heq : p * (1 - x) + r * (1 - y) = 1 - (p * x + r * y) := by
      linear_combination hpr
    linarith
  have hsq2 : (1.4 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1.4 : ℝ) = Real.sqrt (1.4 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hdd : densDist (fun t : ℝ => 1 - t) (1 / 4) (1 / 2) = 1 / 3 := by
    rw [densDist]; norm_num
  refine ⟨2, fun t => 1 - t ^ 2, fun t => 1 - t, 0, 1, 1 / 4, 1 / 2, by norm_num, by norm_num,
    by norm_num, by norm_num, fun t ht => by linarith [ht.2],
    logConcaveOn_of_concaveOn hconcg (fun t ht => by linarith [ht.2]),
    fun t ht => by nlinarith [ht.1, ht.2], concaveOn_one_sub_sq_Icc, one_sub_sq_not_affine_Icc,
    hcont.intervalIntegrable _ _, ?_, ?_⟩
  · simp only [key, hdd]; norm_num
  · simp only [key, hdd]
    norm_num
    nlinarith [hsq2]

end MainWitness

/-! ### Axiom audit

Every declaration in this file must depend on exactly
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms massRight_sub_mul_le
#print axioms massLeft_sub_mul_le
#print axioms densDist_mul_mass_le
#print axioms logRatio_mul_mass_le
#print axioms logConcaveOn_pow_mul_of_concaveOn
#print axioms densDist_profile_mul_mass_le
#print axioms concaveOn_one_sub_sq_Icc
#print axioms one_sub_sq_not_affine_Icc
#print axioms densDist_profile_mul_mass_witness
#print axioms one_sub_le_exp_neg_sub_sq_half
#print axioms one_sub_pow_le_exp
#print axioms integral_exp_linear_sub_mul_sq
#print axioms integrable_exp_linear_sub_mul_sq
#print axioms concaveOn_le_chord_left
#print axioms logConcaveOn_le_exp_left
#print axioms needleWeight_le_gaussian_left
#print axioms needleMass_left_le
#print axioms logConcaveOn_min_le
#print axioms width_mul_min_le_mass
#print axioms logConcaveOn_zero_side
#print axioms sqrt_succ_ge
#print axioms kls38_constant_bound
#print axioms kls38_case2_left
#print axioms concaveOn_reflect
#print axioms logConcaveOn_reflect
#print axioms kls38_case2_right
#print axioms kls38_concave
#print axioms kls38_affine
#print axioms kls38_concave_witness

end Arlib
