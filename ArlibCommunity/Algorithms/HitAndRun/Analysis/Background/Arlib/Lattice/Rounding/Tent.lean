/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The rounding displacement in one coordinate

Kannan–Vempala, *Sampling Lattice Points* (STOC '97), define the randomized
rounding `rnd` used throughout their Theorem 2 but state no construction. The
standard one — and the one whose properties the analysis actually uses — is
**independent coordinatewise randomized rounding**:

  `xₖ = ⌊pₖ⌋ + Bernoulli(pₖ − ⌊pₖ⌋)`.

Fix a lattice point `x` and ask for the density of `p` in one coordinate given
that it rounds to `x`. Writing `u = p − x`: for `u ∈ [0,1)` we have `⌊p⌋ = x` and
the Bernoulli must fail, probability `1 − u`; for `u ∈ [−1,0)` we have
`⌊p⌋ = x − 1` and it must fire, probability `1 + u`. So the density is the
**triangular ("tent") density** `1 − |u|` on `[−1,1]`.

That single function carries every property the rounding analysis needs of the
displacement:
it is a probability density (`Arlib.Lattice.Rounding.integral_tent`), supported in `[−1,1]`
(`Arlib.Lattice.Rounding.tent_eq_zero_of_one_le`), and has **mean zero** (`Arlib.Lattice.Rounding.integral_id_mul_tent`) — the three hypotheses of the
sub-Gaussian tail bound `Arlib.Probability.rounding_tail_bound`, per coordinate.
Independence across coordinates then comes from taking the product.
-/

namespace Arlib.Lattice.Rounding

open MeasureTheory intervalIntegral

/-- The triangular displacement density `1 − |u|` on `[−1,1]`, zero outside. -/
noncomputable def tent (u : ℝ) : ℝ := max (1 - |u|) 0

theorem tent_nonneg (u : ℝ) : 0 ≤ tent u := le_max_right _ _

theorem tent_of_abs_le {u : ℝ} (h : |u| ≤ 1) : tent u = 1 - |u| := by
  rw [tent, max_eq_left]; linarith

theorem tent_eq_zero_of_one_le {u : ℝ} (h : 1 ≤ |u|) : tent u = 0 := by
  rw [tent, max_eq_right]; linarith

/-- The support of the displacement is `[−1,1]` — this is the `hbdd` hypothesis of
`Arlib.Lattice.Rounding.rounding_tail_bound`. -/
theorem tent_eq_zero_of_notMem {u : ℝ} (h : u ∉ Set.Icc (-1 : ℝ) 1) : tent u = 0 := by
  refine tent_eq_zero_of_one_le ?_
  rcases abs_cases u with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;>
    · by_contra hc
      exact h ⟨by linarith, by linarith⟩

theorem continuous_tent : Continuous tent :=
  (continuous_const.sub continuous_abs).max continuous_const

theorem tent_hasCompactSupport : HasCompactSupport tent := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) ?_
  intro u hu
  exact tent_eq_zero_of_notMem hu

theorem integrable_tent : Integrable tent :=
  continuous_tent.integrable_of_hasCompactSupport tent_hasCompactSupport

/-- A compactly supported integrand's integral over `ℝ` is its integral over the
support interval. -/
private theorem integral_eq_interval {f : ℝ → ℝ}
    (hzero : ∀ u ∉ Set.Icc (-1 : ℝ) 1, f u = 0) :
    ∫ u, f u = ∫ u in (-1 : ℝ)..1, f u := by
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc,
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero]

/-- **`∫ tent = 1`** — the displacement density is a probability density. This is
what makes the product kernel doubly stochastic — see
product kernel. -/
theorem integral_tent : ∫ u, tent u = 1 := by
  rw [integral_eq_interval fun u hu => tent_eq_zero_of_notMem hu,
    ← intervalIntegral.integral_add_adjacent_intervals
      (b := (0 : ℝ)) integrable_tent.intervalIntegrable
      integrable_tent.intervalIntegrable]
  have hlo : ∫ u in (-1 : ℝ)..0, tent u = 1 / 2 := by
    rw [intervalIntegral.integral_congr (g := fun u => 1 + u) ?_]
    · rw [intervalIntegral.integral_add intervalIntegrable_const
        intervalIntegral.intervalIntegrable_id]
      simp; norm_num
    · intro u hu
      rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hu
      rw [tent_of_abs_le (by rw [abs_of_nonpos hu.2]; linarith [hu.1]),
        abs_of_nonpos hu.2]
      ring
  have hhi : ∫ u in (0 : ℝ)..1, tent u = 1 / 2 := by
    rw [intervalIntegral.integral_congr (g := fun u => 1 - u) ?_]
    · rw [intervalIntegral.integral_sub intervalIntegrable_const
        intervalIntegral.intervalIntegrable_id]
      simp; norm_num
    · intro u hu
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
      rw [tent_of_abs_le (by rw [abs_of_nonneg hu.1]; exact hu.2), abs_of_nonneg hu.1]
  rw [hlo, hhi]; norm_num

/-- **`∫ u · tent u = 0`** — the displacement has **mean zero**, by symmetry. This
is the `hmean` hypothesis of `Arlib.Lattice.Rounding.rounding_tail_bound`. -/
theorem integral_id_mul_tent : ∫ u, u * tent u = 0 := by
  have hzero : ∀ u ∉ Set.Icc (-1 : ℝ) 1, u * tent u = 0 := by
    intro u hu; rw [tent_eq_zero_of_notMem hu, mul_zero]
  have hint : Integrable (fun u => u * tent u) := by
    refine (continuous_id.mul continuous_tent).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) ?_
    intro u hu; exact hzero u hu
  rw [integral_eq_interval hzero,
    ← intervalIntegral.integral_add_adjacent_intervals
      (b := (0 : ℝ)) hint.intervalIntegrable hint.intervalIntegrable]
  have hlo : ∫ u in (-1 : ℝ)..0, u * tent u = -(1 / 6) := by
    rw [intervalIntegral.integral_congr (g := fun u => u + u ^ 2) ?_]
    · rw [intervalIntegral.integral_add intervalIntegral.intervalIntegrable_id
        (intervalIntegral.intervalIntegrable_pow 2)]
      simp [integral_pow]; norm_num
    · intro u hu
      rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hu
      show u * tent u = u + u ^ 2
      rw [tent_of_abs_le (by rw [abs_of_nonpos hu.2]; linarith [hu.1]),
        abs_of_nonpos hu.2]
      ring
  have hhi : ∫ u in (0 : ℝ)..1, u * tent u = 1 / 6 := by
    rw [intervalIntegral.integral_congr (g := fun u => u - u ^ 2) ?_]
    · rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
        (intervalIntegral.intervalIntegrable_pow 2)]
      simp [integral_pow]; norm_num
    · intro u hu
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
      show u * tent u = u - u ^ 2
      rw [tent_of_abs_le (by rw [abs_of_nonneg hu.1]; exact hu.2), abs_of_nonneg hu.1]
      ring
  rw [hlo, hhi]; norm_num

end Arlib.Lattice.Rounding
