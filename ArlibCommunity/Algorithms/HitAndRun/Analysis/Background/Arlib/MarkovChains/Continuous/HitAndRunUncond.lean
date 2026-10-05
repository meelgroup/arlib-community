/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.ConductanceToTV
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.HitAndRunConductanceParam
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.SphereCap

/-!
# The hit-and-run mixing bound with the Lemma 4.1 overlap constant as a parameter

`Arlib/MarkovChains/Continuous/HitAndRunConductanceParam.lean` freed the Lemma 4.1 overlap
constant in the **conductance** theorem (Theorem 4.2).  This file does the same for the
**mixing** theorem (Theorem 1.1), which is where the constants actually failed to compose:

* What is proved: `Arlib.MarkovChains.tvLe_hitAndRun_lemma41_uncond` (`SphereCap.lean:896`)
  is Lemma 4.1 with no unproved hypothesis, at overlap constant `1 − 1/8000`, for `n ≥ 1100`.
* What the consumers demanded: `hLem41` binders hardcoded at `1 − 1/500`, a constant
  `HitAndRunOverlap.lean`'s module docstring shows the corrected proof cannot reach (two of
  the three bounds in the paper's proof are wrong in the same direction).
* And the mixing theorem hardcoded not just the constant but the *conductance value*:
  `tvLe_iterate_lazy_hitAndRun` (`ConductanceToTV.lean:372`) demands
  `Φ ≥ r/(2²⁸·n·R)` and a deadline `4·lvThreshold n r R M ε`, both of which are what the
  `1/500` route delivers and neither of which the `1/8000` route can meet.

## What is here

| name | content |
|---|---|
| `lsThreshold_anti` | the deadline `log(8M/ε²)/φ²` is antitone in `φ` |
| `tvLe_iterate_lazy_hitAndRun_param` | Theorem 1.1, lazy hit-and-run, at a **free** `phi`, deadline `4·lsThreshold M phi ε` |
| `tvLe_iterate_lazy_hitAndRun_of_param` | the original recovered at `phi = r/(2²⁸·n·R)` |
| `tvLe_iterate_lazy_hitAndRun_of_param_eq` | `rfl`-check: the recovered statement **is** the original |
| `ofReal_le_conductance_hitAndRun_of_unitBall_param` | `Φ ≥ c/(491520·n·R)` from Lemma 4.1 at `1 − c` |
| `tvLe_iterate_lazy_hitAndRun_unitBall_param` | the unit-inball Theorem 1.1 at a free `c` |
| `tvLe_iterate_lazy_hitAndRun_unitBall_of_param` | the original recovered at `c = 1/500` |
| `tvLe_iterate_lazy_hitAndRun_unitBall_of_param_eq` | `rfl`-check for that one |
| `tvLe_hitAndRun_lemma41_uncond_max` | the proved Lemma 4.1, restated in the `max(F u, F v)` shape the `hLem41` binder uses |
| `tvLe_iterate_lazy_hitAndRun_unitBall_8000` | the instantiation at `c = 1/8000`, deadline `4·2⁶⁴·n²R²·log(8M/ε²)` |

## The constant dependence, exactly

Lemma 4.1 at `1 − c` gives `Φ ≥ c/(245760·n·D) = c/(491520·n·R)` (`D ≤ 2R`), and the deadline
is quadratic in `1/Φ`:

    steps  =  4 · lsThreshold M (c/(491520·n·R)) ε  =  4 · 491520² · n²R²/c² · log(8M/ε²).

At `c = 1/500` this is `4·245760000²·n²R²·log(8M/ε²)`, *shorter* than the original's
`4·lvThreshold n 1 R M ε = 4·2⁵⁶·n²R²·log(8M/ε²)` by the factor `(2²⁸/245760000)² ≈ 1.19`
that the original threw away when it rounded `245760000` up to `2²⁸`.  At `c = 1/8000`, after
rounding `8000·491520 = 3932160000` up to `2³²`, it is `4·2⁶⁴·n²R²·log(8M/ε²)` — exactly
`256 = (8000/500)²` times the original.  The shape `O(n²R²·log(M/ε))` is unchanged.

## What remains

1. **`hIso`** — the paper's Theorem 2.1 (the weighted isoperimetric inequality) in its
   corrected form, carrying the clause `∀ x ∈ K, h x ≤ 1/3` without which it is false
   (`Arlib.not_hIso_two`).  It is a binder in `conductance_hitAndRun_ge`, is carried
   verbatim through `conductance_hitAndRun_ge_param`, and is carried verbatim through every
   theorem here.  It is being attacked separately as `htrans` + `hloc`.
2. **`n ≥ 1100`** — the threshold of `tvLe_hitAndRun_lemma41_uncond`, an artifact of the
   union bound in the spherical-cap estimate (`SphereCap.lean`), not of the statement, which
   is true from `n = 5` on.  It appears in no *mixing* theorem of this file, because
   `hLem41` is still a binder; only the §4 bridge lemma carries it.
3. **`hLem41` itself, and why it is still a binder.**  Besides the binder's own hypotheses,
   `tvLe_hitAndRun_lemma41_uncond` needs `u ≠ v`, the two `hmove`s
   (`hitAndRunProposal K u Set.univ = 1`), and `ha`/`hb` (`chordLow K u v < 0`,
   `1 < chordHigh K u v`).  Two of these are cheap: the `max`-versus-`F(u)` mismatch is
   closed by §4 below, and `u = v` by `Arlib.TVLe.refl` and `Arlib.TVLe.mono`.

   **`ha` and `hb` are not, and they fail at boundary points of every body.**  Let `K` be
   compact convex with nonempty interior, `u ∈ ∂K` and `v ∈ interior K`.  If
   `chordLow K u v < 0`, i.e. `u + t(v − u) ∈ K` for some `t < 0`, then `u` lies on the open
   segment between that point of `K` and the interior point `v`, hence `u ∈ interior K` —
   contradiction.  So `chordLow K u v = 0` and `ha` fails, for every such pair, in every
   dimension, smooth boundary or not.  Since the `hLem41` binder quantifies over *all*
   `u, v ∈ K`, no route through `tvLe_hitAndRun_lemma41_uncond` can discharge it, and a
   theorem carrying `∀ u ∈ K, ∀ v ∈ K, u ≠ v → chordLow K u v < 0` would be vacuous.  None
   is stated here.

   `hmove` fails at boundary points too, though less uniformly: it is the *positive-measure*
   degeneracy of the chord that breaks it, not a single tangent direction.  At a vertex of a
   cube the directions with a nondegenerate chord are the inward cone and its reflection, of
   normalised measure `2^{1−n} < 1`, so the proposal is defective there; at a boundary point
   of a Euclidean ball the tangent directions have measure zero and `hmove` still holds.

   The mathematics is not the obstruction: `HitAndRunConductance.lean`'s module docstring
   (§ *Two places where the formalisation is more careful than the paper*, item 1, lines
   210–217) records that the conductance proof cuts `S₁'`, `S₂'` down to `interior K` and so
   only ever *uses* `hLem41` at interior points, where `hmove` is available from
   `Arlib.hitAndRunProposal_univ_eq_one_of_mem_interior`.  The obstruction is that the binder
   is *stated* over all of `K`.  Weakening it to `interior K` is a one-line change inside
   `conductance_hitAndRun_ge_of_tv`'s statement — in a file this module may not edit — and it
   is what would make `tvLe_iterate_lazy_hitAndRun_unitBall_8000` unconditional in `hLem41`.

So `tvLe_iterate_lazy_hitAndRun_unitBall_8000` is stated with `hLem41` intact, at the
constant `1 − 1/8000` the repository proves, in the style of
`conductance_hitAndRun_ge_2048`/`_34386`: the overlap hypothesis is a binder, not a
discharged fact.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

/-! ## 0. The deadline is antitone in the conductance -/

/-- **A better conductance bound is a shorter deadline.**  `lsThreshold M phi eps =
log(8M/ε²)/phi²` is antitone in `phi` on `phi > 0`, because `log(8M/ε²) ≥ 0` whenever
`M ≥ 1` and `0 < ε ≤ 1` (then `8M/ε² ≥ 8 ≥ 1`).

Both positivity hypotheses are needed: for `M < 1/8` and `ε = 1` the logarithm is negative
and the inequality reverses. -/
theorem lsThreshold_anti {M phi phi' eps : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hphi0 : 0 < phi) (hphi : phi ≤ phi') :
    lsThreshold M phi' eps ≤ lsThreshold M phi eps := by
  have hlog : 0 ≤ Real.log (8 * M / eps ^ 2) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  rw [lsThreshold, lsThreshold]
  gcongr

/-! ## 1. Theorem 1.1 for the lazy hit-and-run walk, at a free conductance -/

/-- **`Arlib.MarkovChains.tvLe_iterate_lazy_hitAndRun` with the conductance value a
parameter.**

The original (`ConductanceToTV.lean:372`) hardcodes `phi = r/(2²⁸·n·R)` — the value Theorem
4.2 delivers *at the paper's Lemma 4.1 constant* `1 − 1/500` — and states the deadline as
`4 · lvThreshold n r R M eps = 4 · 2⁵⁶ · n²R²/r² · log(8M/ε²)`.  Nothing in the proof needs
that particular number: the layer beneath (`tvLe_iterate_lazy_of_exceptional`,
`ConductanceToTV.lean:318`) already carries a free `phi`.  Here it is exposed, with the
deadline in its native form `4 · lsThreshold M phi eps = 4 · log(8M/ε²)/phi²`.

The factor `4` is `conductance_lazy`: laziness halves the conductance exactly, and the
deadline is quadratic in `1/phi`.

Everything mathematical is inherited: reversibility from `isReversible_hitAndRun`, the
spectral hypothesis from `hasNonnegSpectrum_lazy`, non-degeneracy from
`exists_smallSet_uniformOn`.  `hphi` is the only hypothesis with content, and it is now
whatever conductance bound the caller actually holds. -/
theorem tvLe_iterate_lazy_hitAndRun_param {n : ℕ} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKm : MeasurableSet K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    {sigma : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure sigma]
    {phi : ℝ} (hphi0 : 0 < phi) (hphi1 : phi ≤ 1)
    {M eps : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hSm : MeasurableSet S)
    (hS : sigma S ≤ ENNReal.ofReal (eps / 2))
    (hdom : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      sigma (A \ S) ≤ ENNReal.ofReal M * uniformOn volume K A)
    (hphi : ENNReal.ofReal phi ≤ conductance (hitAndRun K) (uniformOn volume K))
    {m : ℕ} (hm : 4 * lsThreshold M phi eps ≤ (m : ℝ)) :
    Arlib.TVLe (iterate (lazy (hitAndRun K)) sigma m) (uniformOn volume K)
      (ENNReal.ofReal eps) := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : IsProbabilityMeasure (uniformOn volume K) :=
    Arlib.isProbabilityMeasure_uniformOn volume hK0 hKtop
  obtain ⟨S0, hS0m, hS0pos, hS0half⟩ := exists_smallSet_uniformOn hn hKm hK0 hKtop
  exact tvLe_iterate_lazy_of_exceptional (isReversible_hitAndRun hKm)
    ⟨S0, hS0m, hS0pos, hS0half⟩ hM hphi0 hphi1 heps0 heps1 hSm hS hdom hphi hm

/-! ## 2. The faithfulness check: the original, recovered at `phi = r/(2²⁸·n·R)` -/

/-- **The original `Arlib.MarkovChains.tvLe_iterate_lazy_hitAndRun`, recovered from the
parametric form.**

The statement is that of `ConductanceToTV.lean:372` verbatim, down to the binder names.  The
proof does **not** invoke the original; it goes through `tvLe_iterate_lazy_hitAndRun_param`
at `phi = r/(2²⁸·n·R)` and re-runs the original's own two arithmetic steps (`0 < phi`,
`phi ≤ 1` from `r ≤ R`, and `lsThreshold_eq_lvThreshold`).

That the two statements are *the same statement* is certified mechanically by
`tvLe_iterate_lazy_hitAndRun_of_param_eq` below, which would not typecheck if any binder
had drifted. -/
theorem tvLe_iterate_lazy_hitAndRun_of_param {n : ℕ} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKm : MeasurableSet K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    {sigma : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure sigma]
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (hrR : r ≤ R)
    {M eps : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hSm : MeasurableSet S)
    (hS : sigma S ≤ ENNReal.ofReal (eps / 2))
    (hdom : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      sigma (A \ S) ≤ ENNReal.ofReal M * Arlib.uniformOn volume K A)
    (hphi : ENNReal.ofReal (r / (2 ^ 28 * (n : ℝ) * R))
      ≤ conductance (hitAndRun K) (Arlib.uniformOn volume K))
    {m : ℕ} (hm : 4 * lvThreshold n r R M eps ≤ (m : ℝ)) :
    Arlib.TVLe (iterate (lazy (hitAndRun K)) sigma m) (Arlib.uniformOn volume K)
      (ENNReal.ofReal eps) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hphi0 : 0 < r / (2 ^ 28 * (n : ℝ) * R) := by positivity
  have hphi1 : r / (2 ^ 28 * (n : ℝ) * R) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  refine tvLe_iterate_lazy_hitAndRun_param hn hKm hK0 hKtop hphi0 hphi1 hM heps0 heps1 hSm hS
    hdom hphi ?_
  rw [lsThreshold_eq_lvThreshold hn hr hR]
  exact hm

/-- **The two statements are literally the same statement.**  `rfl` here compares the *types*
of `tvLe_iterate_lazy_hitAndRun_of_param` and the original
`Arlib.MarkovChains.tvLe_iterate_lazy_hitAndRun`: the equation does not even elaborate
unless every binder — implicit/explicit/instance, name, type — agrees, and definitional
proof irrelevance then closes it.

This is the check the brief calls for.  A parametrisation that silently dropped or weakened a
clause would fail here even though both files build. -/
theorem tvLe_iterate_lazy_hitAndRun_of_param_eq :
    @tvLe_iterate_lazy_hitAndRun_of_param = @tvLe_iterate_lazy_hitAndRun := rfl

/-! ## 3. The unit-inball version, at a free overlap constant

`conductance_hitAndRun_ge_param` (`HitAndRunConductanceParam.lean:110`) gives
`Φ ≥ c/(245760·n·D)` from Lemma 4.1 at `1 − c`.  A body inside a ball of radius `R` has
`D ≤ 2R`, so this reads

    Φ  ≥  c / (491520 · n · R),

and the deadline of §1 at that `phi` is `4·491520²·n²R²/c² · log(8M/ε²)` — the paper's shape
`O(n²R²·log(M/ε))`, with a `1/c²`. -/

/-- **The conductance bound in `R`-form, at a free overlap constant.**  This is
`Arlib.MarkovChains.ofReal_inv_le_conductance_hitAndRun_of_unitBall`
(`HitAndRunMixing.lean:905`) with `1/500` freed to `c`, and with the exact denominator
`491520 = 2·245760` in place of the original's rounding to `2²⁸`.

At `c = 1/500` it says `Φ ≥ 1/(245760000·n·R)`, which is *stronger* than the original's
`Φ ≥ 1/(2²⁸·n·R) = 1/(268435456·n·R)`; the original rounded the denominator up to a power of
two. -/
theorem ofReal_le_conductance_hitAndRun_of_unitBall_param {n : ℕ} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    {z zout : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {R : ℝ} (hR : 0 < R) (hout : K ⊆ Metric.closedBall zout R)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      Arlib.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - c)))
    (hIso : ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))), (∀ x, 0 ≤ h x) →
      (∀ x ∈ K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (crossRatioDist K u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(Arlib.uniformOn volume K)) *
          min (Arlib.uniformOn volume K T₁) (Arlib.uniformOn volume K T₂)
        ≤ Arlib.uniformOn volume K ((K \ T₁) \ T₂)) :
    ENNReal.ofReal (c / (491520 * (n : ℝ) * R))
      ≤ conductance (hitAndRun K) (Arlib.uniformOn volume K) := by
  have hKb : Bornology.IsBounded K := Metric.isBounded_closedBall.subset hout
  have hD : Metric.diam K ≤ 2 * R := by
    refine Metric.diam_le_of_forall_dist_le (by positivity) fun x hx y hy => ?_
    have hx' := Metric.mem_closedBall.1 (hout hx)
    have hy' := Metric.mem_closedBall.1 (hout hy)
    calc dist x y ≤ dist x zout + dist zout y := dist_triangle x zout y
      _ = dist x zout + dist y zout := by rw [dist_comm zout y]
      _ ≤ R + R := by gcongr
      _ = 2 * R := by ring
  have h := conductance_hitAndRun_ge_param hn hKc hKcl hKm hKb hball hD hc0 hc1 hLem41 hIso
  rwa [show (245760 : ℝ) * (n : ℝ) * (2 * R) = 491520 * (n : ℝ) * R from by ring] at h

/-- **`Arlib.MarkovChains.tvLe_iterate_lazy_hitAndRun_unitBall` with the Lemma 4.1 overlap
constant a parameter.**

The original (`ConductanceToTV.lean:414`) hardcodes `hLem41` at `1 − 1/500`, a constant
`HitAndRunOverlap.lean` shows the corrected proof of Lemma 4.1 does not reach.  Here the
constant is free: `hLem41` is consumed at `1 − c` for any `c ∈ (0,1]`, `hIso` is carried
verbatim, and the deadline is the honest function of `c`,

    4 · lsThreshold M (c/(491520·n·R)) ε  =  4 · 491520² · n²R²/c² · log(8M/ε²),

quadratic in `1/c`.  At `c = 1/500` this is *shorter* than the original's
`4·lvThreshold n 1 R M ε`, which is what makes the recovery below go through.

`hLem41` is a binder, not a discharged fact — see the module docstring for exactly what
blocks discharging it from `tvLe_hitAndRun_lemma41_uncond`. -/
theorem tvLe_iterate_lazy_hitAndRun_unitBall_param {n : ℕ} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    {z zout : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {R : ℝ} (hR1 : 1 ≤ R) (hout : K ⊆ Metric.closedBall zout R)
    {sigma : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure sigma]
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    {M eps : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hSm : MeasurableSet S)
    (hS : sigma S ≤ ENNReal.ofReal (eps / 2))
    (hdom : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      sigma (A \ S) ≤ ENNReal.ofReal M * Arlib.uniformOn volume K A)
    (hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      Arlib.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - c)))
    (hIso : ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))), (∀ x, 0 ≤ h x) →
      (∀ x ∈ K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (crossRatioDist K u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(Arlib.uniformOn volume K)) *
          min (Arlib.uniformOn volume K T₁) (Arlib.uniformOn volume K T₂)
        ≤ Arlib.uniformOn volume K ((K \ T₁) \ T₂))
    {m : ℕ} (hm : 4 * lsThreshold M (c / (491520 * (n : ℝ) * R)) eps ≤ (m : ℝ)) :
    Arlib.TVLe (iterate (lazy (hitAndRun K)) sigma m) (Arlib.uniformOn volume K)
      (ENNReal.ofReal eps) := by
  have hR : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hK0 : volume K ≠ 0 := by
    have hpos : 0 < volume (Metric.closedBall z 1) :=
      Metric.measure_closedBall_pos volume z one_pos
    exact (lt_of_lt_of_le hpos (measure_mono hball)).ne'
  have hKtop : volume K ≠ ⊤ :=
    ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono hout)
  have hphi0 : 0 < c / (491520 * (n : ℝ) * R) := by positivity
  have hphi1 : c / (491520 * (n : ℝ) * R) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  exact tvLe_iterate_lazy_hitAndRun_param hn hKm hK0 hKtop hphi0 hphi1 hM heps0 heps1 hSm hS
    hdom (ofReal_le_conductance_hitAndRun_of_unitBall_param hn hKc hKcl hKm hball hR hout hc0
      hc1 hLem41 hIso) hm

/-- **The original `Arlib.MarkovChains.tvLe_iterate_lazy_hitAndRun_unitBall`, recovered from
the parametric form at `c = 1/500`.**

The statement is that of `ConductanceToTV.lean:414` verbatim; the certificate that no binder
drifted is `tvLe_iterate_lazy_hitAndRun_unitBall_of_param_eq` below.

The proof is `le_trans` on the deadline, as the brief allows: at `c = 1/500` the parametric
deadline is `4·lsThreshold M (1/(245760000·n·R)) ε`, and the original's
`4·lvThreshold n 1 R M ε = 4·lsThreshold M (1/(2²⁸·n·R)) ε` is *longer*, because
`245760000 ≤ 2²⁸ = 268435456` — the exact rounding the original performed.  So the
parametrisation loses nothing and in fact gains a factor `(268435456/245760000)² ≈ 1.19` in
the step count. -/
theorem tvLe_iterate_lazy_hitAndRun_unitBall_of_param {n : ℕ} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    {z zout : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {R : ℝ} (hR1 : 1 ≤ R) (hout : K ⊆ Metric.closedBall zout R)
    {sigma : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure sigma]
    {M eps : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hSm : MeasurableSet S)
    (hS : sigma S ≤ ENNReal.ofReal (eps / 2))
    (hdom : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      sigma (A \ S) ≤ ENNReal.ofReal M * Arlib.uniformOn volume K A)
    (hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      Arlib.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 500)))
    (hIso : ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))), (∀ x, 0 ≤ h x) →
      (∀ x ∈ K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (crossRatioDist K u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(Arlib.uniformOn volume K)) *
          min (Arlib.uniformOn volume K T₁) (Arlib.uniformOn volume K T₂)
        ≤ Arlib.uniformOn volume K ((K \ T₁) \ T₂))
    {m : ℕ} (hm : 4 * lvThreshold n 1 R M eps ≤ (m : ℝ)) :
    Arlib.TVLe (iterate (lazy (hitAndRun K)) sigma m) (Arlib.uniformOn volume K)
      (ENNReal.ofReal eps) := by
  have hR : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  refine tvLe_iterate_lazy_hitAndRun_unitBall_param hn hKc hKcl hKm hball hR1 hout
    (c := 1 / 500) (by norm_num) (by norm_num) hM heps0 heps1 hSm hS hdom hLem41 hIso ?_
  refine le_trans ?_ hm
  have hle : lsThreshold M ((1 : ℝ) / 500 / (491520 * (n : ℝ) * R)) eps
      ≤ lvThreshold n 1 R M eps := by
    rw [← lsThreshold_eq_lvThreshold hn one_pos hR]
    refine lsThreshold_anti hM heps0 heps1 (by positivity) ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos (lt_of_lt_of_le one_pos hn1) hR]
  linarith

/-- **The two unit-ball statements are literally the same statement.**  As for
`tvLe_iterate_lazy_hitAndRun_of_param_eq`: the equation does not elaborate unless every
binder of `tvLe_iterate_lazy_hitAndRun_unitBall_of_param` matches the original's, including
the `hIso` bundle and the corrected clause `∀ x ∈ K, h x ≤ 1/3` inside it. -/
theorem tvLe_iterate_lazy_hitAndRun_unitBall_of_param_eq :
    @tvLe_iterate_lazy_hitAndRun_unitBall_of_param = @tvLe_iterate_lazy_hitAndRun_unitBall :=
  rfl

/-! ## 4. Towards the `hLem41` binder: the proved Lemma 4.1 in the consumer's `max` shape

`tvLe_hitAndRun_lemma41_uncond` (`SphereCap.lean:896`) asks for
`‖u − v‖ < 2/√n · F(u)` — the median step of the **first** point.  The `hLem41` binder asks
for `dist u v < 2/√n · max(F(u), F(v))`.  The gap is closed by symmetry, at no cost: in the
branch where the max is `F(v)`, apply the lemma with the roles exchanged and flip the
conclusion with `Arlib.TVLe.symm`.  The chord hypotheses survive the exchange because
`chordLow K v u = 1 − chordHigh K u v` and `chordHigh K v u = 1 − chordLow K u v`
(`Arlib.chordLow_swap`, `Arlib.chordHigh_swap`), so `ha` and `hb` simply trade places, and
`crossRatioDist` is symmetric (`Arlib.crossRatioDist_comm`). -/

/-- **Lemma 4.1 at `1 − 1/8000`, in the `max` shape the `hLem41` binder uses.**

Every hypothesis of `tvLe_hitAndRun_lemma41_uncond` is retained: `huv`, the two `hmove`s and
the two chord conditions `ha`, `hb`.  Only the step-length hypothesis is relaxed, from
`F(u)` to `max(F(u), F(v))`.

Non-vacuity: at two distinct **interior** points of a bounded convex body with nonempty
interior, `hmoveu`/`hmovev` hold by `Arlib.hitAndRunProposal_univ_eq_one_of_mem_interior`
and `ha`/`hb` hold because the chord through `u` and `v` extends strictly beyond both.  What
they exclude is boundary points, where `ha` is *always* false — which is exactly why this
lemma does not close the `hLem41` binder; see the module docstring, `What remains`, item 3. -/
theorem tvLe_hitAndRun_lemma41_uncond_max {n : ℕ} (hn : 21 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K) {u v : EuclideanSpace ℝ (Fin n)}
    (hu : u ∈ K) (hv : v ∈ K) (huv : u ≠ v)
    (hmoveu : hitAndRunProposal K u Set.univ = 1)
    (hmovev : hitAndRunProposal K v Set.univ = 1)
    (ha : chordLow K u v < 0) (hb : 1 < chordHigh K u v)
    (hdK : crossRatioDist K u v < 1 / 8)
    (hF : dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v)) :
    Arlib.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 8000)) := by
  rw [dist_eq_norm] at hF
  rcases max_cases (medianStep K u) (medianStep K v) with ⟨heq, _⟩ | ⟨heq, _⟩
  · rw [heq] at hF
    exact tvLe_hitAndRun_lemma41_uncond hn hKc hKcl hKm hKb hu hv huv hmoveu hmovev ha hb
      hdK hF
  · rw [heq, norm_sub_rev u v] at hF
    refine (tvLe_hitAndRun_lemma41_uncond hn hKc hKcl hKm hKb hv hu huv.symm hmovev hmoveu
      ?_ ?_ ?_ hF).symm
    · rw [chordLow_swap hKb huv hu]; linarith
    · rw [chordHigh_swap hKb huv hu]; linarith
    · rwa [← crossRatioDist_comm hKb huv hu hv]

/-! ## 5. The instantiation at the proved overlap constant `1 − 1/8000` -/

/-- **Theorem 1.1 for the lazy hit-and-run walk on a body with a unit inball, at the overlap
constant `1 − 1/8000` that `tvLe_hitAndRun_lemma41_uncond` proves.**

    Φ  ≥  1/(3932160000·n·R)  ≥  1/(2³²·n·R),   deadline  4 · 2⁶⁴ · n²R² · log(8M/ε²).

Exactly `256 = (8000/500)²` times the original's `4 · 2⁵⁶ · n²R² · log(8M/ε²)`, and the same
`O(n²R²·log(M/ε))` shape.  (`8000 · 491520 = 3932160000 ≤ 2³² = 4294967296`; the deadline is
quadratic in `1/c`, and the rounding of `3932160000` up to `2³²` is what makes the ratio
exactly `256` rather than `214.6…`.)

`hLem41` is **still a binder** here, now at the constant the repository actually proves.
`tvLe_hitAndRun_lemma41_uncond_max` above supplies it pointwise for two distinct interior
points; the module docstring says precisely why that does not close the binder, which ranges
over all of `K`.  `hIso` is likewise a binder, as everywhere in this chain. -/
theorem tvLe_iterate_lazy_hitAndRun_unitBall_8000 {n : ℕ} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    {z zout : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {R : ℝ} (hR1 : 1 ≤ R) (hout : K ⊆ Metric.closedBall zout R)
    {sigma : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure sigma]
    {M eps : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hSm : MeasurableSet S)
    (hS : sigma S ≤ ENNReal.ofReal (eps / 2))
    (hdom : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      sigma (A \ S) ≤ ENNReal.ofReal M * Arlib.uniformOn volume K A)
    (hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      Arlib.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 8000)))
    (hIso : ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))), (∀ x, 0 ≤ h x) →
      (∀ x ∈ K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (crossRatioDist K u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(Arlib.uniformOn volume K)) *
          min (Arlib.uniformOn volume K T₁) (Arlib.uniformOn volume K T₂)
        ≤ Arlib.uniformOn volume K ((K \ T₁) \ T₂))
    {m : ℕ}
    (hm : 4 * (2 ^ 64 * (n : ℝ) ^ 2 * R ^ 2 * Real.log (8 * M / eps ^ 2)) ≤ (m : ℝ)) :
    Arlib.TVLe (iterate (lazy (hitAndRun K)) sigma m) (Arlib.uniformOn volume K)
      (ENNReal.ofReal eps) := by
  have hR : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  refine tvLe_iterate_lazy_hitAndRun_unitBall_param hn hKc hKcl hKm hball hR1 hout
    (c := 1 / 8000) (by norm_num) (by norm_num) hM heps0 heps1 hSm hS hdom hLem41 hIso ?_
  refine le_trans ?_ hm
  have hstep : lsThreshold M ((1 : ℝ) / 8000 / (491520 * (n : ℝ) * R)) eps
      ≤ lsThreshold M (1 / (2 ^ 32 * (n : ℝ) * R)) eps := by
    refine lsThreshold_anti hM heps0 heps1 (by positivity) ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos (lt_of_lt_of_le one_pos hn1) hR]
  have hval : lsThreshold M (1 / (2 ^ 32 * (n : ℝ) * R)) eps
      = 2 ^ 64 * (n : ℝ) ^ 2 * R ^ 2 * Real.log (8 * M / eps ^ 2) := by
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    rw [lsThreshold, div_pow, one_pow]
    field_simp
  rw [← hval]
  linarith

/-! ## Axiom profile -/

section AxiomCheck

#print axioms lsThreshold_anti
#print axioms tvLe_iterate_lazy_hitAndRun_param
#print axioms tvLe_iterate_lazy_hitAndRun_of_param
#print axioms tvLe_iterate_lazy_hitAndRun_of_param_eq
#print axioms ofReal_le_conductance_hitAndRun_of_unitBall_param
#print axioms tvLe_iterate_lazy_hitAndRun_unitBall_param
#print axioms tvLe_iterate_lazy_hitAndRun_unitBall_of_param
#print axioms tvLe_iterate_lazy_hitAndRun_unitBall_of_param_eq
#print axioms tvLe_hitAndRun_lemma41_uncond_max
#print axioms tvLe_iterate_lazy_hitAndRun_unitBall_8000

end AxiomCheck

end Arlib.MarkovChains
