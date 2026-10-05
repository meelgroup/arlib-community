/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.MetropolisConductanceSharp
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.OverlapSqrt
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.LensSharp

/-!
# The Metropolis-filtered Gaussian ball walk at separation `δ/√n`

`Arlib.MarkovChains.metropolisGaussian_overlap_of_convex`
(`MetropolisConductanceSharp.lean:238`) proves `cor:overlap` for `metropolisGaussian` only for
pairs with `‖u − v‖ < δ/n`, because its geometric input
`Arlib.MarkovChains.volume_lens_inter_ge_max` (`StarPolar.lean:239`) holds at that separation.
Its consumer `Arlib.MarkovChains.conductance_metropolisGaussian_sharp_ge` (`:431`) therefore
instantiates `Arlib.MarkovChains.conductance_speedyGaussian_ge` — whose own overlap binder is
at `δ_abs/√n` — at the *isoperimetric scale* `δ_abs := δ/√n`, and lands on
`Φ ≥ δ·log 2/(640·σ·n)`.  The speedy walk, by contrast, has overlap at separation `δ/√n`
(`Arlib.MarkovChains.overlap_speedyWalk_sqrt_of_ell_comparable_global`, `OverlapSqrt.lean:545`),
so `Arlib.MarkovChains.conductance_speedyGaussian_ge_of_ell_comparable` (`:658`) instantiates
the same theorem at `δ_abs := δ` and lands on `Φ ≥ δ·log 2/(640·σ·√n)` — a factor `√n` better
at the same kernel step.

This file removes that gap for the Metropolis kernel:

* `metropolisGaussian_overlap_sqrt_of_convex` — `cor:overlap` for `metropolisGaussian` at
  separation `δ/√n`;
* `conductance_metropolisGaussian_sharp_sqrt_ge` — hence `Φ ≥ δ·log 2/(640·σ·√n)` for the
  Metropolis kernel, with `hiso` left as a binder exactly as before;
* `exists_conductance_metropolisGaussian_sharp_sqrt_witness` — non-vacuity: every hypothesis
  of the headline *except* `hiso` is jointly satisfiable at a bounded convex body, at the same
  `θ = 1/4` as the `δ/n` witness.

Nothing here is edited into the files above; all three results are new, and every hypothesis
of `metropolisGaussian_overlap_of_convex` other than the separation is carried unchanged.

## What changes in the proof, and what it costs

The one changed step is the lens input.  The `δ/n` proof uses
`Arlib.MarkovChains.volume_lens_inter_ge_max`, contraction constant `(1 − 1/n)ⁿ`, in the `max`
form; the `δ/√n` proof uses `Arlib.MarkovChains.volume_lens_ge_min_ball_inter_quarter`
(`LensSharp.lean:409`), constant `1/4`, in the `min` form.  Everything else — the ratio
acceptance floor `a = e^{−(2Rδ+δ²)/(2s)}` of `Arlib.MarkovChains.metropolisAccept_ge`, the
domination `Arlib.MarkovChains.mul_volume_le_metropolisGaussian`, the `T`/`Tᶜ` split — is
reused verbatim.

**The `min` form costs nothing here.**  `hell` is a *global* floor `θ ≤ ell K δ x` on all of
`K`, so it bounds `vol(B(u,δ) ∩ K)` and `vol(B(v,δ) ∩ K)` below simultaneously, hence bounds
their `min`.  This is why **no `ℓ`-comparability binder is needed**, unlike
`overlap_speedyWalk_sqrt_of_ell_comparable_global`: the speedy walk normalises by
`vol(B(x,δ) ∩ K)` and therefore carries *no* floor, so it must compare the two normalisers;
the Metropolis kernel normalises by `vol(δBₙ)` and already carries a floor, which does the
same job.  The floor is not optional — see `MetropolisConductanceSharp.lean`'s module
docstring for why `hoverlap` is outright false for this kernel without one.

**What it costs is a slightly stronger floor constant, and almost nothing.**  The floor becomes

    1 ≤ 20 · a · (1/4) · θ,        i.e.  θ ≥ 0.2/a,

against the `δ/n` version's

    1 ≤ 20 · a · (1 − 1/n)ⁿ · θ,   i.e.  θ ≥ 1/(20·(1 − 1/n)ⁿ·a),

and since `(1 − 1/n)ⁿ` increases from `1/4` at `n = 2` to `e⁻¹ ≈ 0.368`, the effective
coefficient goes from `20·(1 − 1/n)ⁿ ∈ [5, 20/e ≈ 7.36]` to a flat `20/4 = 5`.  At `n = 2` the
two floors are **literally the same inequality**; for larger `n` the demand on `θ` is stronger
by at most `4/e ≈ 1.47`.  At `a ≈ 1` the old floor asks `θ ≳ 0.2` (`n = 2`) to `0.136`
(`n` large); the new one asks `θ ≥ 0.2` for every `n`.  This is a hypothesis constant, not a
conclusion: `1 ≤ 20·(P_u(Tᶜ) + P_v(T))` is unchanged, and it now holds on the `√n`-wider set
of pairs.  Concretely, the `δ/n` witness of
`Arlib.MarkovChains.exists_conductance_metropolisGaussian_sharp_witness` — `ℓ ≡ θ = 1/4` on a
disc — carries over to this file unchanged (`exists_conductance_metropolisGaussian_sharp_sqrt_witness`).

## The lens constant: `1/40` is vacuous, `1/8` is tight, `1/4` is what is used

Three constants for the same geometry at separation `δ/√n` sit in this library, and the choice
is not cosmetic — it decides whether the theorem has any instances at all.

* `Arlib.MarkovChains.kls_lemma35_at_sep_sqrt_dim` (`LensMin.lean:423`), constant `1/40`, is
  the obvious input and makes the theorem **vacuous**: the floor would read
  `1 ≤ 20·a·(1/40)·θ = a·θ/2`, while `a ≤ 1` (the exponent is nonpositive) and
  `θ ≤ ell K δ x ≤ 1` (`Arlib.MarkovChains.ell_le_one`) at any point of a nonempty `K`, so
  `a·θ/2 ≤ 1/2 < 1`.  No nonempty body satisfies it.
* `Arlib.MarkovChains.volume_lens_ge_min_ball_inter_sharp` (`OverlapSqrt.lean:195`), constant
  `1/8`, asks `θ ≥ 0.4/a`.  That is satisfiable but **tight**: a supporting hyperplane at a
  boundary point of a convex body forces `ell ≤ 1/2` there, so with `a = e^{−1/8} ≈ 0.88` at
  the Cousins–Vempala parameters the margin is `0.44` against a demand of `0.4`, about `10%`.
* `Arlib.MarkovChains.volume_lens_ge_min_ball_inter_quarter` (`LensSharp.lean:409`), constant
  `1/4` — **used here** — asks `θ ≥ 0.2/a`, roughly doubling that margin and matching the
  `δ/n` floor exactly at `n = 2`.

So the `√n` is not bought at a materially worse hypothesis: it is essentially free.

## Non-vacuity (`CLAUDE.md` §11)

`exists_conductance_metropolisGaussian_sharp_sqrt_witness` discharges every hypothesis of
`conductance_metropolisGaussian_sharp_sqrt_ge` except `hiso`, simultaneously, at `n = 2`,
`K = B(0,1/2) ⊆ ℝ²`, `δ = 1`, `R = 1/2`, `σ = 16`, `θ = 1/4`, and shows the conclusion there is
not the trivial `0 ≤ _` and that `metropolisGaussian_overlap_sqrt_of_convex` genuinely fires at
separation `δ/√2`.  `hiso` itself is **not** exhibited — see below.

## No rate claim

`hiso` is a binder of `conductance_metropolisGaussian_sharp_sqrt_ge`, exactly as it is of
`Arlib.MarkovChains.conductance_metropolisGaussian_sharp_ge`, and it is not proved anywhere in
this repository.  Nothing here is a mixing-time statement or an `O*(n³)` claim.  There is no
`def`, `structure` or named `Prop` in this file; all three declarations are `theorem`s.

## The step cap

`conductance_metropolisGaussian_sharp_sqrt_ge` carries `hδσ : δ ≤ σ/(8√n)`, inherited
unchanged from `Arlib.MarkovChains.conductance_speedyGaussian_ge`, where the `δ/n` consumer
reads `δ ≤ σ/8` only because it instantiates at `δ_abs = δ/√n`.  What `DeltaCap.lean` shows is
that `Θ(σ/√n)` is the operative scale from both sides:

* `Arlib.MarkovChains.metropolis_hfloor_forces_step_cap` — the acceptance floor together with
  `σ√n ≤ R` **forces** `δ ≤ (ln 20)·σ/√n`, so the step cannot exceed `Θ(σ/√n)`;
* `Arlib.MarkovChains.acceptance_factor_ge_of_step_le` — at `δ ≤ σ/(8√n)` (with `R ≤ σ√n`) the
  acceptance factor is at least `e^{−1/4}`, so that step **is** feasible.

Note that `(ln 20)·σ/√n ≈ 3σ/√n` is about `24×` larger than `σ/(8√n)`: the forced cap does
**not** by itself place `δ` inside `hδσ`.  What the two facts do establish is that `hδσ` costs
only a **constant factor** on the operative scale, not a power of `n`.  Evaluated at
`δ = σ/(8√n)` the bound below is `Φ ≥ ln 2/(5120·n)`, against the `δ/n` route's
`Φ ≥ ln 2/(5120·n^{3/2})` at the same step.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

variable {n : ℕ}

/-! ## 1. `cor:overlap` for the Metropolis kernel, at separation `δ/√n` -/

/-- **`cor:overlap` for `metropolisGaussian`, on a bounded convex body, at separation
`δ/√n`:**

    1 ≤ 20·(P_u(Tᶜ) + P_v(T))    whenever u ∈ T ∩ K, v ∈ K \ T, ‖u − v‖ < δ/√n,

given a floor `θ` on the local conductance satisfying `1 ≤ 20·a·(1/4)·θ`, where
`a = e^{−(2Rδ+δ²)/(2s)}` is the acceptance floor of `Arlib.MarkovChains.metropolisAccept_ge`.

This is `Arlib.MarkovChains.metropolisGaussian_overlap_of_convex`
(`MetropolisConductanceSharp.lean:238`) with the separation improved from `δ/n` to `δ/√n`.
The single change is the lens input: `Arlib.MarkovChains.volume_lens_inter_ge_max` at `δ/n`,
constant `(1 − 1/n)ⁿ` in the `max` form, is replaced by
`Arlib.MarkovChains.volume_lens_ge_min_ball_inter_quarter` at `δ/√n`, constant `1/4` in the
`min` form.  The `min` is harmless because `hell` is a floor on all of `K` and so bounds both
ball-slices at once — which is also why **no `ℓ`-comparability hypothesis appears here**,
where `Arlib.MarkovChains.overlap_speedyWalk_sqrt_of_ell_comparable_global` needs one.

The cost is in `hfloor` only, and it is small: the effective coefficient goes from
`20·(1 − 1/n)ⁿ ∈ [5, 20/e ≈ 7.36]` to a flat `20/4 = 5` — the same inequality at `n = 2`, and
at most `4/e ≈ 1.47` more demanding on `θ` at any `n`.  The conclusion is unchanged.

`hKR` (the body is bounded) and `hs` are inherited from the `δ/n` version and are forced by
the kernel: without a radius there is no acceptance floor at all.  `u ∈ T`, `v ∉ T` and
`d_h(u,v) < 1/4` are not used; they are carried so the statement matches the binder of
`Arlib.MarkovChains.conductance_speedyGaussian_ge`. -/
theorem metropolisGaussian_overlap_sqrt_of_convex (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    {δ s R θ : ℝ} (hδ : 0 < δ) (hs : 0 < s) (hR : 0 ≤ R)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hell : ∀ x ∈ K, ENNReal.ofReal θ ≤ ell K δ x)
    (hfloor : 1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s)) * (1 / 4) * θ)
    (h : EuclideanSpace ℝ (Fin n) → ℝ) :
    ∀ T : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet T →
      ∀ u v : EuclideanSpace ℝ (Fin n), u ∈ T → u ∈ K → v ∈ K → v ∉ T →
      ‖u - v‖ < δ / Real.sqrt n → densDist h u v < 1 / 4 →
      1 ≤ 20 * (metropolisGaussian K δ s u Tᶜ + metropolisGaussian K δ s v T) := by
  intro T hT u v _ huK hvK _ hsep _
  have hexp : (0 : ℝ) < Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s)) := Real.exp_pos _
  have hθ0 : (0 : ℝ) ≤ θ := by
    by_contra hc
    push Not at hc
    have hpos : (0:ℝ) < 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s)) * (1 / 4) := by positivity
    linarith [mul_neg_of_pos_of_neg hpos hc]
  set vb : ℝ≥0∞ := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ) with hvbdef
  have hvb0 : vb ≠ 0 := (Metric.measure_ball_pos volume 0 hδ).ne'
  have hvbtop : vb ≠ ⊤ := measure_ball_lt_top.ne
  set C : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball u δ ∩ Metric.ball v δ with hCdef
  have hCK : MeasurableSet (C ∩ K) := (measurableSet_ball.inter measurableSet_ball).inter hK
  set a : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s))) with hadef
  -- the two one-step laws each dominate the lens contribution
  have h1 : a * vb⁻¹ * volume (Tᶜ ∩ (C ∩ K)) ≤ metropolisGaussian K δ s u Tᶜ :=
    mul_volume_le_metropolisGaussian hs hR hδ (hKR u huK) hT.compl hCK Set.inter_subset_left
  have h2 : a * vb⁻¹ * volume (T ∩ (C ∩ K)) ≤ metropolisGaussian K δ s v T :=
    mul_volume_le_metropolisGaussian hs hR hδ (hKR v hvK) hT hCK Set.inter_subset_right
  have h3 : volume (Tᶜ ∩ (C ∩ K)) + volume (T ∩ (C ∩ K)) = volume (C ∩ K) := by
    have hm := measure_inter_add_sdiff (μ := volume) (C ∩ K) hT
    rw [Set.inter_comm (C ∩ K) T, Set.sdiff_eq, Set.inter_comm (C ∩ K) Tᶜ] at hm
    rw [add_comm]; exact hm
  have hsum : a * vb⁻¹ * volume (C ∩ K)
      ≤ metropolisGaussian K δ s u Tᶜ + metropolisGaussian K δ s v T := by
    rw [← h3, mul_add]
    exact add_le_add h1 h2
  -- the lens at separation `δ/√n` carries a `1/4` fraction of the *smaller* ball-slice, and
  -- the global floor `hell` bounds **both** slices below by `θ·vol(δBₙ)`
  have hlens : ENNReal.ofReal (1 / 4)
        * min (volume (Metric.ball u δ ∩ K)) (volume (Metric.ball v δ ∩ K))
      ≤ volume (C ∩ K) := volume_lens_ge_min_ball_inter_quarter hn hKc huK hvK hδ hsep.le
  have hballu : ENNReal.ofReal θ * vb ≤ volume (Metric.ball u δ ∩ K) := by
    rw [hvbdef, ← ell_mul_volume_ball K hδ u]
    exact mul_le_mul' (hell u huK) le_rfl
  have hballv : ENNReal.ofReal θ * vb ≤ volume (Metric.ball v δ ∩ K) := by
    rw [hvbdef, ← ell_mul_volume_ball K hδ v]
    exact mul_le_mul' (hell v hvK) le_rfl
  have hCKlb : ENNReal.ofReal (1 / 4) * (ENNReal.ofReal θ * vb) ≤ volume (C ∩ K) :=
    le_trans (mul_le_mul' le_rfl (le_min hballu hballv)) hlens
  have hcancel : a * vb⁻¹ * (ENNReal.ofReal (1 / 4) * (ENNReal.ofReal θ * vb))
      = a * ENNReal.ofReal (1 / 4) * ENNReal.ofReal θ := by
    have hvbc : vb⁻¹ * vb = 1 := ENNReal.inv_mul_cancel hvb0 hvbtop
    calc a * vb⁻¹ * (ENNReal.ofReal (1 / 4) * (ENNReal.ofReal θ * vb))
        = a * ENNReal.ofReal (1 / 4) * ENNReal.ofReal θ * (vb⁻¹ * vb) := by ring
      _ = _ := by rw [hvbc, mul_one]
  have hkey : a * ENNReal.ofReal (1 / 4) * ENNReal.ofReal θ
      ≤ metropolisGaussian K δ s u Tᶜ + metropolisGaussian K δ s v T := by
    rw [← hcancel]
    exact le_trans (mul_le_mul' le_rfl hCKlb) hsum
  calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
    _ ≤ ENNReal.ofReal
          (20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s)) * (1 / 4) * θ) :=
        ENNReal.ofReal_le_ofReal hfloor
    _ = 20 * (a * ENNReal.ofReal (1 / 4) * ENNReal.ofReal θ) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 20), hadef,
          show ENNReal.ofReal (20 : ℝ) = (20 : ℝ≥0∞) by simp]
        ring
    _ ≤ 20 * (metropolisGaussian K δ s u Tᶜ + metropolisGaussian K δ s v T) :=
        mul_le_mul' le_rfl hkey

/-! ## 2. The headline, at the isoperimetric scale `δ` -/

/-- **The sharp conductance bound for the Metropolis-filtered Gaussian ball walk on a bounded
convex body, at separation `δ/√n`:**

    Φ(metropolisGaussian K δ σ²)  ≥  δ·log 2 / (640·σ·√n)

with respect to `π = Arlib.uniformOn (volume.withDensity (gaussianWeight σ²)) K`, which by
`Arlib.MarkovChains.isReversible_metropolisGaussian` is exactly the chain's stationary law.

This is `Arlib.MarkovChains.conductance_speedyGaussian_ge` instantiated at
`P := metropolisGaussian K δ σ²` and at the isoperimetric scale `δ_abs := δ` — where
`Arlib.MarkovChains.conductance_metropolisGaussian_sharp_ge` must instantiate at
`δ_abs := δ/√n` because its overlap input only reaches separation `δ/n`.  The overlap
hypothesis is discharged by `metropolisGaussian_overlap_sqrt_of_convex`; every hypothesis of
the abstract theorem except `hiso` is discharged here, exactly as in the `δ/n` version, and
the `π ↔ h` bridges (`Arlib.MarkovChains.uniformOn_gaussianWeight_eq_div`,
`Arlib.MarkovChains.integral_gaussianIndicator_pos`) are reused unchanged.

**What is gained and what is paid.**

* **Gained: a factor `√n` in `Φ` at the same kernel step.**  `δ·log 2/(640·σ·√n)` against
  `δ·log 2/(640·σ·n)`, for one and the same kernel `metropolisGaussian K δ σ²`.
* **Paid, in `hfloor`:** `1 ≤ 20·a·(1/4)·θ` in place of `1 ≤ 20·a·(1 − 1/n)ⁿ·θ` — the same
  inequality at `n = 2`, and at most `4/e ≈ 1.47` more demanding on the local-conductance
  floor `θ` at any `n`.  It is met by the very witness the `δ/n` version uses:
  `exists_conductance_metropolisGaussian_sharp_sqrt_witness` runs at the same `K` and the same
  `θ = 1/4`.
* **Paid, in `hδσ`:** `δ ≤ σ/(8√n)`, inherited verbatim from
  `conductance_speedyGaussian_ge`, where the `δ/n` version reads `δ ≤ σ/8` only because of its
  reparameterization.  `DeltaCap.lean` bounds the operative scale on both sides — the
  acceptance floor with `σ√n ≤ R` forces `δ ≤ (ln 20)·σ/√n`
  (`Arlib.MarkovChains.metropolis_hfloor_forces_step_cap`), and `δ ≤ σ/(8√n)` is feasible with
  acceptance `≥ e^{−1/4}` when `R ≤ σ√n` (`Arlib.MarkovChains.acceptance_factor_ge_of_step_le`)
  — so `hδσ` costs a constant factor on the `Θ(σ/√n)` scale, not a power of `n`.  It is not
  implied by the floor: `(ln 20)·σ/√n` is some `24×` larger than `σ/(8√n)`.

**`hiso` is a hypothesis.**  It is Cousins–Vempala's `thm:iso` at `d = δ·log 2/√n`, in the
exact shape `conductance_speedyGaussian_ge` consumes and `Arlib.gaussianRestricted_isoperimetry`
concludes, at `h = 1_K · e^{−‖x‖²/(2σ²)}`.  It is **not proved in this repository**.
Therefore **this theorem is not a mixing-time bound and not an `O*(n³)` claim, and may not be
quoted as either.** -/
theorem conductance_metropolisGaussian_sharp_sqrt_ge (hn : 2 ≤ n)
    {σ δ R θ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) (hδσ : δ ≤ σ / (8 * Real.sqrt n)) (hR : 0 ≤ R)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hKtop : volume K ≠ ⊤) (hK0 : volume K ≠ 0)
    (hell : ∀ x ∈ K, ENNReal.ofReal θ ≤ ell K δ x)
    (hfloor : 1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) * (1 / 4) * θ)
    (hiso : ∀ S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n)),
      IsPartition3 Set.univ S₁ S₂ S₃ →
      MeasurableSet S₁ → MeasurableSet S₂ → MeasurableSet S₃ →
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        δ * Real.log 2 / Real.sqrt n / Real.log 2 ≤ ‖u - v‖ ∨
          4 * (δ * Real.log 2 / Real.sqrt n / σ) * Real.sqrt n
            ≤ densDist (Set.indicator K (gaussianWeightReal (σ ^ 2))) u v) →
      δ * Real.log 2 / Real.sqrt n / σ
          * ((∫ x in S₁, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
            * ∫ x in S₂, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
        ≤ (∫ x, Set.indicator K (gaussianWeightReal (σ ^ 2)) x)
          * ∫ x in S₃, Set.indicator K (gaussianWeightReal (σ ^ 2)) x) :
    ENNReal.ofReal (δ * Real.log 2 / (640 * σ * Real.sqrt n))
      ≤ conductance (metropolisGaussian K δ (σ ^ 2))
          (Arlib.uniformOn ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
            (gaussianWeight (σ ^ 2))) K) := by
  have hs : (0 : ℝ) < σ ^ 2 := by positivity
  set h : EuclideanSpace ℝ (Fin n) → ℝ :=
    Set.indicator K (gaussianWeightReal (σ ^ 2)) with hhdef
  have hh0 : ∀ x, 0 ≤ h x :=
    fun x => Set.indicator_nonneg (fun y _ => (gaussianWeightReal_pos _ y).le) x
  have hmass : 0 < ∫ x, h x := integral_gaussianIndicator_pos hs hK hKtop hK0 hKR
  exact conductance_speedyGaussian_ge hn hσ hδ hδσ hh0 hmass hK
    (metropolisGaussian K δ (σ ^ 2)) _
    (fun A hA => uniformOn_gaussianWeight_eq_div hs hK hKtop A hA)
    (isReversible_metropolisGaussian hK δ (σ ^ 2)) (Arlib.uniformOn_compl_eq_zero _ hK)
    (metropolisGaussian_overlap_sqrt_of_convex hn hK hKc hδ hs hR hKR hell hfloor h) hiso

/-! ## 3. Non-vacuity (`CLAUDE.md` §11) -/

/-- **Non-vacuity: every hypothesis of `conductance_metropolisGaussian_sharp_sqrt_ge` except
`hiso` is jointly satisfiable at a bounded convex body, the conclusion there is not the
trivial `0 ≤ _`, and `metropolisGaussian_overlap_sqrt_of_convex` really does fire at
separation `δ/√n`.**

The witness is `n = 2`, `K = B(0,1/2) ⊆ ℝ²`, `δ = 1`, `R = 1/2`, `σ = 16` (so `s = σ² = 256`),
`θ = 1/4`, `T = B(0,1/8)`, `u = 0`, `v = (1/4,0)` — the body and pair of
`Arlib.MarkovChains.exists_conductance_metropolisGaussian_sharp_witness`, so that the two
witnesses are directly comparable.  There `ℓ ≡ 1/4` on `K`, because `K ⊆ B(x,1)` for every
`x ∈ K`.

Two things change against the `δ/n` witness, and both are forced by this file's binders:

* `σ = 16` rather than `8`, because `hδσ` here is `δ ≤ σ/(8√n)` rather than `δ ≤ σ/8`; at
  `n = 2` this asks `1 ≤ 16/(8√2) = √2`.  The acceptance constant improves as a result,
  `a = e^{−1/256} ≥ 255/256`.
* the separation is checked against `δ/√2 ≈ 0.707` rather than `δ/2`, which `‖u − v‖ = 1/4`
  clears with room to spare — that is the whole point of the file.

The floor is met at exactly the same `θ = 1/4` as the `δ/n` witness:
`20·a·(1/4)·(1/4) = 1.25·a ≥ 1.24 > 1`.  This is what the lens constant `1/4` of
`Arlib.MarkovChains.volume_lens_ge_min_ball_inter_quarter` buys; at the `1/8` of
`Arlib.MarkovChains.volume_lens_ge_min_ball_inter_sharp` the test would read `0.625·a < 1`
and this witness would fail.

**What this does NOT certify.**  `hiso` is a binder of
`conductance_metropolisGaussian_sharp_sqrt_ge` and is *not* exhibited here — it is not proved
anywhere in this repository.  So this witness shows the theorem is not vacuous *for reasons of
its discharged hypotheses*; it does **not** show the theorem has an unconditional instance, and
it is **not** evidence for any mixing-time or `O*(n³)` claim. -/
theorem exists_conductance_metropolisGaussian_sharp_sqrt_witness :
    ∃ (K T : Set (EuclideanSpace ℝ (Fin 2))) (σ δ R θ : ℝ)
      (u v : EuclideanSpace ℝ (Fin 2)),
      0 < σ ∧ 0 < δ ∧ δ ≤ σ / (8 * Real.sqrt ((2 : ℕ) : ℝ)) ∧ 0 ≤ R ∧
      MeasurableSet K ∧ Convex ℝ K ∧ (∀ x ∈ K, ‖x‖ ≤ R) ∧
      volume K ≠ ⊤ ∧ volume K ≠ 0 ∧
      (∀ x ∈ K, ENNReal.ofReal θ ≤ ell K δ x) ∧
      1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) * (1 / 4) * θ ∧
      0 < ENNReal.ofReal (δ * Real.log 2 / (640 * σ * Real.sqrt ((2 : ℕ) : ℝ))) ∧
      MeasurableSet T ∧ u ∈ T ∧ u ∈ K ∧ v ∈ K ∧ v ∉ T ∧
      ‖u - v‖ < δ / Real.sqrt ((2 : ℕ) : ℝ) ∧
      1 ≤ 20 * (metropolisGaussian K δ (σ ^ 2) u Tᶜ
        + metropolisGaussian K δ (σ ^ 2) v T) := by
  classical
  set K : Set (EuclideanSpace ℝ (Fin 2)) := Metric.ball 0 (1 / 2) with hKdef
  set v : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single (0 : Fin 2) (1 / 4 : ℝ) with hvdef
  have hvnorm : ‖v‖ = 1 / 4 := by
    rw [hvdef, PiLp.norm_single, Real.norm_eq_abs]; norm_num
  have hVpos : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume 0 (by norm_num)).ne'
  have hVtop : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hKvol : volume K ≠ 0 := (Metric.measure_ball_pos volume 0 (by norm_num)).ne'
  have hKtop : volume K ≠ ⊤ := measure_ball_lt_top.ne
  have hKc : Convex ℝ K := convex_ball _ _
  have hKR : ∀ x ∈ K, ‖x‖ ≤ 1 / 2 := by
    intro x hx
    rw [hKdef, Metric.mem_ball, dist_eq_norm, sub_zero] at hx
    exact hx.le
  -- `ℓ ≡ 1/4` on `K`, exactly as in the `δ/n` witness
  have hell : ∀ x ∈ K, ell K (1 : ℝ) x = ENNReal.ofReal (1 / 4) := by
    intro x hx
    have hxnorm : ‖x‖ < 1 / 2 := by
      rw [hKdef, Metric.mem_ball, dist_eq_norm, sub_zero] at hx; exact hx
    have hsub : K ⊆ Metric.ball x 1 := by
      intro y hy
      rw [hKdef, Metric.mem_ball, dist_eq_norm, sub_zero] at hy
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le _ _
        _ < 1 := by linarith
    have hball : volume K
        = ENNReal.ofReal (1 / 4) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
      rw [hKdef, Measure.addHaar_ball_of_pos volume 0 (by norm_num : (0:ℝ) < 1 / 2),
        finrank_euclideanSpace_fin]
      norm_num
    rw [ell_apply, Set.inter_eq_self_of_subset_right hsub, hball, volume_ball_eq x 1]
    exact ENNReal.mul_div_cancel_right hVpos hVtop
  -- the acceptance constant at these parameters is `e^{-1/256} ≥ 255/256`
  have hexpge : (255 : ℝ) / 256
      ≤ Real.exp (-(2 * (1 / 2 : ℝ) * 1 + (1 : ℝ) ^ 2) / (2 * (16 : ℝ) ^ 2)) := by
    have h := Real.add_one_le_exp (-(1 : ℝ) / 256)
    have heq : -(2 * (1 / 2 : ℝ) * 1 + (1 : ℝ) ^ 2) / (2 * (16 : ℝ) ^ 2) = -(1 : ℝ) / 256 := by
      norm_num
    rw [heq]; linarith
  have hfloor : 1 ≤ 20 * Real.exp (-(2 * (1 / 2 : ℝ) * 1 + (1 : ℝ) ^ 2) / (2 * (16 : ℝ) ^ 2))
      * (1 / 4 : ℝ) * (1 / 4 : ℝ) := by linarith
  -- `√2 < 2`, which gives both the step cap `1 ≤ 16/(8√2)` and the separation `1/4 < 1/√2`
  have hcast2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  have hs0 : 0 < Real.sqrt ((2 : ℕ) : ℝ) := Real.sqrt_pos.2 (by rw [hcast2]; norm_num)
  have hs2 : Real.sqrt ((2 : ℕ) : ℝ) < 2 := by
    have h1 : Real.sqrt ((2 : ℕ) : ℝ) ^ 2 = ((2 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
    nlinarith [Real.sqrt_nonneg ((2 : ℕ) : ℝ), h1, hcast2]
  have hδσ : (1 : ℝ) ≤ 16 / (8 * Real.sqrt ((2 : ℕ) : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hs2]
  have huK : (0 : EuclideanSpace ℝ (Fin 2)) ∈ K := by
    rw [hKdef]; exact Metric.mem_ball_self (by norm_num)
  have hvK : v ∈ K := by
    rw [hKdef, Metric.mem_ball, dist_eq_norm, sub_zero, hvnorm]; norm_num
  have hvT : v ∉ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 8) := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, hvnorm]; norm_num
  have hsep : ‖(0 : EuclideanSpace ℝ (Fin 2)) - v‖ < (1 : ℝ) / Real.sqrt ((2 : ℕ) : ℝ) := by
    rw [zero_sub, norm_neg, hvnorm, div_lt_div_iff₀ (by norm_num) hs0]
    nlinarith [hs2]
  have hdens : densDist (fun _ : EuclideanSpace ℝ (Fin 2) => (1 : ℝ)) 0 v < 1 / 4 := by
    simp [densDist]
  refine ⟨K, Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 8), 16, 1, 1 / 2, 1 / 4, 0, v,
    by norm_num, by norm_num, hδσ, by norm_num, measurableSet_ball, hKc, hKR,
    hKtop, hKvol, fun x hx => (hell x hx).ge, hfloor,
    ENNReal.ofReal_pos.2 (by positivity), measurableSet_ball,
    Metric.mem_ball_self (by norm_num), huK, hvK, hvT, hsep, ?_⟩
  exact metropolisGaussian_overlap_sqrt_of_convex (n := 2) (by norm_num) measurableSet_ball hKc
    (by norm_num) (by norm_num) (by norm_num) hKR (fun x hx => (hell x hx).ge) hfloor
    (fun _ => 1) (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 8)) measurableSet_ball
    0 v (Metric.mem_ball_self (by norm_num)) huK hvK hvT hsep hdens

end Arlib.MarkovChains

/-! ### Axiom audit -/

#print axioms Arlib.MarkovChains.metropolisGaussian_overlap_sqrt_of_convex
#print axioms Arlib.MarkovChains.conductance_metropolisGaussian_sharp_sqrt_ge
#print axioms Arlib.MarkovChains.exists_conductance_metropolisGaussian_sharp_sqrt_witness
