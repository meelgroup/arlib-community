/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.SpeedyGaussianConductance

/-!
# `lem:f-dist`, and the elimination of the global `ℓ`-comparability premise

`Arlib.MarkovChains.overlap_speedyWalk_sqrt_of_ell_comparable_global` (`OverlapSqrt.lean:556`)
and everything downstream of it — up to
`Arlib.MarkovChains.conductance_speedyMetropolisGaussian_ge`
(`SpeedyGaussianConductance.lean:523`) — carry `ℓ`-comparability as a **global** premise:

    hcomp : ∀ x ∈ K, ∀ y ∈ K, ‖x − y‖ < δ/√n → ℓ(x) ≤ (3/2)·ℓ(y).

Globally that is **false**, and this repository proves it false
(`Arlib.MarkovChains.exists_ell_not_comparable_at_sqrt_dim_counterexample`).  So every
theorem carrying `hcomp` was blocked.

But comparability is only ever used at the pairs those theorems already quantify over —
`u, v ∈ K` with `‖u − v‖ < δ/√n` **and** `d_h(u,v) < 1/4` for the target density `h = 1_K·ℓ·γ`
— and at those pairs it is a *theorem*: Cousins–Vempala's `lem:f-dist`
(`1409.6011/vol3_journal.tex:553`).  This file proves `lem:f-dist` and uses it to **discharge
`hcomp` outright**.  It is not moved inside a quantifier; it is gone.

## Main results

* `Arlib.MarkovChains.gaussianWeightReal_le_of_cv` — the Gaussian bracket
  `f(u) ≤ (9/8)·f(v)` at separation `δ/√n`, with the paper's "for `n` large enough" replaced
  by the **explicit threshold `n ≥ 21`**, derived rather than inherited.
* `Arlib.MarkovChains.le_three_halves_of_densDist_mul_lt` — the arithmetic of `lem:f-dist`,
  over abstract positive reals.
* `Arlib.MarkovChains.ell_comparable_of_densDist` — **`lem:f-dist`**: from `d_h(u,v) < 1/4`,
  `‖u − v‖ ≤ δ/√n`, `δ ≤ σ/(8√n)` and `K ⊆ 4σ√n·Bₙ`, both `ℓ(u) ≤ (3/2)·ℓ(v)` and
  `ℓ(v) ≤ (3/2)·ℓ(u)`.  Non-vacuous away from the diagonal
  (`ell_comparable_of_densDist_witness`).
* `Arlib.MarkovChains.overlap_speedyWalk_sqrt_perPair` — `cor:overlap` for the speedy walk,
  **with no comparability hypothesis**.
* `Arlib.MarkovChains.hoverlap_speedyMetropolisGaussian_perPair` — the same for the filtered
  chain, in `conductance_speedyGaussian_ge`'s `hoverlap` shape.
* `Arlib.MarkovChains.conductance_speedyMetropolisGaussian_ge_perPair` —
  `Φ ≥ δ·ln 2/(640σ√n)` for `speedyMetropolisGaussian`, **with `hcomp` gone**.

## What this file changes, and what it does not

`conductance_speedyMetropolisGaussian_ge_perPair` differs from its source in exactly two
binders: `hn : 2 ≤ n` becomes `hn : 21 ≤ n`, and `hcomp` disappears.  `hn : 21 ≤ n` is the
only hypothesis introduced anywhere in this file that is not already a binder of the
consumer; it is a numeral condition on the dimension, satisfied at `n = 21`, and it is
computed — not guessed — in `gaussianWeightReal_le_of_cv`.  Every other hypothesis of every
lemma here is passed verbatim to its consumer, so drift is a type error.

`hellLip`/`hLσ` are **not** touched, and the result is still conditional on them.  They are a
different defect from `hcomp` — see the docstring of
`conductance_speedyMetropolisGaussian_ge_perPair`: Cousins–Vempala's `thm:iso`
(`vol3_journal.tex:467`) needs no Lipschitz control of `ℓ` at all, but the repository's
isoperimetry route (`Arlib.norm_sub_ge_of_densDist_weighted`) does, so removing them means
reproving isoperimetry by localization.

**This file does not establish a mixing-time or runtime bound**, and nothing in it may be
quoted as one.  Nothing is `sorry`ed; see the axiom audit at the bottom.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

variable {n : ℕ}

/-! ## 1. The Gaussian bracket, with the dimension threshold made explicit -/

/-- **The Gaussian ratio bracket of `lem:f-dist`, with the paper's "for `n` large enough"
replaced by an explicit dimension threshold.**

Cousins–Vempala (`1409.6011/vol3_journal.tex:566`) assert `0.9 ≤ f(v)/f(u) ≤ 1.1` at
separation `δ/√n` "for `n` large enough" and never say how large.  Here is the arithmetic.
For `‖u‖, ‖v‖ ≤ R` and `‖u − v‖ ≤ δ/√n`,

    ‖v‖² − ‖u‖²  ≤  (‖v‖ − ‖u‖)(‖v‖ + ‖u‖)  ≤  (δ/√n)·2R,

so with `R ≤ 4σ√n` (the paper's containment `K ⊆ 4σ√n Bₙ`) and `δ ≤ σ/(8√n)` (the paper's
step bound) the exponent obeys

    (‖v‖² − ‖u‖²)/(2σ²)  ≤  8σδ/(2σ²)  =  4δ/σ  ≤  1/(2√n).

`1/(2√n) ≤ 1/9` exactly when `√n ≥ 4.5`, i.e. `n ≥ 21` — `n = 20` gives `√20 = 4.472… < 4.5`
and misses.  Finally `e^{1/9} ≤ 9/8`, since `e^{−1/9} ≥ 1 − 1/9 = 8/9`.

The constant is `9/8`, not the paper's `1.1`, because `9/8` is what `lem:f-dist` actually
consumes: `(4/3)·(9/8) = 3/2` on the nose.  A bracket of `1.1` would need `n ≥ 28` and buy
nothing. -/
theorem gaussianWeightReal_le_of_cv (hn : 21 ≤ n) {σ δ R : ℝ} (hσ : 0 < σ) (hδ : 0 < δ)
    (hδσ : δ ≤ σ / (8 * Real.sqrt n)) (hRσ : R ≤ 4 * σ * Real.sqrt n)
    {u v : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R)
    (huv : ‖u - v‖ ≤ δ / Real.sqrt n) :
    gaussianWeightReal (σ ^ 2) u ≤ 9 / 8 * gaussianWeightReal (σ ^ 2) v := by
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hnR : (21 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hS : (4.5 : ℝ) ≤ Real.sqrt n := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by linarith), Real.sqrt_nonneg (n : ℝ)]
  have hSpos : (0 : ℝ) < Real.sqrt n := by linarith
  have h8 : δ * (8 * Real.sqrt n) ≤ σ := (le_div_iff₀ (by positivity)).1 hδσ
  have hR0 : (0 : ℝ) ≤ R := le_trans (norm_nonneg u) hu
  have hnorm : ‖v‖ - ‖u‖ ≤ ‖u - v‖ := by
    rw [norm_sub_rev u v]; exact norm_sub_norm_le v u
  have he0 : (0 : ℝ) ≤ ‖u - v‖ := norm_nonneg _
  -- `‖u − v‖·√n ≤ δ`
  have hsep : ‖u - v‖ * Real.sqrt n ≤ δ := by
    have : ‖u - v‖ * Real.sqrt n ≤ δ / Real.sqrt n * Real.sqrt n := by nlinarith
    rwa [div_mul_cancel₀ δ hSpos.ne'] at this
  -- the exponent bound `‖v‖² − ‖u‖² ≤ 2σ²/9`
  have hstep1 : ‖v‖ ^ 2 - ‖u‖ ^ 2 ≤ ‖u - v‖ * (2 * R) := by
    nlinarith [mul_nonneg he0 (by linarith [norm_nonneg u, norm_nonneg v] :
        (0 : ℝ) ≤ 2 * R - (‖v‖ + ‖u‖)),
      mul_nonneg (by linarith : (0 : ℝ) ≤ ‖u - v‖ - (‖v‖ - ‖u‖))
        (by positivity : (0 : ℝ) ≤ ‖v‖ + ‖u‖)]
  have hstep2 : ‖u - v‖ * (2 * R) * Real.sqrt n ≤ 8 * σ * δ * Real.sqrt n := by
    nlinarith [mul_le_mul_of_nonneg_right hsep (by linarith : (0 : ℝ) ≤ 2 * R),
      mul_le_mul_of_nonneg_left hRσ hδ.le]
  have hstep3 : ‖u - v‖ * (2 * R) ≤ 8 * σ * δ :=
    le_of_mul_le_mul_right hstep2 hSpos
  have hstep4 : 8 * σ * δ ≤ 2 * σ ^ 2 / 9 := by nlinarith
  have hkey : ‖v‖ ^ 2 - ‖u‖ ^ 2 ≤ 2 * σ ^ 2 / 9 := by linarith
  -- `e^{1/9} ≤ 9/8`
  have hexp19 : Real.exp (1 / 9 : ℝ) ≤ 9 / 8 := by
    have h9 : (8 : ℝ) / 9 ≤ Real.exp (-(1 / 9) : ℝ) := by
      have := Real.add_one_le_exp (-(1 / 9) : ℝ); linarith
    have hmul : Real.exp (1 / 9 : ℝ) * Real.exp (-(1 / 9) : ℝ) = 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1 / 9 : ℝ)]
  have hexp : Real.exp ((‖v‖ ^ 2 - ‖u‖ ^ 2) / (2 * σ ^ 2)) ≤ 9 / 8 := by
    have ht : (‖v‖ ^ 2 - ‖u‖ ^ 2) / (2 * σ ^ 2) ≤ 1 / 9 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    exact le_trans (Real.exp_le_exp.2 ht) hexp19
  -- assemble
  rw [gaussianWeightReal, gaussianWeightReal]
  have hfac : Real.exp (-‖u‖ ^ 2 / (2 * σ ^ 2))
      = Real.exp (-‖v‖ ^ 2 / (2 * σ ^ 2)) * Real.exp ((‖v‖ ^ 2 - ‖u‖ ^ 2) / (2 * σ ^ 2)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [hfac]
  nlinarith [Real.exp_pos (-‖v‖ ^ 2 / (2 * σ ^ 2))]

/-! ## 2. `lem:f-dist`, as pure real arithmetic -/

/-- **The arithmetic core of Cousins–Vempala's `lem:f-dist`**
(`1409.6011/vol3_journal.tex:553`), with the two densities abstracted to positive reals.

`A, B` stand for `ℓ(u), ℓ(v)` and `a, b` for `f(u), f(v)`; `hab`/`hba` are the Gaussian
bracket of §1, and `hd` is the paper's `d_h(u,v) < 1/4` at `h = ℓ·f`, spelled with the
repository's `Arlib.densDist`.

The paper's proof, verbatim.  WLOG `A·a ≥ B·b`; then `d_h < 1/4` says `3·A·a < 4·B·b`, and
`b ≤ (9/8)·a` turns that into `3·A < (9/2)·B`, i.e. `A < (3/2)·B`.  In the other direction
`B·b ≤ A·a` and `a ≤ (9/8)·b` give `B ≤ (9/8)·A ≤ (3/2)·A` outright.  The symmetric case is
the same with `A ↔ B`, `a ↔ b`.

The bracket constant `9/8` is exactly what the argument can afford: `(4/3)·(9/8) = 3/2`. -/
theorem le_three_halves_of_densDist_mul_lt {A B a b : ℝ} (hA : 0 < A) (hB : 0 < B)
    (ha : 0 < a) (hb : 0 < b) (hab : a ≤ 9 / 8 * b) (hba : b ≤ 9 / 8 * a)
    (hd : |A * a - B * b| / max (A * a) (B * b) < 1 / 4) :
    A ≤ 3 / 2 * B ∧ B ≤ 3 / 2 * A := by
  rcases le_total (B * b) (A * a) with hle | hle
  · rw [max_eq_left hle, abs_of_nonneg (by linarith),
      div_lt_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)] at hd
    refine ⟨?_, ?_⟩
    · nlinarith [mul_nonneg hB.le (by linarith : (0 : ℝ) ≤ 9 / 8 * a - b)]
    · nlinarith [mul_nonneg hA.le (by linarith : (0 : ℝ) ≤ 9 / 8 * b - a)]
  · rw [max_eq_right hle, abs_of_nonpos (by linarith),
      div_lt_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)] at hd
    refine ⟨?_, ?_⟩
    · nlinarith [mul_nonneg hB.le (by linarith : (0 : ℝ) ≤ 9 / 8 * a - b)]
    · nlinarith [mul_nonneg hA.le (by linarith : (0 : ℝ) ≤ 9 / 8 * b - a)]

/-! ## 3. `lem:f-dist` for `ℓ` and the Gaussian, proved -/

/-- `densDist` reads its function only at the two points, so restricting the function to any
set containing both of them changes nothing.  This is the bridge between the `h` that
`Arlib.MarkovChains.conductance_speedyGaussian_ge` is instantiated at — the *indicator*
`1_K·ℓ·γ` — and the bare product `ℓ·γ` that `lem:f-dist` is about. -/
theorem densDist_indicator_of_mem {E : Type*} {f : E → ℝ} {K : Set E} {u v : E}
    (hu : u ∈ K) (hv : v ∈ K) :
    densDist (Set.indicator K f) u v = densDist f u v := by
  rw [densDist, densDist, Set.indicator_of_mem hu, Set.indicator_of_mem hv]

/-- The `ℝ≥0∞` lift of a real comparison of local conductances.  `ℓ ≤ 1` (`ell_le_one`) makes
both sides finite unconditionally, so no hypothesis is needed. -/
theorem ell_le_of_toReal_le {K : Set (EuclideanSpace ℝ (Fin n))} {δ : ℝ}
    {u v : EuclideanSpace ℝ (Fin n)}
    (h : (ell K δ u).toReal ≤ 3 / 2 * (ell K δ v).toReal) :
    ell K δ u ≤ ENNReal.ofReal (3 / 2) * ell K δ v := by
  have hutop : ell K δ u ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (ell_le_one K δ u)
  have hvtop : ell K δ v ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (ell_le_one K δ v)
  calc ell K δ u = ENNReal.ofReal (ell K δ u).toReal := (ENNReal.ofReal_toReal hutop).symm
    _ ≤ ENNReal.ofReal (3 / 2 * (ell K δ v).toReal) := ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal (3 / 2) * ENNReal.ofReal (ell K δ v).toReal :=
        ENNReal.ofReal_mul (by norm_num)
    _ = ENNReal.ofReal (3 / 2) * ell K δ v := by rw [ENNReal.ofReal_toReal hvtop]

/-- **Cousins–Vempala's `lem:f-dist` (`1409.6011/vol3_journal.tex:553`), proved** — and with
it, the death of the global `ℓ`-comparability premise.

> Let `K ⊆ 4σ√n Bₙ` be a convex body and `u, v ∈ K` with `‖u − v‖ ≤ δ/√n`.  If
> `δ ≤ σ/(8√n)` and `d_h(u,v) < 1/4` for `h = ℓ·f`, then `d_ℓ(u,v) < 1/3`.

`d_ℓ(u,v) < 1/3` is written here division-free, in the two-sided shape every consumer in this
repository wants: `ℓ(u) ≤ (3/2)·ℓ(v)` **and** `ℓ(v) ≤ (3/2)·ℓ(u)`
(`Arlib.MarkovChains.ell_le_of_densDist_ell_lt` shows the two spellings agree).

**This is the hypothesis `Arlib.MarkovChains.overlap_speedyWalk_sqrt_of_ell_comparable_global`
and `Arlib.MarkovChains.conductance_speedyMetropolisGaussian_ge` carry as `hcomp` — and those
carry it *globally over `K`*, where
`Arlib.MarkovChains.exists_ell_not_comparable_at_sqrt_dim_counterexample` refutes it.**  The
premise `d_h(u,v) < 1/4` is what makes the difference: it is false globally and true at
exactly the pairs the consumers' binders quantify over.

Hypotheses, and where each comes from:

* `hn : 21 ≤ n` — the paper's "for `n` large enough", computed in
  `gaussianWeightReal_le_of_cv`.  It is the **only** hypothesis here that is not already a
  binder of the consumer; it is satisfiable (`n = 21`).
* `hδσ : δ ≤ σ/(8√n)` — the paper's step bound, verbatim a binder of
  `conductance_speedyMetropolisGaussian_ge`.
* `hRσ : R ≤ 4σ√n` — the paper's `K ⊆ 4σ√n Bₙ`.  The repository's consumer assumes the
  *stronger* `R ≤ 2σ√n`, which implies this.
* `hu`, `hv : ell K δ · ≠ 0` — non-degeneracy, exactly as
  `Arlib.MarkovChains.ell_le_of_densDist_ell_lt` needs it, and for the same reason: `d_ℓ` is
  `0/0 = 0` where both vanish.  Supplied downstream by
  `Arlib.MarkovChains.volume_ball_inter_ne_zero_of_convex`. -/
theorem ell_comparable_of_densDist (hn : 21 ≤ n) {σ δ R : ℝ} (hσ : 0 < σ) (hδ : 0 < δ)
    (hδσ : δ ≤ σ / (8 * Real.sqrt n)) (hRσ : R ≤ 4 * σ * Real.sqrt n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    {u v : EuclideanSpace ℝ (Fin n)} (huK : u ∈ K) (hvK : v ∈ K)
    (hu : ell K δ u ≠ 0) (hv : ell K δ v ≠ 0)
    (hsep : ‖u - v‖ ≤ δ / Real.sqrt n)
    (hd : densDist (fun x => (ell K δ x).toReal * gaussianWeightReal (σ ^ 2) x) u v < 1 / 4) :
    ell K δ u ≤ ENNReal.ofReal (3 / 2) * ell K δ v ∧
      ell K δ v ≤ ENNReal.ofReal (3 / 2) * ell K δ u := by
  have hutop : ell K δ u ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (ell_le_one K δ u)
  have hvtop : ell K δ v ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (ell_le_one K δ v)
  have hA : 0 < (ell K δ u).toReal := ENNReal.toReal_pos hu hutop
  have hB : 0 < (ell K δ v).toReal := ENNReal.toReal_pos hv hvtop
  have hsep' : ‖v - u‖ ≤ δ / Real.sqrt n := by rwa [norm_sub_rev]
  obtain ⟨h1, h2⟩ := le_three_halves_of_densDist_mul_lt hA hB
    (gaussianWeightReal_pos (σ ^ 2) u) (gaussianWeightReal_pos (σ ^ 2) v)
    (gaussianWeightReal_le_of_cv hn hσ hδ hδσ hRσ (hKR u huK) (hKR v hvK) hsep)
    (gaussianWeightReal_le_of_cv hn hσ hδ hδσ hRσ (hKR v hvK) (hKR u huK) hsep')
    (by simpa only [densDist] using hd)
  exact ⟨ell_le_of_toReal_le h1, ell_le_of_toReal_le h2⟩

/-! ## 4. `cor:overlap` with no comparability premise at all -/

/-- **`Arlib.MarkovChains.overlap_speedyWalk_sqrt_of_ell_comparable_global` with `hcomp`
discharged, not moved.**

Diff against the source statement (`OverlapSqrt.lean:556`), clause by clause:

* `hn : 2 ≤ n` becomes `hn : 21 ≤ n` — the threshold of `gaussianWeightReal_le_of_cv`;
* `hcomp`, the global `ℓ`-comparability premise that
  `Arlib.MarkovChains.exists_ell_not_comparable_at_sqrt_dim_counterexample` **refutes**, is
  **gone**;
* in its place come the geometry hypotheses `lem:f-dist` needs and the paper states:
  `hσ`, `hδσ : δ ≤ σ/(8√n)` and `K ⊆ R·Bₙ ⊆ 4σ√n·Bₙ`;
* the universally quantified `(h : ℝⁿ → ℝ)` is **specialised** to the density the consumer
  actually passes, `1_K·ℓ·γ`.  That is the whole point: in the source the clause
  `densDist h u v < 1/4` is inert (the docstring there says so — "not used"), and here it
  carries the entire argument.

Everything else — `hK`, `hKc`, `hδ`, `hpos`, the `T/u/v` quantifier block, the separation
clause, the `densDist` clause and the conclusion `1 ≤ 20·(P_u(Tᶜ) + P_v(T))` — is verbatim.

The proved constant is still `12` (`one_le_twelve_mul_speedyWalk_add_of_comparable`),
weakened to `20` for the consumer. -/
theorem overlap_speedyWalk_sqrt_perPair (hn : 21 ≤ n) {σ R : ℝ} (hσ : 0 < σ)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    {δ : ℝ} (hδ : 0 < δ) (hδσ : δ ≤ σ / (8 * Real.sqrt n))
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hRσ : R ≤ 4 * σ * Real.sqrt n)
    (hpos : ∀ x ∈ K, volume (Metric.ball x δ ∩ K) ≠ 0) :
    ∀ T : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet T →
      ∀ u v : EuclideanSpace ℝ (Fin n), u ∈ T → u ∈ K → v ∈ K → v ∉ T →
      ‖u - v‖ < δ / Real.sqrt n →
      densDist (Set.indicator K
        (fun x => (ell K δ x).toReal * gaussianWeightReal (σ ^ 2) x)) u v < 1 / 4 →
      1 ≤ 20 * (speedyWalk K δ u Tᶜ + speedyWalk K δ v T) := by
  intro T hT u v _ huK hvK _ hsep hd
  rw [densDist_indicator_of_mem huK hvK] at hd
  obtain ⟨h1, h2⟩ := ell_comparable_of_densDist hn hσ hδ hδσ hRσ hKR huK hvK
    (ell_ne_zero_of_volume_ball_inter_ne_zero hδ (hpos u huK))
    (ell_ne_zero_of_volume_ball_inter_ne_zero hδ (hpos v hvK)) hsep.le hd
  have h12 := one_le_twelve_mul_speedyWalk_add_of_comparable (by omega : 2 ≤ n) hK hKc hδ
    huK hvK hsep.le (hpos u huK)
    (max_volume_ball_inter_le_of_ell_comparable hδ h1 h2) hT
  refine le_trans h12 ?_
  gcongr
  norm_num

/-- **`Arlib.MarkovChains.hoverlap_speedyMetropolisGaussian` with `hcomp` discharged**, at
`s = σ²`, in exactly the binder shape `Arlib.MarkovChains.conductance_speedyGaussian_ge`'s
`hoverlap` demands once `h` is fixed to `1_K·ℓ·γ` — which is what
`Arlib.MarkovChains.hpi_ellGaussian` fixes it to.

The proof is the source proof with `hcomp u huK v hvK hsep` / `hcomp v hvK u huK hsep'`
replaced by the two halves of `ell_comparable_of_densDist`. -/
theorem hoverlap_speedyMetropolisGaussian_perPair (hn : 21 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hK0 : volume K ≠ 0)
    {σ δ R : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) (hδσ : δ ≤ σ / (8 * Real.sqrt n))
    (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hRσ : R ≤ 4 * σ * Real.sqrt n)
    (hfloor : 1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) * (1 / 8) * (2 / 3)) :
    ∀ T : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet T →
      ∀ u v : EuclideanSpace ℝ (Fin n), u ∈ T → u ∈ K → v ∈ K → v ∉ T →
      ‖u - v‖ < δ / Real.sqrt n →
      densDist (Set.indicator K
        (fun x => (ell K δ x).toReal * gaussianWeightReal (σ ^ 2) x)) u v < 1 / 4 →
      1 ≤ 20 * (speedyMetropolisGaussian K δ (σ ^ 2) u Tᶜ
        + speedyMetropolisGaussian K δ (σ ^ 2) v T) := by
  intro T hT u v _ huK hvK _ hsep hd
  rw [densDist_indicator_of_mem huK hvK] at hd
  obtain ⟨h1, h2⟩ := ell_comparable_of_densDist hn hσ hδ hδσ hRσ hKR huK hvK
    (ell_ne_zero_of_volume_ball_inter_ne_zero hδ
      (volume_ball_inter_ne_zero_of_convex hKc hKb hK0 huK hδ))
    (ell_ne_zero_of_volume_ball_inter_ne_zero hδ
      (volume_ball_inter_ne_zero_of_convex hKc hKb hK0 hvK hδ)) hsep.le hd
  exact one_le_twenty_mul_speedyMetropolisGaussian_add_of_comparable (by omega : 2 ≤ n)
    hK hKc hδ (by positivity : (0:ℝ) < σ ^ 2) hR huK hvK (hKR u huK) (hKR v hvK) hsep.le
    (volume_ball_inter_ne_zero_of_convex hKc hKb hK0 huK hδ)
    (max_volume_ball_inter_le_of_ell_comparable hδ h1 h2) hfloor hT

/-! ## 5. The conductance bound, with `hcomp` gone -/

/-- **`Arlib.MarkovChains.conductance_speedyMetropolisGaussian_ge` with `hcomp` removed**
(`SpeedyGaussianConductance.lean:523`):

    Φ(speedyMetropolisGaussian K δ σ²)  ≥  δ·ln 2 / (640·σ·√n)

with respect to `Arlib.MarkovChains.ellGaussianProb K δ σ²`.

Diff against the source, clause by clause: `hn : 2 ≤ n` becomes `hn : 21 ≤ n`, and `hcomp`
— the global `ℓ`-comparability premise, **refuted** by
`Arlib.MarkovChains.exists_ell_not_comparable_at_sqrt_dim_counterexample` — is **gone**,
discharged by `hoverlap_speedyMetropolisGaussian_perPair` from the `densDist h u v < 1/4`
that `hoverlap`'s own binder supplies.  Every other binder, including `hRσ : R ≤ 2σ√n`
(which implies the `R ≤ 4σ√n` of `lem:f-dist`), and the conclusion, are verbatim.

**One hypothesis remains, and this statement is conditional on it.  It is not a mixing-time
bound, not a spectral-gap bound and not a runtime claim, and may not be quoted as one.**

* `hellLip`/`hLσ` — log-Lipschitzness of `ℓ` on `K` at an explicit constant `Lf`, and its
  compatibility with `σ` and `R`.  These are **not** `hcomp`'s defect and do not dissolve the
  same way.  Cousins–Vempala's `thm:iso` (`vol3_journal.tex:467`) uses **no** Lipschitz
  control of `ℓ` anywhere: its density branch `d_h(u,v) ≥ 4d√n` is consumed inside the
  one-dimensional localization, by inequality `(1d-1)`.  The hypothesis enters this
  repository only through `Arlib.norm_sub_ge_of_densDist_weighted`
  (`Arlib/Convexity/IsoWeighted.lean:237`), which converts that density branch into a
  *metric* separation `‖u − v‖ ≥ 2√3·d` so that `Arlib.exists_disjoint_open_enlargement_weighted`
  can build disjoint enlargements.  It is therefore an artefact of the repository's proof
  route, not of the mathematics — but it is load-bearing for that route, so removing it means
  reproving isoperimetry by localization, which is out of this file's scope.

**UPDATE (same day): that reproof exists, and this theorem is superseded.**
`Arlib.conductance_speedyMetropolisGaussian_ge_uncond`
(`Arlib/Convexity/SpeedyGaussianUncond.lean`) is this statement with `hLf`, `hellLip` and
`hLσ` removed — same conclusion, same remaining binders — and it has an unconditional
witness.  Prefer it.  See `AUDIT.md` §0k. -/
theorem conductance_speedyMetropolisGaussian_ge_perPair (hn : 21 ≤ n) {σ δ R Lf : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ) (hδσ : δ ≤ σ / (8 * Real.sqrt n)) (hLf : 0 ≤ Lf)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hK0 : volume K ≠ 0) (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRσ : R ≤ 2 * σ * Real.sqrt n)
    (hellLip : ∀ u ∈ K, ∀ v ∈ K,
      (ell K δ u).toReal ≤ (ell K δ v).toReal * Real.exp (Lf * ‖u - v‖))
    (hLσ : Real.sqrt 3 * (σ ^ 2 * Lf + R) ≤ 2 * σ * Real.sqrt n) :
    ENNReal.ofReal (δ * Real.log 2 / (640 * σ * Real.sqrt n))
      ≤ conductance (speedyMetropolisGaussian K δ (σ ^ 2)) (ellGaussianProb K δ (σ ^ 2)) := by
  have hn2 : 2 ≤ n := by omega
  have hs : (0 : ℝ) < σ ^ 2 := by positivity
  have hR4 : R ≤ 4 * σ * Real.sqrt n := by
    have := Real.sqrt_nonneg (n : ℝ)
    nlinarith
  have hKcb : K ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
    intro x hx
    simpa [Metric.mem_closedBall, dist_eq_norm] using hKR x hx
  have hKb : Bornology.IsBounded K := Metric.isBounded_closedBall.subset hKcb
  have hKtop : volume K ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hKcb) measure_closedBall_lt_top)
  exact conductance_speedyGaussian_ge hn2 hσ hδ hδσ
    (fun x => Set.indicator_nonneg
      (fun y _ => mul_nonneg ENNReal.toReal_nonneg (gaussianWeightReal_pos _ y).le) x)
    (integral_ellGaussianIndicator_pos hs hK hKc hKb hK0 hKtop hδ)
    hK (speedyMetropolisGaussian K δ (σ ^ 2)) (ellGaussianProb K δ (σ ^ 2))
    (hpi_ellGaussian hs hK hKtop δ)
    (isReversible_speedyMetropolisGaussian_prob hK δ (σ ^ 2))
    (ellGaussianProb_compl_eq_zero hK δ (σ ^ 2))
    (hoverlap_speedyMetropolisGaussian_perPair hn hK hKc hKb hK0 hσ hδ hδσ hR hKR hR4
      (acceptance_floor_of_cv hn2 hσ hδ hδσ hRσ))
    (hiso_speedyMetropolisGaussian hn2 hσ hδ hLf hK hKc hKb hKR hK0 hellLip hLσ)

/-! ## 6. Non-vacuity -/

/-- **The hypothesis bundle of `ell_comparable_of_densDist` is satisfiable, at two *distinct*
points.**

`n = 21` (the threshold, met on the nose), `σ = 100`, `δ = 2`, `K = (1/2)·B₂₁`, `u = 0` and
`v = (1/4)e₀`.  On this body every proposal ball swallows `K` — `‖y − x‖ ≤ 1 < 2` for
`x, y ∈ K` — so `ℓ` is *constant* on `K`, and the density branch `d_h(u,v) < 1/4` reduces to
the Gaussian bracket of §1, which gives `d_h ≤ 1/8`.

This rules out the reading that `ell_comparable_of_densDist` is vacuous because its
`densDist` premise cannot hold away from the diagonal: it holds here with `u ≠ v`. -/
theorem ell_comparable_of_densDist_witness :
    ∃ (m : ℕ) (σ δ R : ℝ) (K : Set (EuclideanSpace ℝ (Fin m)))
      (u v : EuclideanSpace ℝ (Fin m)),
      21 ≤ m ∧ 0 < σ ∧ 0 < δ ∧ δ ≤ σ / (8 * Real.sqrt m) ∧ R ≤ 4 * σ * Real.sqrt m ∧
      (∀ x ∈ K, ‖x‖ ≤ R) ∧ u ∈ K ∧ v ∈ K ∧ ell K δ u ≠ 0 ∧ ell K δ v ≠ 0 ∧
      ‖u - v‖ ≤ δ / Real.sqrt m ∧
      densDist (fun x => (ell K δ x).toReal * gaussianWeightReal (σ ^ 2) x) u v < 1 / 4 ∧
      u ≠ v := by
  classical
  set K : Set (EuclideanSpace ℝ (Fin 21)) := Metric.closedBall 0 (1 / 2) with hKdef
  set v : EuclideanSpace ℝ (Fin 21) := EuclideanSpace.single ⟨0, by omega⟩ (1 / 4 : ℝ) with hvdef
  have hvn : ‖v‖ = 1 / 4 := by rw [hvdef, PiLp.norm_single]; norm_num
  have hmem : ∀ x : EuclideanSpace ℝ (Fin 21), x ∈ K ↔ ‖x‖ ≤ 1 / 2 := by
    intro x; rw [hKdef, Metric.mem_closedBall, dist_zero_right]
  have h0K : (0 : EuclideanSpace ℝ (Fin 21)) ∈ K := by rw [hmem]; simp
  have hvK : v ∈ K := by rw [hmem, hvn]; norm_num
  have hK0 : volume K ≠ 0 := by
    have : 0 < volume K :=
      lt_of_lt_of_le (Metric.measure_ball_pos volume 0 (by norm_num : (0 : ℝ) < 1 / 2))
        (measure_mono Metric.ball_subset_closedBall)
    exact this.ne'
  -- the proposal ball swallows `K`, so `ℓ` is constant on `K`
  have hswallow : ∀ x ∈ K, Metric.ball x (2 : ℝ) ∩ K = K := by
    intro x hx
    refine Set.inter_eq_right.2 fun y hy => ?_
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le y x
      _ ≤ 1 / 2 + 1 / 2 := by
          exact add_le_add ((hmem y).1 hy) ((hmem x).1 hx)
      _ < 2 := by norm_num
  have hellne : ∀ x ∈ K, ell K 2 x ≠ 0 := by
    intro x hx
    exact ell_ne_zero_of_volume_ball_inter_ne_zero (by norm_num)
      (by rw [hswallow x hx]; exact hK0)
  have helleq : ell K 2 (0 : EuclideanSpace ℝ (Fin 21)) = ell K 2 v := by
    rw [ell_apply, ell_apply, hswallow 0 h0K, hswallow v hvK,
      volume_ball_eq (0 : EuclideanSpace ℝ (Fin 21)) (2 : ℝ), volume_ball_eq v (2 : ℝ)]
  -- `√21` between `4` and `5`
  have hcast : Real.sqrt ((21 : ℕ) : ℝ) = Real.sqrt (21 : ℝ) := by norm_num
  have hnn : (0 : ℝ) ≤ Real.sqrt (21 : ℝ) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (21 : ℝ) ^ 2 = 21 := Real.sq_sqrt (by norm_num)
  have h4 : (4 : ℝ) ≤ Real.sqrt (21 : ℝ) := by nlinarith
  have h5 : Real.sqrt (21 : ℝ) ≤ 5 := by nlinarith
  have hδσ : (2 : ℝ) ≤ 100 / (8 * Real.sqrt ((21 : ℕ) : ℝ)) := by
    rw [hcast, le_div_iff₀ (by positivity)]; linarith
  have hRσ : (1 / 2 : ℝ) ≤ 4 * 100 * Real.sqrt ((21 : ℕ) : ℝ) := by rw [hcast]; linarith
  have hsep : ‖(0 : EuclideanSpace ℝ (Fin 21)) - v‖ ≤ 2 / Real.sqrt ((21 : ℕ) : ℝ) := by
    rw [zero_sub, norm_neg, hvn, hcast, le_div_iff₀ (by linarith)]; linarith
  refine ⟨21, 100, 2, 1 / 2, K, 0, v, le_refl _, by norm_num, by norm_num, hδσ, hRσ,
    fun x hx => (hmem x).1 hx, h0K, hvK, hellne _ h0K, hellne _ hvK, hsep, ?_, ?_⟩
  · -- the density branch, from the Gaussian bracket and the constancy of `ℓ`
    set A : ℝ := (ell K 2 (0 : EuclideanSpace ℝ (Fin 21))).toReal with hAdef
    have hAv : (ell K 2 v).toReal = A := by rw [hAdef, helleq]
    have hApos : 0 < A := ENNReal.toReal_pos (hellne _ h0K)
      (ne_top_of_le_ne_top ENNReal.one_ne_top (ell_le_one K 2 _))
    set a : ℝ := gaussianWeightReal ((100 : ℝ) ^ 2) (0 : EuclideanSpace ℝ (Fin 21)) with hadef
    set b : ℝ := gaussianWeightReal ((100 : ℝ) ^ 2) v with hbdef
    have hapos : 0 < a := gaussianWeightReal_pos _ _
    have hbpos : 0 < b := gaussianWeightReal_pos _ _
    have hab : a ≤ 9 / 8 * b :=
      gaussianWeightReal_le_of_cv (le_refl 21) (by norm_num) (by norm_num) hδσ hRσ
        (by simp) ((hmem v).1 hvK) hsep
    have hba : b ≤ 9 / 8 * a := by
      refine gaussianWeightReal_le_of_cv (le_refl 21) (by norm_num) (by norm_num) hδσ hRσ
        ((hmem v).1 hvK) (by simp) ?_
      rw [norm_sub_rev]; exact hsep
    simp only [densDist, hAv, ← hAdef, ← hadef, ← hbdef]
    rcases le_total (A * b) (A * a) with hle | hle
    · rw [max_eq_left hle, abs_of_nonneg (by linarith),
        div_lt_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)]
      nlinarith
    · rw [max_eq_right hle, abs_of_nonpos (by linarith),
        div_lt_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)]
      nlinarith
  · intro hc
    rw [← hc, norm_zero] at hvn
    norm_num at hvn

end Arlib.MarkovChains

/-! ## Axiom audit (`CLAUDE.md` §4) -/

#print axioms Arlib.MarkovChains.gaussianWeightReal_le_of_cv
#print axioms Arlib.MarkovChains.le_three_halves_of_densDist_mul_lt
#print axioms Arlib.MarkovChains.densDist_indicator_of_mem
#print axioms Arlib.MarkovChains.ell_le_of_toReal_le
#print axioms Arlib.MarkovChains.ell_comparable_of_densDist
#print axioms Arlib.MarkovChains.overlap_speedyWalk_sqrt_perPair
#print axioms Arlib.MarkovChains.hoverlap_speedyMetropolisGaussian_perPair
#print axioms Arlib.MarkovChains.conductance_speedyMetropolisGaussian_ge_perPair
#print axioms Arlib.MarkovChains.ell_comparable_of_densDist_witness
