/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Localisation for lower semicontinuous integrands — residual (C) of the assembly

`Arlib.Convexity.LocalizationAssembly` classifies every hypothesis of the localisation
conclusion and lists residual **(C) Lower semicontinuity** as genuinely open:

> The thin-tube comparison consumes a modulus-of-continuity hypothesis, not lower
> semicontinuity; the Lovász–Simonovits statement for merely lower semicontinuous integrable
> data needs an approximation step that is not carried out.  In the general-position form the
> integrands are asked to be *bounded continuous*.

This file carries out that approximation step.

## What is weakened, and to what

`Arlib.exists_needle_of_lowerSemicontinuous` takes the localisation conclusion for **bounded
continuous** data — the binder `hloc`, see "What is assumed" — and returns it with the second
integrand `g₂` only **bounded and lower semicontinuous**.  `Arlib.exists_needle_indicator_sub_smul`
and `Arlib.exists_needle_smul_indicator_sub_indicator` are the corollaries for integrands built
from indicator functions, which is what every downstream consumer applies localisation to:

* `g₂ = 1_S · f − c · f` for `S` **open** and `f` continuous nonnegative — the shape named in
  the task;
* `g₂ = c · 1_U · f − 1_F · f` for `U` **open**, `F` **closed**, `c ≥ 0` — the shape of
  `g₂ = (d/σ)·A·1_{S₂}h − 1_{S₃}h` in Cousins–Vempala's proof of `thm:iso`
  (`vol3_journal.tex:479–493`), and of the corresponding integrand in Lovász–Vempala's
  Theorem 4.2.

Neither integrand is continuous, so both are outside what the bounded-continuous form accepts.

The mechanism is the **Lipschitz minorant** (inf-convolution) `Arlib.lipschitzMinorant`:
`⨅ y, g y + n · dist x y` is `n`-Lipschitz, lies below `g`, and converges up to `g` pointwise
when `g` is lower semicontinuous and bounded below
(`Arlib.tendsto_lipschitzMinorant`).  Dominated convergence on a set of finite measure turns
that into `Arlib.exists_continuous_le_setIntegral_pos`: a bounded lower semicontinuous `g` with
`0 < ∫_K g` has a *continuous* minorant with the same bound and still-positive integral.  Both
the hypothesis `0 < ∫_K g₂` and the conclusion `0 < ∫ W · g₂ ∘ γ` are monotone increasing in the
integrand, so producing the needle for the minorant proves the statement for `g₂`.

## What is *not* weakened, and why not

**`g₁` — the integrand carrying the equality — stays continuous.**  The hypothesis `∫_K g₁ = 0`
is an equality, hence monotone in neither direction, and the needle that `hloc` returns depends
on the function fed to it, so no single approximation can transfer the conclusion
`∫ W · g₁ ∘ γ = 0` back.  What *is* provable is the equality with a prescribed slack:
`Arlib.exists_needle_of_lowerSemicontinuous_pair` allows `g₁` lower semicontinuous too and
concludes, for every `η > 0`,

`−η · ∫ W ≤ ∫ W · g₁ ∘ γ`  and  `0 < ∫ W · g₂ ∘ γ`,

the slack being exactly the re-centring constant of
`Arlib.exists_continuous_setIntegral_eq_zero`.  Since `η` is chosen *before* the needle, the
slack cannot be sent to `0` at a fixed needle; removing it would need a compactness statement
about the family of needles, which is a different development.

`Arlib.exists_needle_indicator_sub_smul_pair` is that statement specialised to
`g₁ = 1_S·f − A·f` with `S` open — the shape Cousins–Vempala put in the equality slot.  The
surviving inequality has the sign their contradiction consumes: `Arlib.needle_masses_contradiction`
uses `I₁ = A·I` only through `I₁ ≥ A·I`.

**This is the precise place where this file stops.**

## Where the indicator corollaries stop: open, not measurable

`1_S · f` is lower semicontinuous exactly when the open-set structure is there:
`Arlib.lowerSemicontinuous_indicator_of_isOpen` needs `S` open, and
`Arlib.lowerSemicontinuous_neg_indicator_of_isClosed` needs `F` closed for the *negative*
coefficient.  For a general measurable `S` no weakening of this file applies, and that is not a
gap in the proof but a fact about the objects: the Lipschitz minorants of `1_S` converge to the
lower semicontinuous envelope of `1_S`, which is `1_{interior S}`.  For `S` a fat Cantor set —
closed, positive measure, empty interior — every continuous minorant of `1_S` has nonpositive
integral, so `Arlib.exists_continuous_le_setIntegral_pos` has no analogue there.  Independently,
a needle is a *null* subset of the ambient space, so two integrands agreeing off a null set can
have entirely different needle integrals; a measurable set is only determined up to null sets by
its measure, and no approximation that is only good in measure can control a needle integral.

The passage from measurable sets to open ones therefore belongs to the **consumer**, where it is
a genuine reduction rather than an approximation: in Cousins–Vempala's `thm:iso` one replaces
`S₁, S₂` by open supersets (outer regularity of Lebesgue measure), which only enlarges
`π(S₁)·π(S₂)` and shrinks `S₃`, so the conclusion for the enlarged data implies it for the
original, provided the separation hypothesis is kept with a slightly smaller `d`.  That reduction
is *not* carried out here.

## Why not the `L¹`-density route

Density of bounded continuous functions in `L¹(μ)` is the other natural approximation.  It cannot
work: the needle integral `∫ W · g ∘ γ` is an integral over the one-dimensional image of `γ`,
which is `μ`-null, so an `L¹(μ)`-small perturbation of `g` can change it arbitrarily.  Only a
*pointwise* comparison survives the passage to the needle, which is why monotone approximation
from below is the route taken.

## What is assumed

Exactly one thing, and it appears only as the inline `∀`-binder `hloc` of every theorem in the
"needle" sections — never as a `def`, `structure`, `class` or named `Prop`:

> **`hloc`** — the localisation conclusion for **bounded continuous** integrands, in the form
> "from `∫_K f₁ = 0` and `0 < ∫_K f₂` produce a measurable needle `γ : ℝ → E` and a nonnegative
> *integrable* profile `W` with `∫ W · f₁ ∘ γ = 0` and `0 < ∫ W · f₂ ∘ γ`", together with
> whatever further property the localisation delivers, carried opaquely as an arbitrary
> `P : (ℝ → E) → (ℝ → ℝ) → Prop` (concavity of `W ^ (1/m)`, support in `[0,1]`, …).

Two remarks on that binder.

* It is stated at the level of the *starting body* `K`, not at the level of a localisation
  chain.  That is forced.  At the chain level the invariant is `ε · vol (D k) ≤ ∫_{D k} g₂` for
  **every** `k`, and passing to a minorant would need `sup_{D 0} (g₂ − minorant) ≤ ε/2`, i.e.
  *uniform* convergence of the minorants — which holds for continuous `g₂` (Dini) and fails for
  lower semicontinuous `g₂`.  So the approximation must happen before the chain is built, which
  is exactly where `hloc` sits.
* `Integrable W` is part of what `hloc` must deliver, and is not decorative: the transfer step
  compares `∫ W · f₂ ∘ γ` with `∫ W · g₂ ∘ γ`, and a Bochner integral of a non-integrable
  nonnegative function is `0`, not `+∞`, so the comparison would be false without it.  The `W`
  the repository's localisation stack produces is bounded with support in `[0,1]`
  (`Arlib.normalised_volume_slice_le`), hence integrable; but
  `Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_chain` does not currently *state* that,
  so discharging `hloc` from it needs that one extra conclusion exposed.

`Arlib.exists_needle_indicator_sub_smul_witness` discharges `hloc` on concrete data and checks
that every hypothesis of the indicator corollary can hold simultaneously, with a strictly
positive conclusion.

## Honesty note

The file contains exactly one `def`, `Arlib.lipschitzMinorant`, which is a plain explicit formula
(`⨅ y, g y + n · dist x y`); every property attributed to it is proved.  There is no `structure`,
`class` or named `Prop`, and nothing below asserts the Localization Lemma.
-/

open MeasureTheory Set Filter Metric

open scoped ENNReal Topology NNReal

namespace Arlib

/-! ### The Lipschitz minorants of a lower semicontinuous function -/

section LipschitzMinorant

variable {E : Type*} [PseudoMetricSpace E] [Nonempty E]

/-- **The `n`-th Lipschitz minorant (inf-convolution with `n · dist`).**

This is a plain explicit formula — `⨅ y, g y + n · dist x y` — and nothing is asserted about it
here.  For `g` bounded below it is `n`-Lipschitz, lies below `g`, and (for `g` lower
semicontinuous) converges pointwise up to `g`; all three are theorems below. -/
noncomputable def lipschitzMinorant (g : E → ℝ) (n : ℕ) (x : E) : ℝ :=
  ⨅ y : E, g y + n * dist x y

omit [Nonempty E] in
/-- The family whose infimum defines `Arlib.lipschitzMinorant` is bounded below. -/
theorem bddBelow_lipschitzMinorant {g : E → ℝ} {c : ℝ} (hc : ∀ y, c ≤ g y) (n : ℕ) (x : E) :
    BddBelow (Set.range fun y : E => g y + n * dist x y) := by
  refine ⟨c, ?_⟩
  rintro _ ⟨y, rfl⟩
  have h : (0 : ℝ) ≤ (n : ℝ) * dist x y := by positivity
  linarith [hc y]

omit [Nonempty E] in
/-- The Lipschitz minorant lies below `g`. -/
theorem lipschitzMinorant_le {g : E → ℝ} {c : ℝ} (hc : ∀ y, c ≤ g y) (n : ℕ) (x : E) :
    lipschitzMinorant g n x ≤ g x := by
  have h := ciInf_le (bddBelow_lipschitzMinorant hc n x) x
  simpa [lipschitzMinorant] using h

/-- The Lipschitz minorant inherits any lower bound of `g`. -/
theorem le_lipschitzMinorant {g : E → ℝ} {c : ℝ} (hc : ∀ y, c ≤ g y) (n : ℕ) (x : E) :
    c ≤ lipschitzMinorant g n x := by
  refine le_ciInf fun y => ?_
  have h : (0 : ℝ) ≤ (n : ℝ) * dist x y := by positivity
  linarith [hc y]

/-- **The Lipschitz minorant is `n`-Lipschitz.**  The triangle inequality, applied inside the
infimum. -/
theorem lipschitzWith_lipschitzMinorant {g : E → ℝ} {c : ℝ} (hc : ∀ y, c ≤ g y) (n : ℕ) :
    LipschitzWith (n : ℝ≥0) (lipschitzMinorant g n) := by
  refine LipschitzWith.of_le_add_mul (n : ℝ≥0) fun x z => ?_
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have key : ∀ y : E,
      lipschitzMinorant g n x - (n : ℝ) * dist x z ≤ g y + (n : ℝ) * dist z y := by
    intro y
    have h1 : lipschitzMinorant g n x ≤ g y + (n : ℝ) * dist x y :=
      ciInf_le (bddBelow_lipschitzMinorant hc n x) y
    have h2 : dist x y ≤ dist x z + dist z y := dist_triangle x z y
    nlinarith
  have h3 : lipschitzMinorant g n x - (n : ℝ) * dist x z ≤ lipschitzMinorant g n z :=
    le_ciInf key
  have hcast : ((n : ℝ≥0) : ℝ) = (n : ℝ) := by push_cast; ring
  rw [hcast]
  linarith

/-- The Lipschitz minorant is continuous. -/
theorem continuous_lipschitzMinorant {g : E → ℝ} {c : ℝ} (hc : ∀ y, c ≤ g y) (n : ℕ) :
    Continuous (lipschitzMinorant g n) :=
  (lipschitzWith_lipschitzMinorant hc n).continuous

/-- **The Lipschitz minorants of a lower semicontinuous function converge to it pointwise.**

This is the approximation-from-below that the localisation conclusion consumes: `g` lower
semicontinuous and bounded below is the pointwise limit of the increasing sequence of Lipschitz
functions `Arlib.lipschitzMinorant g n`, each of which lies below `g`. -/
theorem tendsto_lipschitzMinorant {g : E → ℝ} {c : ℝ} (hc : ∀ y, c ≤ g y)
    (hg : LowerSemicontinuous g) (x : E) :
    Tendsto (fun n : ℕ => lipschitzMinorant g n x) atTop (𝓝 (g x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- lower semicontinuity gives a ball on which `g` stays above `g x - ε/2`
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ > 0, ∀ y : E, dist y x < δ → g x - ε / 2 < g y := by
    have h := hg x (g x - ε / 2) (by linarith)
    rw [Metric.eventually_nhds_iff] at h
    obtain ⟨δ, hδpos, hδ⟩ := h
    exact ⟨δ, hδpos, fun y hy => hδ hy⟩
  obtain ⟨N, hN⟩ := exists_nat_ge ((g x - c) / δ)
  refine ⟨N, fun n hn => ?_⟩
  have hle : lipschitzMinorant g n x ≤ g x := lipschitzMinorant_le hc n x
  have hge : g x - ε / 2 ≤ lipschitzMinorant g n x := by
    refine le_ciInf fun y => ?_
    rcases lt_or_ge (dist x y) δ with hlt | hge'
    · have hy : dist y x < δ := by rwa [dist_comm]
      have h1 := hδ y hy
      have h2 : (0 : ℝ) ≤ (n : ℝ) * dist x y := by positivity
      linarith
    · have hNn : ((g x - c) / δ) ≤ (n : ℝ) := le_trans hN (Nat.cast_le.mpr hn)
      have hgxc : g x - c ≤ (n : ℝ) * δ := by
        rw [div_le_iff₀ hδpos] at hNn
        linarith
      have hmono : (n : ℝ) * δ ≤ (n : ℝ) * dist x y :=
        mul_le_mul_of_nonneg_left hge' (Nat.cast_nonneg n)
      linarith [hc y]
  rw [Real.dist_eq, abs_of_nonpos (by linarith)]
  linarith

end LipschitzMinorant

/-! ### Approximation from below, inside the integral -/

section Approximation

variable {E : Type*} [PseudoMetricSpace E] [Nonempty E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {μ : Measure E}

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
/-- The Lipschitz minorants of a bounded `g` are bounded by the same constant. -/
theorem abs_lipschitzMinorant_le {g : E → ℝ} {M : ℝ} (hM : ∀ x, |g x| ≤ M) (n : ℕ) (x : E) :
    |lipschitzMinorant g n x| ≤ M := by
  have hc : ∀ y, -M ≤ g y := fun y => (abs_le.mp (hM y)).1
  exact abs_le.mpr ⟨le_lipschitzMinorant hc n x,
    le_trans (lipschitzMinorant_le hc n x) (abs_le.mp (hM x)).2⟩

/-- **The set integrals of the Lipschitz minorants converge.**

Dominated convergence on a set of finite measure, the dominating function being the constant
bound of `g`. -/
theorem tendsto_setIntegral_lipschitzMinorant {K : Set E} (hKfin : μ K ≠ ⊤)
    {g : E → ℝ} (hg : LowerSemicontinuous g) {M : ℝ} (hM : ∀ x, |g x| ≤ M) :
    Tendsto (fun n : ℕ => ∫ x in K, lipschitzMinorant g n x ∂μ) atTop
      (𝓝 (∫ x in K, g x ∂μ)) := by
  have hc : ∀ y, -M ≤ g y := fun y => (abs_le.mp (hM y)).1
  haveI : IsFiniteMeasure (μ.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hKfin⟩
  refine tendsto_integral_of_dominated_convergence (fun _ => M)
    (fun n => (continuous_lipschitzMinorant hc n).aestronglyMeasurable)
    (integrable_const M) (fun n => Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => tendsto_lipschitzMinorant hc hg x)
  simpa [Real.norm_eq_abs] using abs_lipschitzMinorant_le hM n x

/-- **Approximation from below at a strictly positive integral.**

A bounded lower semicontinuous `g` with `0 < ∫_K g` has a *continuous* minorant with the same
bound and a strictly positive integral.  This is the whole content of the approximation step the
Lovász–Simonovits statement for lower semicontinuous data needs: the hypothesis `0 < ∫_K g` is
monotone increasing in `g`, so it survives the passage to a minorant, and so does the
conclusion. -/
theorem exists_continuous_le_setIntegral_pos {K : Set E} (hKfin : μ K ≠ ⊤)
    {g : E → ℝ} (hg : LowerSemicontinuous g) {M : ℝ} (hM : ∀ x, |g x| ≤ M)
    (hpos : 0 < ∫ x in K, g x ∂μ) :
    ∃ f : E → ℝ, Continuous f ∧ (∀ x, f x ≤ g x) ∧ (∀ x, |f x| ≤ M) ∧
      0 < ∫ x in K, f x ∂μ := by
  have hc : ∀ y, -M ≤ g y := fun y => (abs_le.mp (hM y)).1
  have hlim := tendsto_setIntegral_lipschitzMinorant (μ := μ) hKfin hg hM
  obtain ⟨n, hn⟩ := ((tendsto_order.mp hlim).1 0 hpos).exists
  exact ⟨lipschitzMinorant g n, continuous_lipschitzMinorant hc n,
    fun x => lipschitzMinorant_le hc n x, fun x => abs_lipschitzMinorant_le hM n x, hn⟩

/-- **Approximation from below at a vanishing integral, after re-centering.**

The equality `∫_K g = 0` is *not* monotone in `g`, so a minorant cannot preserve it; what it can
preserve is the equality up to an additive constant.  For a bounded lower semicontinuous `g` with
`∫_K g = 0` and any `η > 0` there is a *continuous* `f` with `∫_K f = 0` exactly, and
`f - η ≤ f - κ ≤ g` for a constant `κ ∈ [0, η]`.

This is the exact point at which the equality form degrades: the localisation conclusion for `f`
transfers to `g` only up to the slack `κ · ∫ W`. -/
theorem exists_continuous_setIntegral_eq_zero {K : Set E} (hKfin : μ K ≠ ⊤) (hK0 : μ K ≠ 0)
    {g : E → ℝ} (hg : LowerSemicontinuous g) {M : ℝ} (hM : ∀ x, |g x| ≤ M)
    (hzero : (∫ x in K, g x ∂μ) = 0) {η : ℝ} (hη : 0 < η) :
    ∃ (f : E → ℝ) (κ : ℝ), Continuous f ∧ 0 ≤ κ ∧ κ ≤ η ∧ (∀ x, f x - κ ≤ g x) ∧
      (∀ x, |f x| ≤ M + η) ∧ (∫ x in K, f x ∂μ) = 0 := by
  have hc : ∀ y, -M ≤ g y := fun y => (abs_le.mp (hM y)).1
  have hVpos : 0 < (μ K).toReal := ENNReal.toReal_pos hK0 hKfin
  haveI : IsFiniteMeasure (μ.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hKfin⟩
  have hlim := tendsto_setIntegral_lipschitzMinorant (μ := μ) hKfin hg hM
  rw [hzero] at hlim
  obtain ⟨n, hn⟩ :
      ∃ n : ℕ, -(η * (μ K).toReal) < ∫ x in K, lipschitzMinorant g n x ∂μ :=
    ((tendsto_order.mp hlim).1 _ (by nlinarith)).exists
  set m : E → ℝ := lipschitzMinorant g n with hm
  have hmc : Continuous m := continuous_lipschitzMinorant hc n
  have hmle : ∀ x, m x ≤ g x := fun x => lipschitzMinorant_le hc n x
  have hmb : ∀ x, |m x| ≤ M := fun x => abs_lipschitzMinorant_le hM n x
  have hmint : IntegrableOn m K μ :=
    Measure.integrableOn_of_bounded hKfin hmc.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hmb x)
  have hgint : IntegrableOn g K μ :=
    Measure.integrableOn_of_bounded hKfin (hg.measurable.aestronglyMeasurable)
      (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hM x)
  have hle0 : (∫ x in K, m x ∂μ) ≤ 0 := by
    rw [← hzero]
    exact integral_mono hmint hgint hmle
  set κ : ℝ := -(∫ x in K, m x ∂μ) / (μ K).toReal with hκ
  have hκ0 : 0 ≤ κ := div_nonneg (by linarith) hVpos.le
  have hκη : κ ≤ η := by
    rw [hκ, div_le_iff₀ hVpos]
    linarith
  refine ⟨fun x => m x + κ, κ, hmc.add continuous_const, hκ0, hκη, fun x => by
    simpa using hmle x, fun x => ?_, ?_⟩
  · have h1 := abs_le.mp (hmb x)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [integral_add hmint (integrableOn_const (C := κ) hKfin),
      setIntegral_const, smul_eq_mul, Measure.real, hκ]
    field_simp
    ring

end Approximation

/-! ### The localisation conclusion for lower semicontinuous integrands -/

section Needle

variable {E : Type*} [PseudoMetricSpace E] [Nonempty E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E}

omit [PseudoMetricSpace E] [Nonempty E] [BorelSpace E] in
/-- Along a measurable needle, a nonnegative integrable profile integrates any bounded measurable
integrand. -/
theorem integrable_profile_mul {γ : ℝ → E} (hγ : Measurable γ) {W : ℝ → ℝ}
    (hWi : Integrable W) {f : E → ℝ} (hfm : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) :
    Integrable fun t : ℝ => W t * f (γ t) :=
  hWi.mul_bdd (hfm.comp hγ).aestronglyMeasurable
    (Eventually.of_forall fun t => by simpa [Real.norm_eq_abs] using hM (γ t))

omit [PseudoMetricSpace E] [Nonempty E] [BorelSpace E] in
/-- Monotonicity of the needle integral in the integrand. -/
theorem needleIntegral_mono {γ : ℝ → E} (hγ : Measurable γ) {W : ℝ → ℝ} (hWi : Integrable W)
    (hW0 : ∀ t, 0 ≤ W t) {f g : E → ℝ} (hfm : Measurable f) (hgm : Measurable g) {M : ℝ}
    (hMf : ∀ x, |f x| ≤ M) (hMg : ∀ x, |g x| ≤ M) (hfg : ∀ x, f x ≤ g x) :
    (∫ t : ℝ, W t * f (γ t)) ≤ ∫ t : ℝ, W t * g (γ t) :=
  integral_mono (integrable_profile_mul hγ hWi hfm hMf) (integrable_profile_mul hγ hWi hgm hMg)
    fun t => mul_le_mul_of_nonneg_left (hfg (γ t)) (hW0 t)

/-- **The localisation conclusion with the second integrand merely lower semicontinuous.**

`hloc` is the localisation lemma for *bounded continuous* data, in the shape the assembly of
`Arlib.Convexity.LocalizationAssembly` targets: from `∫_K f₁ = 0` and `0 < ∫_K f₂` it produces a
needle `γ` carrying a nonnegative integrable profile `W` (with whatever extra property `P`
records — concavity of `W ^ (1/m)`, support in `[0,1]`, …) such that `∫ W · f₁ ∘ γ = 0` and
`0 < ∫ W · f₂ ∘ γ`.

The theorem removes the continuity restriction on `g₂`: it may be **lower semicontinuous** and
bounded.  Both the hypothesis `0 < ∫_K g₂` and the conclusion `0 < ∫ W · g₂ ∘ γ` are monotone
increasing in the integrand, so a continuous minorant
(`Arlib.exists_continuous_le_setIntegral_pos`) carries the whole argument: the needle is produced
for the minorant and the conclusion is inherited by `g₂`.  `g₁` is passed to `hloc` untouched.

**Why not an `L¹` approximation.**  The needle integral `∫ W · g ∘ γ` is an integral over a
one-dimensional set, which is null in `E`; two integrands that agree outside an `E`-null set can
have completely different needle integrals.  So density of continuous functions in `L¹(μ)` — the
other natural route — carries no information here, and monotone approximation from below is the
only one that survives the passage to the needle. -/
theorem exists_needle_of_lowerSemicontinuous {K : Set E} (hKfin : μ K ≠ ⊤)
    {P : (ℝ → E) → (ℝ → ℝ) → Prop} {g₁ g₂ : E → ℝ} {M : ℝ}
    (hg₁ : Continuous g₁) (hM₁ : ∀ x, |g₁ x| ≤ M)
    (hg₂ : LowerSemicontinuous g₂) (hM₂ : ∀ x, |g₂ x| ≤ M)
    (hzero : (∫ x in K, g₁ x ∂μ) = 0) (hpos : 0 < ∫ x in K, g₂ x ∂μ)
    (hloc : ∀ (f₁ f₂ : E → ℝ) (M' : ℝ), Continuous f₁ → Continuous f₂ →
      (∀ x, |f₁ x| ≤ M') → (∀ x, |f₂ x| ≤ M') →
      (∫ x in K, f₁ x ∂μ) = 0 → 0 < (∫ x in K, f₂ x ∂μ) →
      ∃ (γ : ℝ → E) (W : ℝ → ℝ), Measurable γ ∧ (∀ t, 0 ≤ W t) ∧ Integrable W ∧ P γ W ∧
        (∫ t : ℝ, W t * f₁ (γ t)) = 0 ∧ 0 < ∫ t : ℝ, W t * f₂ (γ t)) :
    ∃ (γ : ℝ → E) (W : ℝ → ℝ), Measurable γ ∧ (∀ t, 0 ≤ W t) ∧ Integrable W ∧ P γ W ∧
      (∫ t : ℝ, W t * g₁ (γ t)) = 0 ∧ 0 < ∫ t : ℝ, W t * g₂ (γ t) := by
  obtain ⟨f₂, hf₂c, hf₂le, hf₂b, hf₂pos⟩ :=
    exists_continuous_le_setIntegral_pos hKfin hg₂ hM₂ hpos
  obtain ⟨γ, W, hγ, hW0, hWi, hP, hW₁, hW₂⟩ :=
    hloc g₁ f₂ M hg₁ hf₂c hM₁ hf₂b hzero hf₂pos
  refine ⟨γ, W, hγ, hW0, hWi, hP, hW₁, lt_of_lt_of_le hW₂ ?_⟩
  exact needleIntegral_mono hγ hWi hW0 hf₂c.measurable hg₂.measurable hf₂b hM₂ hf₂le

/-- **Both integrands lower semicontinuous — the equality degrades to an `η`-slack.**

With `g₁` lower semicontinuous rather than continuous the conclusion `∫ W · g₁ ∘ γ = 0` is no
longer available, and this is not an artefact of the proof: the hypothesis `∫_K g₁ = 0` is an
*equality*, so it is preserved neither by passing to a minorant nor by passing to a majorant, and
the needle produced by `hloc` depends on the function fed to it.  What survives is the equality
up to a prescribed slack: for every `η > 0` there is a needle with

`−η · ∫ W ≤ ∫ W · g₁ ∘ γ` and `0 < ∫ W · g₂ ∘ γ`.

The mechanism is `Arlib.exists_continuous_setIntegral_eq_zero`: a continuous minorant of `g₁`
re-centred by a constant `κ ∈ [0, η]` has integral exactly `0` over `K`, and the re-centring
constant is exactly the slack. -/
theorem exists_needle_of_lowerSemicontinuous_pair {K : Set E} (hKfin : μ K ≠ ⊤) (hK0 : μ K ≠ 0)
    {P : (ℝ → E) → (ℝ → ℝ) → Prop} {g₁ g₂ : E → ℝ} {M : ℝ}
    (hg₁ : LowerSemicontinuous g₁) (hM₁ : ∀ x, |g₁ x| ≤ M)
    (hg₂ : LowerSemicontinuous g₂) (hM₂ : ∀ x, |g₂ x| ≤ M)
    (hzero : (∫ x in K, g₁ x ∂μ) = 0) (hpos : 0 < ∫ x in K, g₂ x ∂μ)
    {η : ℝ} (hη : 0 < η)
    (hloc : ∀ (f₁ f₂ : E → ℝ) (M' : ℝ), Continuous f₁ → Continuous f₂ →
      (∀ x, |f₁ x| ≤ M') → (∀ x, |f₂ x| ≤ M') →
      (∫ x in K, f₁ x ∂μ) = 0 → 0 < (∫ x in K, f₂ x ∂μ) →
      ∃ (γ : ℝ → E) (W : ℝ → ℝ), Measurable γ ∧ (∀ t, 0 ≤ W t) ∧ Integrable W ∧ P γ W ∧
        (∫ t : ℝ, W t * f₁ (γ t)) = 0 ∧ 0 < ∫ t : ℝ, W t * f₂ (γ t)) :
    ∃ (γ : ℝ → E) (W : ℝ → ℝ), Measurable γ ∧ (∀ t, 0 ≤ W t) ∧ Integrable W ∧ P γ W ∧
      -(η * ∫ t : ℝ, W t) ≤ (∫ t : ℝ, W t * g₁ (γ t)) ∧ 0 < ∫ t : ℝ, W t * g₂ (γ t) := by
  obtain ⟨f₁, κ, hf₁c, hκ0, hκη, hf₁le, hf₁b, hf₁zero⟩ :=
    exists_continuous_setIntegral_eq_zero hKfin hK0 hg₁ hM₁ hzero hη
  obtain ⟨f₂, hf₂c, hf₂le, hf₂b, hf₂pos⟩ :=
    exists_continuous_le_setIntegral_pos hKfin hg₂ hM₂ hpos
  obtain ⟨γ, W, hγ, hW0, hWi, hP, hW₁, hW₂⟩ :=
    hloc f₁ f₂ (M + η) hf₁c hf₂c hf₁b
      (fun x => le_trans (hf₂b x) (by linarith)) hf₁zero hf₂pos
  refine ⟨γ, W, hγ, hW0, hWi, hP, ?_,
    lt_of_lt_of_le hW₂ (needleIntegral_mono hγ hWi hW0 hf₂c.measurable hg₂.measurable
      hf₂b hM₂ hf₂le)⟩
  -- the re-centred minorant `f₁ - κ` lies below `g₁`, and its needle integral is `-κ · ∫ W`
  have hWnn : 0 ≤ ∫ t : ℝ, W t := integral_nonneg hW0
  have hint₁ : Integrable fun t : ℝ => W t * f₁ (γ t) :=
    integrable_profile_mul hγ hWi hf₁c.measurable hf₁b
  have hintκ : Integrable fun t : ℝ => κ * W t := hWi.const_mul κ
  have hshift : (∫ t : ℝ, W t * (f₁ (γ t) - κ)) = -(κ * ∫ t : ℝ, W t) := by
    have hfun : (fun t : ℝ => W t * (f₁ (γ t) - κ))
        = fun t : ℝ => W t * f₁ (γ t) - κ * W t := by funext t; ring
    rw [hfun, integral_sub hint₁ hintκ, integral_const_mul, hW₁, zero_sub]
  have hmono : (∫ t : ℝ, W t * (f₁ (γ t) - κ)) ≤ ∫ t : ℝ, W t * g₁ (γ t) := by
    refine needleIntegral_mono hγ hWi hW0 (f := fun x => f₁ x - κ) (g := g₁)
      (hf₁c.sub continuous_const).measurable
      hg₁.measurable (M := M + 2 * η) (fun x => ?_) (fun x => ?_) (fun x => hf₁le x)
    · have h := abs_le.mp (hf₁b x)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · have h := abs_le.mp (hM₁ x)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  rw [hshift] at hmono
  refine le_trans ?_ hmono
  have : κ * (∫ t : ℝ, W t) ≤ η * ∫ t : ℝ, W t :=
    mul_le_mul_of_nonneg_right hκη hWnn
  linarith

end Needle

/-! ### Integrands built from indicator functions -/

section Indicator

variable {E : Type*} [TopologicalSpace E]

/-- **`1_S · f` is lower semicontinuous for `S` open and `f` continuous nonnegative.**

Mathlib's `IsOpen.lowerSemicontinuous_indicator` covers only a *constant* value; the localisation
consumers need a continuous weight. -/
theorem lowerSemicontinuous_indicator_of_isOpen {S : Set E} (hS : IsOpen S) {f : E → ℝ}
    (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) : LowerSemicontinuous (S.indicator f) := by
  intro x y hy
  by_cases hx : x ∈ S
  · have hfx : y < f x := by rwa [Set.indicator_of_mem hx] at hy
    have hopen : IsOpen (S ∩ f ⁻¹' Set.Ioi y) := hS.inter (isOpen_Ioi.preimage hf)
    filter_upwards [hopen.mem_nhds ⟨hx, hfx⟩] with x' hx'
    rw [Set.indicator_of_mem hx'.1]
    exact hx'.2
  · have hy0 : y < 0 := by rwa [Set.indicator_of_notMem hx] at hy
    refine Eventually.of_forall fun x' => ?_
    show y < S.indicator f x'
    by_cases h : x' ∈ S
    · rw [Set.indicator_of_mem h]; exact lt_of_lt_of_le hy0 (hf0 x')
    · rw [Set.indicator_of_notMem h]; exact hy0

/-- **`-1_F · f` is lower semicontinuous for `F` closed and `f` continuous nonnegative.**

Equivalently `1_F · f` is *upper* semicontinuous.  This is the sign in which a set with a
*negative* coefficient enters a lower semicontinuous integrand — in the Cousins–Vempala
application, the set `S₃` of `g₂ = (d/σ)A·1_{S₂}h − 1_{S₃}h`. -/
theorem lowerSemicontinuous_neg_indicator_of_isClosed {F : Set E} (hF : IsClosed F) {f : E → ℝ}
    (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) :
    LowerSemicontinuous fun x => -F.indicator f x := by
  intro x y hy
  replace hy : y < -F.indicator f x := hy
  by_cases hx : x ∈ F
  · have hfx : y < -f x := by rwa [Set.indicator_of_mem hx] at hy
    have hopen : IsOpen {z : E | y < -f z} := isOpen_Ioi.preimage hf.neg
    filter_upwards [hopen.mem_nhds hfx] with x' hx'
    show y < -F.indicator f x'
    by_cases h : x' ∈ F
    · rw [Set.indicator_of_mem h]; exact hx'
    · rw [Set.indicator_of_notMem h, neg_zero]
      have h0 : -f x ≤ 0 := neg_nonpos.mpr (hf0 x)
      linarith
  · have hy0 : y < 0 := by
      rw [Set.indicator_of_notMem hx, neg_zero] at hy; exact hy
    filter_upwards [hF.isOpen_compl.mem_nhds hx] with x' hx'
    show y < -F.indicator f x'
    rw [Set.indicator_of_notMem hx', neg_zero]
    exact hy0

/-- **The shape the task names: `1_S · f − c · f` is lower semicontinuous for `S` open.**

`f` is continuous and nonnegative; `c` is an arbitrary real, because `−c·f` is continuous and a
continuous function is lower semicontinuous. -/
theorem lowerSemicontinuous_indicator_sub_smul {S : Set E} (hS : IsOpen S) {f : E → ℝ}
    (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) (c : ℝ) :
    LowerSemicontinuous fun x => S.indicator f x - c * f x := by
  have h1 := lowerSemicontinuous_indicator_of_isOpen hS hf hf0
  have h2 : LowerSemicontinuous fun x : E => -(c * f x) :=
    ((continuous_const.mul hf).neg).lowerSemicontinuous
  simpa [sub_eq_add_neg] using h1.add h2

omit [TopologicalSpace E] in
/-- Scaling an indicator by a constant is the indicator of the scaled weight. -/
theorem const_mul_indicator {S : Set E} (f : E → ℝ) (c : ℝ) :
    (fun x => c * S.indicator f x) = S.indicator fun x => c * f x := by
  funext x
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]

/-- **The Cousins–Vempala integrand `c·1_U·f − 1_F·f` is lower semicontinuous** when `U` is open,
`F` is closed, `f` is continuous nonnegative and `c ≥ 0`.

This is exactly the shape of `g₂ = (d/σ)·A·1_{S₂}h − 1_{S₃}h` at `vol3_journal.tex:479–493`,
with `S₂` open and `S₃` closed. -/
theorem lowerSemicontinuous_smul_indicator_sub_indicator {U F : Set E} (hU : IsOpen U)
    (hF : IsClosed F) {f : E → ℝ} (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) {c : ℝ} (hc : 0 ≤ c) :
    LowerSemicontinuous fun x => c * U.indicator f x - F.indicator f x := by
  have h1 : LowerSemicontinuous fun x : E => c * U.indicator f x := by
    rw [const_mul_indicator]
    exact lowerSemicontinuous_indicator_of_isOpen hU (continuous_const.mul hf)
      fun x => mul_nonneg hc (hf0 x)
  have h2 := lowerSemicontinuous_neg_indicator_of_isClosed hF hf hf0
  simpa [sub_eq_add_neg] using h1.add h2

end Indicator

/-! ### The indicator corollaries -/

section IndicatorNeedle

variable {E : Type*} [PseudoMetricSpace E] [Nonempty E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E}

/-- **The corollary the consumers need: an indicator-built integrand.**

`Arlib.exists_needle_of_lowerSemicontinuous` specialised to
`g₂ = 1_S · f − c · f`, for `S` **open**, `f` continuous and nonnegative, and an arbitrary real
`c` — an integrand that is *not continuous*, which is precisely what the bounded-continuous form
of the localisation conclusion cannot accept.

Openness of `S` is not a convenience: see the module docstring, "Where this stops". -/
theorem exists_needle_indicator_sub_smul {K : Set E} (hKfin : μ K ≠ ⊤)
    {P : (ℝ → E) → (ℝ → ℝ) → Prop} {g₁ : E → ℝ} {M : ℝ}
    (hg₁ : Continuous g₁) (hM₁ : ∀ x, |g₁ x| ≤ M)
    {S : Set E} (hS : IsOpen S) {f : E → ℝ} (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) {c : ℝ}
    (hM₂ : ∀ x, |S.indicator f x - c * f x| ≤ M)
    (hzero : (∫ x in K, g₁ x ∂μ) = 0)
    (hpos : 0 < ∫ x in K, (S.indicator f x - c * f x) ∂μ)
    (hloc : ∀ (f₁ f₂ : E → ℝ) (M' : ℝ), Continuous f₁ → Continuous f₂ →
      (∀ x, |f₁ x| ≤ M') → (∀ x, |f₂ x| ≤ M') →
      (∫ x in K, f₁ x ∂μ) = 0 → 0 < (∫ x in K, f₂ x ∂μ) →
      ∃ (γ : ℝ → E) (W : ℝ → ℝ), Measurable γ ∧ (∀ t, 0 ≤ W t) ∧ Integrable W ∧ P γ W ∧
        (∫ t : ℝ, W t * f₁ (γ t)) = 0 ∧ 0 < ∫ t : ℝ, W t * f₂ (γ t)) :
    ∃ (γ : ℝ → E) (W : ℝ → ℝ), Measurable γ ∧ (∀ t, 0 ≤ W t) ∧ Integrable W ∧ P γ W ∧
      (∫ t : ℝ, W t * g₁ (γ t)) = 0 ∧
      0 < ∫ t : ℝ, W t * (S.indicator f (γ t) - c * f (γ t)) :=
  exists_needle_of_lowerSemicontinuous hKfin hg₁ hM₁
    (lowerSemicontinuous_indicator_sub_smul hS hf hf0 c) hM₂ hzero hpos hloc

/-- **The Cousins–Vempala shape.**

`g₂ = c·1_U·f − 1_F·f` with `U` open, `F` closed, `f` continuous nonnegative and `c ≥ 0` — the
shape of `g₂ = (d/σ)·A·1_{S₂}h − 1_{S₃}h` at `vol3_journal.tex:479–493`. -/
theorem exists_needle_smul_indicator_sub_indicator {K : Set E} (hKfin : μ K ≠ ⊤)
    {P : (ℝ → E) → (ℝ → ℝ) → Prop} {g₁ : E → ℝ} {M : ℝ}
    (hg₁ : Continuous g₁) (hM₁ : ∀ x, |g₁ x| ≤ M)
    {U F : Set E} (hU : IsOpen U) (hF : IsClosed F) {f : E → ℝ} (hf : Continuous f)
    (hf0 : ∀ x, 0 ≤ f x) {c : ℝ} (hc : 0 ≤ c)
    (hM₂ : ∀ x, |c * U.indicator f x - F.indicator f x| ≤ M)
    (hzero : (∫ x in K, g₁ x ∂μ) = 0)
    (hpos : 0 < ∫ x in K, (c * U.indicator f x - F.indicator f x) ∂μ)
    (hloc : ∀ (f₁ f₂ : E → ℝ) (M' : ℝ), Continuous f₁ → Continuous f₂ →
      (∀ x, |f₁ x| ≤ M') → (∀ x, |f₂ x| ≤ M') →
      (∫ x in K, f₁ x ∂μ) = 0 → 0 < (∫ x in K, f₂ x ∂μ) →
      ∃ (γ : ℝ → E) (W : ℝ → ℝ), Measurable γ ∧ (∀ t, 0 ≤ W t) ∧ Integrable W ∧ P γ W ∧
        (∫ t : ℝ, W t * f₁ (γ t)) = 0 ∧ 0 < ∫ t : ℝ, W t * f₂ (γ t)) :
    ∃ (γ : ℝ → E) (W : ℝ → ℝ), Measurable γ ∧ (∀ t, 0 ≤ W t) ∧ Integrable W ∧ P γ W ∧
      (∫ t : ℝ, W t * g₁ (γ t)) = 0 ∧
      0 < ∫ t : ℝ, W t * (c * U.indicator f (γ t) - F.indicator f (γ t)) :=
  exists_needle_of_lowerSemicontinuous hKfin hg₁ hM₁
    (lowerSemicontinuous_smul_indicator_sub_indicator hU hF hf hf0 hc) hM₂ hzero hpos hloc

/-- **The indicator in the *equality* slot, with its unavoidable slack.**

Cousins–Vempala apply localisation with `g₁ = 1_{S₁}h − A·h`, an integrand built from the
indicator of a set, in the slot that carries the **equality** `∫ W · g₁ ∘ γ = 0`.  This corollary
is what this file can give there: for `S` **open** the equality becomes

`−η · ∫ W ≤ ∫ W · (1_S·f − A·f) ∘ γ`,

for a slack `η > 0` chosen in advance.  See "What is *not* weakened, and why not" in the module
docstring for why the slack cannot be removed by this route: the needle produced by `hloc`
depends on the function fed to it, so `η` cannot be sent to `0` at a fixed needle.

Note the *sign* of the surviving inequality is the useful one for the Cousins–Vempala
contradiction, which consumes `I₁ = A·I` only through `I₁ ≥ A·I`
(`Arlib.needle_masses_contradiction`: from `c·(I₁·I₂) ≤ I·I₃ < I·(c·A·I₂)`, any lower bound on
`I₁` suffices when `c ≥ 0` and `I₂ ≥ 0`). -/
theorem exists_needle_indicator_sub_smul_pair {K : Set E} (hKfin : μ K ≠ ⊤) (hK0 : μ K ≠ 0)
    {P : (ℝ → E) → (ℝ → ℝ) → Prop} {M : ℝ}
    {S : Set E} (hS : IsOpen S) {f : E → ℝ} (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) {A : ℝ}
    (hM₁ : ∀ x, |S.indicator f x - A * f x| ≤ M)
    {g₂ : E → ℝ} (hg₂ : LowerSemicontinuous g₂) (hM₂ : ∀ x, |g₂ x| ≤ M)
    (hzero : (∫ x in K, (S.indicator f x - A * f x) ∂μ) = 0)
    (hpos : 0 < ∫ x in K, g₂ x ∂μ) {η : ℝ} (hη : 0 < η)
    (hloc : ∀ (f₁ f₂ : E → ℝ) (M' : ℝ), Continuous f₁ → Continuous f₂ →
      (∀ x, |f₁ x| ≤ M') → (∀ x, |f₂ x| ≤ M') →
      (∫ x in K, f₁ x ∂μ) = 0 → 0 < (∫ x in K, f₂ x ∂μ) →
      ∃ (γ : ℝ → E) (W : ℝ → ℝ), Measurable γ ∧ (∀ t, 0 ≤ W t) ∧ Integrable W ∧ P γ W ∧
        (∫ t : ℝ, W t * f₁ (γ t)) = 0 ∧ 0 < ∫ t : ℝ, W t * f₂ (γ t)) :
    ∃ (γ : ℝ → E) (W : ℝ → ℝ), Measurable γ ∧ (∀ t, 0 ≤ W t) ∧ Integrable W ∧ P γ W ∧
      -(η * ∫ t : ℝ, W t) ≤ (∫ t : ℝ, W t * (S.indicator f (γ t) - A * f (γ t))) ∧
      0 < ∫ t : ℝ, W t * g₂ (γ t) :=
  exists_needle_of_lowerSemicontinuous_pair hKfin hK0
    (lowerSemicontinuous_indicator_sub_smul hS hf hf0 A) hM₁ hg₂ hM₂ hzero hpos hη hloc

end IndicatorNeedle

/-! ### Non-vacuity -/

section Witness

/-- Against the profile `1_s`, the needle integral along the identity needle is the set integral
over `s`. -/
theorem integral_indicator_one_mul {s : Set ℝ} (hs : MeasurableSet s) (f : ℝ → ℝ) :
    (∫ t : ℝ, s.indicator (fun _ => (1 : ℝ)) t * f t) = ∫ t in s, f t := by
  have hfun : (fun t : ℝ => s.indicator (fun _ => (1 : ℝ)) t * f t) = s.indicator f := by
    funext t
    by_cases ht : t ∈ s
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, one_mul]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul]
  rw [hfun, integral_indicator hs]

/-- **Non-vacuity of `Arlib.exists_needle_indicator_sub_smul`.**

Every hypothesis holds simultaneously, `hloc` included, on concrete data:
`K = [-1,1]`, `g₁ = sin` (continuous, `∫_K sin = 0` by oddness), `S = (-1,1)` open, `f = 1`,
`c = 1/2`, so that `g₂ = 1_{(-1,1)} − 1/2` is lower semicontinuous but **not** continuous, with
`∫_K g₂ = 1 > 0`.  The localisation binder is discharged by the trivial needle `γ = id` carrying
the profile `W = 1_{[-1,1]}`, for which both needle integrals *are* the set integrals over `K`;
and the extra property `P` is instantiated at the non-trivial `0 < ∫ W`.

So the conclusion delivered is a strictly positive lower bound on a genuinely discontinuous
integrand's needle integral, not a statement about an unsatisfiable configuration. -/
theorem exists_needle_indicator_sub_smul_witness :
    ∃ (γ : ℝ → ℝ) (W : ℝ → ℝ), Measurable γ ∧ (∀ t, 0 ≤ W t) ∧ Integrable W ∧
      (0 < ∫ t : ℝ, W t) ∧
      (∫ t : ℝ, W t * Real.sin (γ t)) = 0 ∧
      0 < ∫ t : ℝ, W t *
        ((Set.Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) (γ t) - 1 / 2 * (1 : ℝ)) := by
  set K : Set ℝ := Set.Icc (-1 : ℝ) 1 with hK
  have hKm : MeasurableSet K := measurableSet_Icc
  have hKvol : volume K = ENNReal.ofReal 2 := by
    rw [hK, Real.volume_Icc]; norm_num
  have hKfin : volume K ≠ ⊤ := by rw [hKvol]; exact ENNReal.ofReal_ne_top
  have hKreal : (volume K).toReal = 2 := by rw [hKvol]; simp
  -- the profile
  set W : ℝ → ℝ := K.indicator (fun _ => (1 : ℝ)) with hW
  have hW0 : ∀ t, 0 ≤ W t := fun t => Set.indicator_nonneg (fun _ _ => zero_le_one) t
  have hWi : Integrable W := (integrable_indicator_iff hKm).mpr (integrableOn_const hKfin)
  have hWtot : (∫ t : ℝ, W t) = 2 := by
    rw [hW, integral_indicator hKm, setIntegral_const, smul_eq_mul, mul_one, Measure.real, hKreal]
  -- the first integrand
  have hsin : (∫ x in K, Real.sin x) = 0 := by
    rw [hK, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1), integral_sin, Real.cos_neg]
    ring
  -- the second integrand
  have hIoom : MeasurableSet (Set.Ioo (-1 : ℝ) 1) := measurableSet_Ioo
  have hinter : K ∩ Set.Ioo (-1 : ℝ) 1 = Set.Ioo (-1 : ℝ) 1 :=
    Set.inter_eq_self_of_subset_right Set.Ioo_subset_Icc_self
  have hIoofin : volume (Set.Ioo (-1 : ℝ) 1) ≠ ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hind_on : IntegrableOn ((Set.Ioo (-1 : ℝ) 1).indicator fun _ => (1 : ℝ)) K :=
    ((integrable_indicator_iff hIoom).mpr
      (integrableOn_const (C := (1 : ℝ)) hIoofin)).integrableOn
  have hconst_on : IntegrableOn (fun _ : ℝ => (1 : ℝ) / 2 * (1 : ℝ)) K :=
    integrableOn_const (C := (1 : ℝ) / 2 * (1 : ℝ)) hKfin
  have hg₂ : (∫ x in K, ((Set.Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x
      - 1 / 2 * (1 : ℝ))) = 1 := by
    rw [integral_sub hind_on hconst_on, setIntegral_indicator hIoom, hinter,
      setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul, mul_one,
      Measure.real, Measure.real, Real.volume_Ioo, hKreal]
    norm_num
  refine exists_needle_indicator_sub_smul (μ := volume) (K := K)
    (P := fun _ W => 0 < ∫ t : ℝ, W t) hKfin Real.continuous_sin
    (M := 1) (fun x => Real.abs_sin_le_one x) isOpen_Ioo continuous_const
    (fun _ => zero_le_one) (c := 1 / 2) (fun x => ?_) hsin (by rw [hg₂]; norm_num) ?_
  · by_cases hx : x ∈ Set.Ioo (-1 : ℝ) 1
    · rw [Set.indicator_of_mem hx]; norm_num
    · rw [Set.indicator_of_notMem hx]; norm_num
  · intro f₁ f₂ M' hf₁ hf₂ hb₁ hb₂ h₁ h₂
    refine ⟨id, W, measurable_id, hW0, hWi, by rw [hWtot]; norm_num, ?_, ?_⟩
    · simpa [hW] using (integral_indicator_one_mul hKm f₁).trans h₁
    · simpa [hW] using lt_of_lt_of_le h₂ (le_of_eq (integral_indicator_one_mul hKm f₂).symm)

end Witness

end Arlib

/-! ### Axiom audit -/

#print axioms Arlib.tendsto_lipschitzMinorant
#print axioms Arlib.exists_continuous_le_setIntegral_pos
#print axioms Arlib.exists_continuous_setIntegral_eq_zero
#print axioms Arlib.exists_needle_of_lowerSemicontinuous
#print axioms Arlib.exists_needle_of_lowerSemicontinuous_pair
#print axioms Arlib.lowerSemicontinuous_indicator_of_isOpen
#print axioms Arlib.lowerSemicontinuous_neg_indicator_of_isClosed
#print axioms Arlib.lowerSemicontinuous_indicator_sub_smul
#print axioms Arlib.lowerSemicontinuous_smul_indicator_sub_indicator
#print axioms Arlib.exists_needle_indicator_sub_smul
#print axioms Arlib.exists_needle_smul_indicator_sub_indicator
#print axioms Arlib.exists_needle_indicator_sub_smul_pair
#print axioms Arlib.exists_needle_indicator_sub_smul_witness
