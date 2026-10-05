/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Topology.HamSandwich
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.NeedleProfile

/-!
# Assembling the Localization Lemma: the pencil cut and the rational-flat chain

The **Localization Lemma** of Kannan–Lovász–Simonovits, in the *equality-refined* form
(KLS 1995, Corollary 2.4) that Lovász–Vempala's Theorem 2.1 invokes, reads:

> if `g₁, g₂ : ℝⁿ → ℝ` are integrable with `∫ g₁ = 0` and `∫ g₂ > 0`, then there are points
> `a, b ∈ ℝⁿ` and a nonnegative *linear* `ℓ : [0,1] → ℝ` with
> `∫₀¹ ℓ(t)^{n-1} g₁(a + t(b-a)) dt = 0` and `∫₀¹ ℓ(t)^{n-1} g₂(a + t(b-a)) dt > 0`.

This file assembles the *localisation induction* for that statement and proves outright every
step of it that does not go through the limit passage.  **Nothing here is a `def`, `structure`,
`class` or named `Prop` asserting the Localization Lemma, the ham sandwich, Helly selection, or
any profile-convergence property**; the two definitions below (`Arlib.pencilFun`,
`Arlib.pencilLevel`) are explicit formulas, and every property attributed to them is proved.
The residual analytic ingredients appear only as inline `∀`-hypotheses of
`Arlib.needleIntegral_eq_zero_and_ge`, in exactly the shape
`Arlib.Convexity.NeedleProfile` states them.

## What is proved here, unconditionally

**1. The pencil bisection through a *prescribed* codimension-two flat.**

* `Arlib.continuous_pencilMass` — the mass on one side of a cut rotating about a fixed
  codimension-two flat is continuous in the angle (dominated convergence, via
  `Arlib.continuousAt_setIntegral_param`; the critical set is a hyperplane, hence Haar-null).
* `Arlib.exists_pencil_bisecting` — hence, by the *one-parameter* intermediate value theorem
  between an angle and its half-turn, **some hyperplane containing any prescribed flat
  `{⟪e₁,·⟫ = r} ∩ {⟪e₂,·⟫ = s}` bisects `∫_C g`**, for signed integrable `g`.

  This is the missing *positional* control.  `Arlib.exists_halfSpace_bisecting` prescribes the
  direction but not the position; `Arlib.exists_halfSpace_bisecting_pair_of_finrank` prescribes
  neither.  It is the "rotating pencil" route that `Arlib.Topology.HamSandwich` records as a
  cheap alternative available to a later reader — and no Borsuk–Ulam is used: with the equality
  form, only *one* integrand ever needs bisecting.

**2. The flat cut, equality form — Corollary 2.4 costs nothing over the weak form.**

* `Arlib.exists_flat_cut_zero_pos` — from `∫_C g₁ = 0` and `∫_C g₂ > 0`, a cut through any
  prescribed flat has a side `D` with `∫_D g₁ = 0` **exactly** and `∫_D g₂ > 0`.  The bisection
  of `0` gives `0` on *both* sides, so the equality is inherited for free and the choice of side
  is dictated only by `g₂` (whose two masses sum to something positive).  No weak version is
  proved and upgraded.

**3. The chain, run to infinite depth, over a prescribed sequence of flats.**

* `Arlib.exists_flat_cut_chain` — a decreasing `K = C 0 ⊇ C 1 ⊇ ⋯` of measurable (convex, if `K`
  is) bodies with `∫_{C m} g₁ = 0` and `∫_{C m} g₂ > 0` at every stage, in which `C (m+1)` is
  literally one side of a hyperplane through the `m`-th flat.
* `Arlib.notMem_interior_of_subset_halfSpace`, `Arlib.notMem_interior_of_pencil_cut` — **flat
  exhaustion**: once a flat has been cut through, it misses the interior of every later body.
* `Arlib.interior_nonempty_of_setIntegral_pos` — and every body stays full-dimensional, because
  a convex set with empty interior lies in a proper affine subspace and is therefore Haar-null,
  which the invariant `0 < ∫_{C m} g₂` forbids.

**4. Thinness, obtained combinatorially rather than metrically.**

* `Arlib.exists_mem_coords` — if `x, y, z` lie in a convex `S` and the `(i,j)`-minor of
  `y - x`, `z - x` is nonzero, then *every* coordinate pair `(r', s')` in an explicit
  `ε`-neighbourhood of the projected centroid is realised by an explicit convex combination of
  `x, y, z` inside `S`.
* `Arlib.minor_eq_of_pencil_exhaustion` — hence, if `S` lies on one side of a pencil hyperplane
  through *every rational coordinate flat* `{w i = r, w j = s}`, all such minors vanish.  A
  rational pair in the neighbourhood, pushed `ε/2` along the cut normal, lands strictly on the
  far side of the cut; the push works because `cos²θ + sin²θ = 1`, i.e. because the pencil
  functional is never zero.
* `Arlib.collinear_of_minor_eq`, `Arlib.exists_flat_cut_chain_collinear` — enumerating the
  countably many rational coordinate flats, **`⋂ m, C m` is collinear**: the limit body is a
  segment.

  This is the guidance of task #60 carried out: `Arlib.le_diam_of_sign_separated` and
  `Arlib.one_le_diam_bisection_chain` prove that no diameter decay can be had, and none is asked
  for.  The segment `⋂ m, C m` may be arbitrarily long; that is the correct behaviour.

**5. Strictness, and the two conclusions in the limit.**

* `Arlib.lt_setIntegral_of_perturbed` — running the chain on `g₂ - ε·1_K` upgrades
  `0 < ∫_{C m} g₂'` to the quantitative `ε · vol (C m) < ∫_{C m} g₂`, i.e. the *normalised*
  `g₂`-masses stay bounded below by `ε`.  This is the only perturbation needed: `g₁` keeps its
  equality for free (point 2).
* `Arlib.needleIntegral_eq_zero_and_ge` — feeding those two invariants through the limit passage
  `Arlib.tendsto_average_setIntegral_of_profile` gives **exactly Corollary 2.4's two
  conclusions**: `∫ W(t) g₁(axis t) dt = 0` and `0 < ∫ W(t) g₂(axis t) dt`.  The `g₁` sequence is
  *identically* `0`, so no limit theorem can degrade it.

## The profile is concave, and that is deliberate

`W` is delivered as a limit of normalised slice profiles.  `Arlib.concaveOn_limit_slice_profile`
makes `W^{1/(n-1)}` concave, and `Arlib.logConcaveOn_concaveNeedleDensity` shows that a concave
profile already gives a log-concave needle density — the only thing any downstream consumer of a
needle in this repository asks for.  `Arlib.exists_convex_slice_profile_not_affine` refutes the
"concave-to-affine" upgrade, and that upgrade has **zero consumers**, so it is not attempted here
and `ℓ` is delivered concave, not affine.

## Classification of every hypothesis of `Arlib.needleIntegral_eq_zero_and_ge`

*(proved)* — the chain invariants `hzero`, `hge`: supplied by `Arlib.exists_flat_cut_chain` and
`Arlib.lt_setIntegral_of_perturbed`.  Measurability, finiteness and positivity of the volumes:
`Arlib.exists_flat_cut_chain` plus `Arlib.interior_nonempty_of_setIntegral_pos`.

*(proved — (G2a), (G2b) of `Arlib.Convexity.NeedleProfile`, in
`Arlib.Convexity.ConcaveSelection`)* — `hB`, the uniform bound on the normalised slice profiles
(`Arlib.normalised_volume_slice_le`, at constant `2^(m+1)`), and `hlim`, their pointwise
convergence to `W` along a subsequence (`Arlib.exists_subseq_tendsto_normalised_slice_profile'`,
Arzelà–Ascoli on the *profiles*, not Blaschke on the *bodies*).  Both are packaged into
`Arlib.needleIntegral_eq_zero_and_ge` by `Arlib.exists_needleIntegral_eq_zero_and_pos`
(`Arlib.Convexity.LocalizationAffine`), which quantifies `W` existentially and asks instead only
that the bodies be convex, slice-finite and spanning.

*(proved — the two items formerly listed here as open, in `Arlib.Convexity.LocalizationAffine`
and `Arlib.Convexity.LocalizationTransverse`)*:

* **(A) The transverse-thinness bridge**, formerly "the precise point at which the assembly
  stops", is now `Arlib.exists_tendsto_transverse_modulus` /
  `Arlib.exists_tendsto_transverse_modulus_pair`.  Hausdorff convergence is *not* what it uses:
  `Arlib.eventually_subset_of_antitone_isCompact` shows a decreasing sequence of **compact** sets
  is eventually inside any open neighbourhood of its intersection (finite-intersection property),
  and the neighbourhood `{y | |g y − g (axis y)| < ε}` is open because `g` and the axis map are
  continuous.  The explicit moduli `δ k = sSup {|g y − g (axis y)| : y ∈ C k}` then tend to `0`.
  What it needs of the chain — that its bodies be *closed* — is supplied by
  `Arlib.exists_flat_cut_chain_collinear_compact` (`Arlib.Convexity.LocalizationClosed`), which
  closes each body of `Arlib.exists_flat_cut_chain` up: the frontier of a convex set is
  Haar-null, so no mass moves, and a half-turn of the pencil turns the closure of the open side
  of a cut into the closed side of another cut through the same flat.  Nothing about (A) is
  open.
* **(B) (G2c), the affine change of coordinates**, is now
  `Arlib.exists_needleIntegral_eq_zero_and_pos_affine`: for an arbitrary needle `t ↦ a + t • v`
  and an arbitrary height functional `φ` normalised by `φ v = 1`, the two conclusions of the
  equality form hold for bodies of the slab `{y | φ (y − a) ∈ [0,1]}`.  The frame is
  `Arlib.exists_linearEquiv_frame` (a linear automorphism carrying the first axis to `ℝ ∙ v` and
  reading the height back off as `φ`, built from a basis of `ker φ`), and the transport is
  `Arlib.map_affine_addHaar`, `Arlib.addHaar_preimage_affine`, `Arlib.setIntegral_comp_affine`.
  The Jacobian is a single positive constant and cancels from both conclusions, so the
  factorisation of the determinant into "first-coordinate scaling times transverse determinant"
  that `Arlib.Convexity.NeedleProfile` anticipated is **not** needed: the profile hypotheses are
  discharged in the frame, before the transport.
  `Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact` combines (A) and (B), and
  `Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_box` is its non-vacuity witness.
  All three deliver `W` nonnegative with `W ^ (1/m)` concave on `(0,1)`
  (`Arlib.concaveOn_limit_normalised_slice_profile`), i.e. `W = ℓ^m` for a concave `ℓ` — the
  concave form of Corollary 2.4 that §"The profile is concave, and that is deliberate" above
  argues is the right target.

* **(D) Closedness of the chain, and its positioning — closed.**
  `Arlib.exists_flat_cut_chain_collinear_compact` delivers the chain with **compact** convex
  bodies of positive volume (and `Arlib.exists_flat_cut_chain_collinear_compact_ge` with the
  quantitative `ε · vol ≤ ∫ g₂`); `Arlib.exists_axis_of_collinear` positions the collinear limit
  body along an explicit axis, so `Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear`
  states the needle conclusions with `haxis` replaced by `Collinear ℝ (⋂ k, D k)` — exactly what
  the chain produces.  `Arlib.halfSpace` is unchanged.

* **(E) The slab rigidity of `hslab`/`hspan` — closed.**
  `Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact` asks every body to lie in *and* span
  one fixed slab, which forces `φ '' (D k − a) = [0,1]` at every stage and
  (`Arlib.exists_mem_iInter_height`) in the limit; a localisation chain shrinks in *every*
  direction, so no nonzero `φ` has constant range along it.  `Arlib.Convexity.NeedleSlab`
  removes the rigidity: the `k`-th body lies in and spans its **own** slab `[l k, u k]`, with
  `l k ≤ 0 ≤ 1 ≤ u k`, `l k → 0`, `u k → 1`.  The mechanism is a rescaling of the *profile*
  rather than the body — `Arlib.rescaledProfile` puts every stage's profile on `[0,1]`, so the
  Arzelà–Ascoli selection of `Arlib.Convexity.ConcaveSelection` applies verbatim, with the
  slab-independent uniform bound supplied by `Arlib.le_two_pow_of_concaveOn_rpow` (a
  one-dimensional restatement of `Arlib.normalised_volume_slice_le` with the geometry stripped
  out).  The needle point then moves with `k`, and continuity of the integrands absorbs it in
  the same dominated-convergence step (`Arlib.tendsto_average_setIntegral_of_rescaledProfile`).
  `Arlib.Convexity.NeedleSlabAffine` carries this to general position, and
  `Arlib.exists_needleIntegral_eq_zero_and_pos_shrinking_box` is the acid test: the boxes
  `[−1/(k+1), 1+1/(k+1)] × [−1/(k+1), 1/(k+1)]^m` shrink in *every* direction including along
  the needle, which the fixed-slab form provably cannot accept.  In
  `Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_chain` the slab hypotheses are gone
  altogether: `Arlib.exists_unitHeight_functional` and `Arlib.exists_slab_of_compact_chain`
  derive them from compactness plus two distinct points in the limit.

*(closed, with a boundary)*:

* **(C) Lower semicontinuity.**  ~~The thin-tube comparison consumes a modulus-of-continuity
  hypothesis, not lower semicontinuity.~~  **Closed** in
  `Arlib/Convexity/LocalizationLSC.lean`: `Arlib.exists_needle_of_lowerSemicontinuous` runs
  with `g₂` bounded *lower semicontinuous* (`g₁` still continuous), by inf-convolution
  Lipschitz minorants (`Arlib.lipschitzMinorant`).  That is the case CV needs —
  `g₂ = (d/σ)·A·1_{S₂}h − 1_{S₃}h` is lsc for `S₂` open and `S₃` closed, stated in CV's own
  shape as `Arlib.exists_needle_smul_indicator_sub_indicator`.

  **The boundary is not an unfinished proof.**  Merely *measurable* `S₁` is unreachable by
  this route, for two independent reasons.  (1) A needle is a **null set**, so two integrands
  agreeing off a null set have arbitrarily different needle integrals, while a measurable set
  is only pinned down up to null sets — no approximation good "in measure" can control a
  needle integral.  (2) Even for `S₁` *open* the **equality** `∫ W·g₁∘γ = 0` does not
  transfer: it is monotone in neither direction, and the needle depends on the function fed
  in, so the re-centring slack cannot be driven to `0` at a fixed needle.  For `S` a fat
  Cantor set every continuous minorant of `1_S` has nonpositive integral.  Hence
  `Arlib.exists_needle_of_lowerSemicontinuous_pair` degrades the equality to
  `−η·∫W ≤ ∫ W·g₁∘γ`; the `η` is the honest price.

  Chain-level is *forced* to fail, recorded so nobody retries it: the invariant
  `ε·vol(D k) ≤ ∫_{D k} g₂` for every `k` needs uniform convergence — true for continuous
  `g₂` by Dini, false for lsc.  The result is at the `∫_K` level.

  Consumers should note that `Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_chain`
  does not state `Integrable W`, which the monotone transfer needs (a Bochner integral of a
  non-integrable nonnegative function is `0`, not `+∞`).  Its `W` *is* bounded with support
  in `[0,1]` (`Arlib.normalised_volume_slice_le`), so exposing it is routine but not done.

* **(F) Two residues of (E)'s composition**, both explicit hypotheses rather than hidden
  assumptions.  **Both are now addressed** in `Arlib/Convexity/LocalizationTransport.lean`.

  *The transport is closed outright, with no residual binder.*  `EuclideanSpace ℝ (Fin n)` is
  `WithLp 2 (Fin n → ℝ)`, and in this Mathlib `WithLp` is a **structure**, so none of it was
  definitional — each transport is proved.  `Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_chain_euclidean`
  restates the slab-free form *verbatim* over `EuclideanSpace ℝ (Fin (m+1))`.  The
  `MeasurableSet`/`IsCompact`/`Convex`/`Collinear` transfer lemmas are stated as **iffs** on
  purpose: `toLp ⁻¹' (ofLp ⁻¹' T) = T` by `rfl`, so they move hypotheses in both directions.

  ⚠ **This sentence used to name a lemma that does not exist.**  It said the transport
  "should be routine" via `EuclideanSpace.volume_preserving_measurableEquiv`.  There is no
  such declaration in this Mathlib.  The actual bridge is `PiLp.volume_preserving_toLp` /
  `PiLp.volume_preserving_ofLp` together with `MeasurableEquiv.toLp`.

  *Nondegeneracy is closed modulo exactly one explicit data hypothesis*,
  `hsep : ∀ x, g₁ x = 0 → g₂ x < ε`, in `Arlib.exists_ne_mem_iInter_of_chain`.  The cutting
  scheme is free to collapse to a point, and the only consequences a collapse has for the two
  chain invariants are `g₁ p = 0` and `ε ≤ g₂ p`; `hsep` is exactly the denial of that
  conjunction, hence the weakest hypothesis *this pointwise argument* can use — **not**
  claimed weakest outright.  `Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_chain_euclidean_of_sep`
  is the composed form downstream consumers want: both conclusions, no nondegeneracy
  hypothesis, only `hsep`.

  ⚠ **Strictness gap for anyone wiring `hsep` to slab separation.**
  `Arlib.forall_lt_of_sign_separated` derives `hsep`, but needs the `g₁` side **strict**
  (`a < L x → g₁ x < 0`).  `Arlib.le_diam_of_sign_separated` (`NeedleLimit.lean:234`) is
  stated with `≤ 0`, and the non-strict form does **not** suffice: `g₁` may vanish above the
  level, where nothing bounds `g₂`.  That is why `hsep` is stated directly.

## Provenance caveat

Task #60 could **not** read Kannan–Lovász–Simonovits 1995 verbatim — Springer's scan carries a
text layer on page 1 only, the rest being CCITT-G4 images — so the target Corollary 2.4 stated at
the top is *reconstructed* from what Lovász–Vempala's proof consumes together with the
Kook–Vempala survey (arXiv:2512.10848), not read from the source.

That survey's printed construction also reads *"if `A_m ∩ int K_m ≠ ∅`, set `K_{m+1} := K_m`"*,
which is backwards relative to its own later contradiction argument; #60 reads it as a typo for
cutting *when* the flat meets the interior.  **This file does not have to choose.**
`Arlib.exists_flat_cut_chain` cuts at **every** step, unconditionally — legitimate, because
`Arlib.exists_pencil_bisecting` has no hypothesis about the flat meeting the interior — and the
exhaustion property comes out unconditionally too.  The discrepancy is bypassed, not resolved,
and nothing below depends on either reading.
-/

open MeasureTheory Set Filter Metric Bornology Module

open scoped ENNReal Topology

namespace Arlib

/-! ### The pencil of hyperplanes through a codimension-two flat -/

section Pencil

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The pencil of hyperplanes through a codimension-two flat: the functional.**

For orthonormal `e₁, e₂` the hyperplanes containing the flat
`{x | ⟪e₁,x⟫ = r ∧ ⟪e₂,x⟫ = s}` are exactly the level sets
`{x | pencilFun e₁ e₂ θ x = pencilLevel r s θ}`, `θ ∈ ℝ`.  This is a plain explicit definition of
a linear combination of two inner products; nothing is asserted about it here. -/
noncomputable def pencilFun (e₁ e₂ : E) (θ : ℝ) : E →L[ℝ] ℝ :=
  Real.cos θ • innerSL ℝ e₁ + Real.sin θ • innerSL ℝ e₂

theorem pencilFun_apply (e₁ e₂ : E) (θ : ℝ) (x : E) :
    pencilFun e₁ e₂ θ x = Real.cos θ * inner ℝ e₁ x + Real.sin θ * inner ℝ e₂ x := rfl

/-- **The pencil of hyperplanes through a codimension-two flat: the level.**  Explicit. -/
noncomputable def pencilLevel (r s θ : ℝ) : ℝ := Real.cos θ * r + Real.sin θ * s

/-- Every hyperplane of the pencil contains the flat `{⟪e₁,·⟫ = r} ∩ {⟪e₂,·⟫ = s}`. -/
theorem pencilFun_eq_pencilLevel {e₁ e₂ : E} {r s : ℝ} {x : E}
    (h1 : inner ℝ e₁ x = r) (h2 : inner ℝ e₂ x = s) (θ : ℝ) :
    pencilFun e₁ e₂ θ x = pencilLevel r s θ := by
  rw [pencilFun_apply, pencilLevel, h1, h2]

/-- A half-turn of the pencil negates the functional. -/
theorem pencilFun_add_pi (e₁ e₂ : E) (θ : ℝ) :
    pencilFun e₁ e₂ (θ + Real.pi) = -pencilFun e₁ e₂ θ := by
  ext x
  simp only [pencilFun_apply, neg_apply, Real.cos_add, Real.sin_add,
    Real.cos_pi, Real.sin_pi]
  ring

/-- A half-turn of the pencil negates the level. -/
theorem pencilLevel_add_pi (r s θ : ℝ) :
    pencilLevel r s (θ + Real.pi) = -pencilLevel r s θ := by
  simp only [pencilLevel, Real.cos_add, Real.sin_add, Real.cos_pi, Real.sin_pi]
  ring

/-- Every functional of the pencil is nonzero: it takes the value `1` at
`cos θ • e₁ + sin θ • e₂`. -/
theorem pencilFun_ne_zero {e₁ e₂ : E} (h11 : inner ℝ e₁ e₁ = (1 : ℝ))
    (h22 : inner ℝ e₂ e₂ = (1 : ℝ)) (h12 : inner ℝ e₁ e₂ = (0 : ℝ)) (θ : ℝ) :
    pencilFun e₁ e₂ θ ≠ 0 := by
  have h21 : inner ℝ e₂ e₁ = (0 : ℝ) := by rw [real_inner_comm]; exact h12
  intro hzero
  have hv : pencilFun e₁ e₂ θ (Real.cos θ • e₁ + Real.sin θ • e₂) = 1 := by
    rw [pencilFun_apply, inner_add_right, inner_add_right, real_inner_smul_right,
      real_inner_smul_right, real_inner_smul_right, real_inner_smul_right, h11, h22, h12, h21]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [hzero] at hv
  simp at hv

end Pencil

/-! ### The cut mass along the pencil is continuous -/

section PencilMass

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **The mass on one side of a rotating pencil cut is continuous in the angle.**

Dominated convergence (`Arlib.continuousAt_setIntegral_param`); the critical set is a hyperplane,
null because every functional of the pencil is nonzero. -/
theorem continuous_pencilMass {e₁ e₂ : E} (h11 : inner ℝ e₁ e₁ = (1 : ℝ))
    (h22 : inner ℝ e₂ e₂ = (1 : ℝ)) (h12 : inner ℝ e₁ e₂ = (0 : ℝ))
    {C : Set E} {g : E → ℝ} (hgi : IntegrableOn g C μ) (r s : ℝ) :
    Continuous fun θ : ℝ =>
      ∫ x in C ∩ halfSpace (pencilFun e₁ e₂ θ) (pencilLevel r s θ) true, g x ∂μ := by
  set φ : ℝ → E → ℝ := fun θ x => pencilFun e₁ e₂ θ x - pencilLevel r s θ with hφ
  have hset : ∀ θ : ℝ, {x : E | φ θ x ≤ 0}
      = halfSpace (pencilFun e₁ e₂ θ) (pencilLevel r s θ) true := by
    intro θ; ext x
    simp only [hφ, halfSpace_true, mem_setOf_eq]
    constructor <;> intro h <;> linarith
  have hcont : ∀ x : E, Continuous fun θ : ℝ => φ θ x := by
    intro x
    simp only [hφ, pencilFun_apply, pencilLevel]
    exact ((Real.continuous_cos.mul continuous_const).add
      (Real.continuous_sin.mul continuous_const)).sub
      ((Real.continuous_cos.mul continuous_const).add (Real.continuous_sin.mul continuous_const))
  have hmeas : ∀ θ : ℝ, MeasurableSet {x : E | φ θ x ≤ 0} := by
    intro θ; rw [hset θ]; exact measurableSet_halfSpace _ _ _
  rw [continuous_iff_continuousAt]
  intro θ₀
  have hnull : (μ.restrict C) {x : E | φ θ₀ x = 0} = 0 := by
    have hset0 : {x : E | φ θ₀ x = 0}
        = {x : E | pencilFun e₁ e₂ θ₀ x = pencilLevel r s θ₀} := by
      ext x
      simp only [hφ, mem_setOf_eq]
      constructor <;> intro h <;> linarith
    have hμ : μ {x : E | pencilFun e₁ e₂ θ₀ x = pencilLevel r s θ₀} = 0 :=
      measure_hyperplane_eq_zero μ (pencilFun_ne_zero h11 h22 h12 θ₀) _
    rw [hset0]
    exact le_antisymm (le_trans (Measure.restrict_apply_le _ _) hμ.le) zero_le
  have h := continuousAt_setIntegral_param (μ := μ) hgi hcont hmeas hnull
  simpa only [hset] using h

/-- **The pencil bisection, through a prescribed codimension-two flat.**

For orthonormal `e₁, e₂`, a measurable `C` and an integrable — possibly sign-changing — `g`,
*some hyperplane containing the flat* `{x | ⟪e₁,x⟫ = r ∧ ⟪e₂,x⟫ = s}` splits `∫_C g` into two
equal halves.

This is the **positional** bisection that `Arlib.exists_halfSpace_bisecting` (which fixes the
direction, not the position) and `Arlib.exists_halfSpace_bisecting_pair_of_finrank` (which
prescribes neither) do not give.  It is the "rotating pencil" route recorded as an alternative in
`Arlib.Topology.HamSandwich`: only the *one-parameter* intermediate value theorem is used, no
Borsuk–Ulam.  A single integrand is bisected — which is all the equality form of the Localization
Lemma needs. -/
theorem exists_pencil_bisecting {e₁ e₂ : E} (h11 : inner ℝ e₁ e₁ = (1 : ℝ))
    (h22 : inner ℝ e₂ e₂ = (1 : ℝ)) (h12 : inner ℝ e₁ e₂ = (0 : ℝ))
    {C : Set E} {g : E → ℝ} (hC : MeasurableSet C) (hgi : IntegrableOn g C μ) (r s : ℝ) :
    ∃ θ : ℝ, ∫ x in C ∩ halfSpace (pencilFun e₁ e₂ θ) (pencilLevel r s θ) true, g x ∂μ
      = (∫ x in C, g x ∂μ) / 2 := by
  set F : ℝ → ℝ := fun θ =>
    ∫ x in C ∩ halfSpace (pencilFun e₁ e₂ θ) (pencilLevel r s θ) true, g x ∂μ with hF
  have hFcont : Continuous F := continuous_pencilMass h11 h22 h12 hgi r s
  have hsum : F 0 + F Real.pi = ∫ x in C, g x ∂μ := by
    have hzero : (0 : ℝ) + Real.pi = Real.pi := zero_add _
    have h1 : F Real.pi = ∫ x in C ∩ halfSpace (-pencilFun e₁ e₂ 0) (-pencilLevel r s 0) true,
        g x ∂μ := by
      rw [hF]
      simp only
      rw [← hzero, pencilFun_add_pi, pencilLevel_add_pi]
    rw [h1]
    exact setIntegral_halfSpace_add_neg hC hgi
      (Or.inl (pencilFun_ne_zero h11 h22 h12 0))
  set I : ℝ := ∫ x in C, g x ∂μ with hI
  have hpi : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have hIVT : I / 2 ∈ F '' Icc (0 : ℝ) Real.pi := by
    rcases le_total (F 0) (F Real.pi) with hle | hle
    · exact intermediate_value_Icc hpi hFcont.continuousOn ⟨by linarith, by linarith⟩
    · exact intermediate_value_Icc' hpi hFcont.continuousOn ⟨by linarith, by linarith⟩
  obtain ⟨θ, -, hθ⟩ := hIVT
  exact ⟨θ, hθ⟩

/-- **The flat cut, equality form.**

If `∫_C g₁ = 0` and `∫_C g₂ > 0` then, through *any* prescribed codimension-two flat
`{⟪e₁,·⟫ = r} ∩ {⟪e₂,·⟫ = s}`, there is a hyperplane one of whose sides `D` satisfies
`∫_D g₁ = 0` **exactly** and `∫_D g₂ > 0`.

The equality is free: the pencil bisects `∫_C g₁ = 0` into `0` and `0`, so *both* sides inherit
it, and the choice of side is then dictated only by `g₂`, whose two masses sum to
`∫_C g₂ > 0`.  This is why Corollary 2.4 of KLS 1995 (the equality-refined form) costs nothing
over the weak form. -/
theorem exists_flat_cut_zero_pos {e₁ e₂ : E} (h11 : inner ℝ e₁ e₁ = (1 : ℝ))
    (h22 : inner ℝ e₂ e₂ = (1 : ℝ)) (h12 : inner ℝ e₁ e₂ = (0 : ℝ))
    {C : Set E} {g₁ g₂ : E → ℝ} (hC : MeasurableSet C)
    (hg₁ : IntegrableOn g₁ C μ) (hg₂ : IntegrableOn g₂ C μ)
    (hz : ∫ x in C, g₁ x ∂μ = 0) (hp : 0 < ∫ x in C, g₂ x ∂μ) (r s : ℝ) :
    ∃ (θ : ℝ) (side : Bool),
      (∫ x in C ∩ halfSpace (pencilFun e₁ e₂ θ) (pencilLevel r s θ) side, g₁ x ∂μ) = 0 ∧
      0 < ∫ x in C ∩ halfSpace (pencilFun e₁ e₂ θ) (pencilLevel r s θ) side, g₂ x ∂μ := by
  obtain ⟨θ, hθ⟩ := exists_pencil_bisecting h11 h22 h12 hC hg₁ r s
  rw [hz, zero_div] at hθ
  have hsum₁ := setIntegral_halfSpace_add hg₁ hC (pencilFun e₁ e₂ θ) (pencilLevel r s θ)
  have hsum₂ := setIntegral_halfSpace_add hg₂ hC (pencilFun e₁ e₂ θ) (pencilLevel r s θ)
  have hfalse₁ : (∫ x in C ∩ halfSpace (pencilFun e₁ e₂ θ) (pencilLevel r s θ) false, g₁ x ∂μ)
      = 0 := by rw [hz] at hsum₁; linarith
  rcases lt_or_ge 0
      (∫ x in C ∩ halfSpace (pencilFun e₁ e₂ θ) (pencilLevel r s θ) true, g₂ x ∂μ) with hg | hg
  · exact ⟨θ, true, hθ, hg⟩
  · exact ⟨θ, false, hfalse₁, by linarith⟩

end PencilMass

/-! ### A cut removes its flat from the interior, permanently -/

section FlatExhaustion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A point on the boundary hyperplane is not interior to either side.**

For `L ≠ 0` and `L x = c`, `x ∉ interior (halfSpace L c side)` for both sides: the open side does
not contain `x` at all, and the closed side `{L ≤ c}` has interior inside `{L < c}` because `L` is
a nonzero — hence open — map. -/
theorem notMem_interior_halfSpace {L : E →L[ℝ] ℝ} (hL : L ≠ 0) {c : ℝ} {x : E} (hx : L x = c)
    (side : Bool) : x ∉ interior (halfSpace L c side) := by
  obtain ⟨y, hy⟩ : ∃ y : E, 0 < L y := by
    have hex : ∃ z : E, L z ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hL (by ext z; simp [hcon z])
    obtain ⟨z, hz⟩ := hex
    rcases lt_or_gt_of_ne hz with hlt | hgt
    · exact ⟨-z, by rw [map_neg]; linarith⟩
    · exact ⟨z, hgt⟩
  have hy0 : ‖y‖ ≠ 0 := by
    intro h
    rw [norm_eq_zero] at h
    rw [h, map_zero] at hy
    exact lt_irrefl 0 hy
  cases side
  · intro hmem
    have hxx : x ∈ halfSpace L c false := interior_subset hmem
    rw [halfSpace_false, mem_setOf_eq] at hxx
    exact absurd hx (ne_of_gt hxx)
  · intro hmem
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hmem
    obtain ⟨ε, hε, hball⟩ := hmem
    have hnorm : (0 : ℝ) < ‖y‖ := lt_of_le_of_ne (norm_nonneg y) (Ne.symm hy0)
    set t : ℝ := ε / (2 * ‖y‖) with ht
    have htpos : 0 < t := by positivity
    have hmemball : x + t • y ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      have : ‖x + t • y - x‖ = t * ‖y‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      rw [this, ht]
      field_simp
      linarith
    have hin := hball hmemball
    rw [halfSpace_true, mem_setOf_eq, map_add, map_smul, smul_eq_mul] at hin
    nlinarith

/-- **A cut removes its flat from the interior of the successor, hence of every later body.**

If `D` is contained in one of the two sides of a hyperplane containing the point `x`, then `x` is
not in the interior of `D`.  Applied along a chain this says: once a flat has been cut through, no
later body of the chain has that flat meeting its interior. -/
theorem notMem_interior_of_subset_halfSpace {L : E →L[ℝ] ℝ} (hL : L ≠ 0) {c : ℝ} {D : Set E}
    {side : Bool} (hD : D ⊆ halfSpace L c side) {x : E} (hx : L x = c) : x ∉ interior D :=
  fun hmem => notMem_interior_halfSpace hL hx side (interior_mono hD hmem)

end FlatExhaustion

/-! ### The rational-flat chain -/

section Chain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **The localisation chain driven by a prescribed sequence of flats, equality form.**

Given a sequence of codimension-two flats `A m = {⟪d₁ m,·⟫ = a m} ∩ {⟪d₂ m,·⟫ = b m}` (each pair
`d₁ m, d₂ m` orthonormal) and a starting body `K` with `∫_K g₁ = 0` and `∫_K g₂ > 0`, there is a
decreasing chain `K = C 0 ⊇ C 1 ⊇ ⋯` of measurable (convex, if `K` is) bodies with

* `∫_{C m} g₁ = 0` **exactly**, and `∫_{C m} g₂ > 0`, at every stage — the equality form is
  maintained for free, because a bisection of `0` gives `0` on both sides;
* **flat exhaustion**: `A m` misses `interior (C (m+1))`, hence (the chain being decreasing)
  misses the interior of every later body.

Note that the cut is taken **unconditionally** at every step, whether or not `A m` meets
`interior (C m)`.  The Kook–Vempala survey (arXiv:2512.10848) prints the construction with the
guard "if `A_m ∩ int K_m ≠ ∅`, set `K_{m+1} := K_m`", which reads backwards relative to its own
later contradiction argument — task #60 reads it as a typo for cutting *when* the flat meets the
interior.  This file does not have to choose: cutting always is legitimate (the pencil bisection
of `Arlib.exists_pencil_bisecting` has no such hypothesis) and yields the exhaustion property
unconditionally, so the discrepancy is bypassed rather than resolved. -/
theorem exists_flat_cut_chain {d₁ d₂ : ℕ → E} (h11 : ∀ m, inner ℝ (d₁ m) (d₁ m) = (1 : ℝ))
    (h22 : ∀ m, inner ℝ (d₂ m) (d₂ m) = (1 : ℝ)) (h12 : ∀ m, inner ℝ (d₁ m) (d₂ m) = (0 : ℝ))
    (a b : ℕ → ℝ) {K : Set E} (hK : MeasurableSet K) {g₁ g₂ : E → ℝ}
    (hg₁ : Integrable g₁ μ) (hg₂ : Integrable g₂ μ)
    (hz : ∫ x in K, g₁ x ∂μ = 0) (hp : 0 < ∫ x in K, g₂ x ∂μ) :
    ∃ C : ℕ → Set E, C 0 = K ∧ (∀ m, C (m + 1) ⊆ C m) ∧
      (∀ m, MeasurableSet (C m) ∧ C m ⊆ K ∧ (Convex ℝ K → Convex ℝ (C m)) ∧
        (∫ x in C m, g₁ x ∂μ) = 0 ∧ 0 < ∫ x in C m, g₂ x ∂μ) ∧
      (∀ m, ∃ (θ : ℝ) (side : Bool),
        C (m + 1) ⊆ halfSpace (pencilFun (d₁ m) (d₂ m) θ) (pencilLevel (a m) (b m) θ) side) := by
  classical
  have hstep : ∀ (m : ℕ) (C : Set E), ∃ D : Set E,
      MeasurableSet C → C ⊆ K → (Convex ℝ K → Convex ℝ C) → (∫ x in C, g₁ x ∂μ) = 0 →
      0 < (∫ x in C, g₂ x ∂μ) →
      (D ⊆ C ∧ MeasurableSet D ∧ D ⊆ K ∧ (Convex ℝ K → Convex ℝ D) ∧
        (∫ x in D, g₁ x ∂μ) = 0 ∧ 0 < (∫ x in D, g₂ x ∂μ) ∧
        ∃ (θ : ℝ) (side : Bool),
          D ⊆ halfSpace (pencilFun (d₁ m) (d₂ m) θ) (pencilLevel (a m) (b m) θ) side) := by
    intro m C
    by_cases hyp : MeasurableSet C ∧ C ⊆ K ∧ (Convex ℝ K → Convex ℝ C) ∧
        (∫ x in C, g₁ x ∂μ) = 0 ∧ 0 < (∫ x in C, g₂ x ∂μ)
    · obtain ⟨hCm, hCK, hCc, hC1, hC2⟩ := hyp
      obtain ⟨θ, side, hD1, hD2⟩ := exists_flat_cut_zero_pos (h11 m) (h22 m) (h12 m) hCm
        hg₁.integrableOn hg₂.integrableOn hC1 hC2 (a m) (b m)
      set L : E →L[ℝ] ℝ := pencilFun (d₁ m) (d₂ m) θ with hL
      set c : ℝ := pencilLevel (a m) (b m) θ with hc
      exact ⟨C ∩ halfSpace L c side, fun _ _ _ _ _ =>
        ⟨inter_subset_left, hCm.inter (measurableSet_halfSpace _ _ _),
          inter_subset_left.trans hCK, fun hcv => (hCc hcv).inter (convex_halfSpace _ _ _),
          hD1, hD2, ⟨θ, side, inter_subset_right⟩⟩⟩
    · exact ⟨C, fun p1 p2 p3 p4 p5 => absurd ⟨p1, p2, p3, p4, p5⟩ hyp⟩
  choose F hF using hstep
  have hinv : ∀ m : ℕ,
      MeasurableSet (Nat.rec K (fun j c => F j c) m : Set E) ∧
      (Nat.rec K (fun j c => F j c) m : Set E) ⊆ K ∧
      (Convex ℝ K → Convex ℝ (Nat.rec K (fun j c => F j c) m : Set E)) ∧
      (∫ x in (Nat.rec K (fun j c => F j c) m : Set E), g₁ x ∂μ) = 0 ∧
      0 < ∫ x in (Nat.rec K (fun j c => F j c) m : Set E), g₂ x ∂μ := by
    intro m
    induction m with
    | zero => exact ⟨hK, Subset.rfl, fun hc => hc, hz, hp⟩
    | succ j ih =>
      obtain ⟨p1, p2, p3, p4, p5⟩ := ih
      obtain ⟨-, q2, q3, q4, q5, q6, -⟩ := hF j _ p1 p2 p3 p4 p5
      exact ⟨q2, q3, q4, q5, q6⟩
  refine ⟨fun m => Nat.rec K (fun j c => F j c) m, rfl, ?_, hinv, ?_⟩
  · intro m
    obtain ⟨h1, h2, h3, h4, h5⟩ := hinv m
    exact (hF m _ h1 h2 h3 h4 h5).1
  · intro m
    obtain ⟨h1, h2, h3, h4, h5⟩ := hinv m
    exact (hF m _ h1 h2 h3 h4 h5).2.2.2.2.2.2


omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- The chain's flat-exhaustion property, in the "the flat misses the interior" form. -/
theorem notMem_interior_of_pencil_cut {d₁ d₂ : E} (h11 : inner ℝ d₁ d₁ = (1 : ℝ))
    (h22 : inner ℝ d₂ d₂ = (1 : ℝ)) (h12 : inner ℝ d₁ d₂ = (0 : ℝ)) {D : Set E} {θ r s : ℝ}
    {side : Bool} (hD : D ⊆ halfSpace (pencilFun d₁ d₂ θ) (pencilLevel r s θ) side)
    {x : E} (hx1 : inner ℝ d₁ x = r) (hx2 : inner ℝ d₂ x = s) : x ∉ interior D :=
  notMem_interior_of_subset_halfSpace (pencilFun_ne_zero h11 h22 h12 θ) hD
    (pencilFun_eq_pencilLevel hx1 hx2 θ)

/-- **A convex body carrying positive mass has nonempty interior.**

If `interior C` were empty then, `C` being convex, `affineSpan ℝ C` would be a proper affine
subspace, hence Haar-null, hence `∫_C f = 0` for every `f`.  This is what keeps every body of the
localisation chain full-dimensional: the invariant `0 < ∫_{C m} g₂` is doing the work. -/
theorem interior_nonempty_of_setIntegral_pos {C : Set E} (hCconv : Convex ℝ C) {f : E → ℝ}
    (hf : 0 < ∫ x in C, f x ∂μ) : (interior C).Nonempty := by
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  have hspan : affineSpan ℝ C ≠ ⊤ := by
    intro htop
    have hne := (Convex.interior_nonempty_iff_affineSpan_eq_top hCconv).mpr htop
    rw [hemp] at hne
    exact absurd hne (by simp)
  have hnull : μ C = 0 :=
    measure_mono_null (subset_affineSpan ℝ C) (Measure.addHaar_affineSubspace μ _ hspan)
  rw [Measure.restrict_eq_zero.mpr hnull, integral_zero_measure] at hf
  exact lt_irrefl 0 hf

end Chain

/-! ### Coordinate flats and combinatorial thinness -/

section Coordinates

variable {n : ℕ}

/-- A three-point convex combination stays in a convex set. -/
theorem convex_three_mem {V : Type*} [AddCommGroup V] [Module ℝ V] {S : Set V}
    (hS : Convex ℝ S) {x y z : V} (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) {p q r : ℝ}
    (hp : 0 ≤ p) (hq : 0 < q) (hr : 0 < r) (hsum : p + q + r = 1) :
    p • x + (q • y + r • z) ∈ S := by
  have ht : 0 < q + r := by linarith
  have hne : q + r ≠ 0 := ne_of_gt ht
  have hw : (q / (q + r)) • y + (r / (q + r)) • z ∈ S :=
    hS hy hz (by positivity) (by positivity) (by field_simp)
  have hmem := hS hx hw hp ht.le (by linarith)
  have h1 : (q + r) * (q / (q + r)) = q := by field_simp
  have h2 : (q + r) * (r / (q + r)) = r := by field_simp
  rwa [smul_add, smul_smul, smul_smul, h1, h2] at hmem

/-- The explicit solution of the `2 × 2` system with matrix `[[ui, vi], [uj, vj]]`. -/
theorem pencil_solve {ui uj vi vj dr ds : ℝ} (hD : ui * vj - uj * vi ≠ 0) :
    ((dr * vj - ds * vi) / (ui * vj - uj * vi)) * ui
        + ((ds * ui - dr * uj) / (ui * vj - uj * vi)) * vi = dr ∧
      ((dr * vj - ds * vi) / (ui * vj - uj * vi)) * uj
        + ((ds * ui - dr * uj) / (ui * vj - uj * vi)) * vj = ds := by
  have hnum1 : (dr * vj - ds * vi) * ui + (ds * ui - dr * uj) * vi
      = dr * (ui * vj - uj * vi) := by ring
  have hnum2 : (dr * vj - ds * vi) * uj + (ds * ui - dr * uj) * vj
      = ds * (ui * vj - uj * vi) := by ring
  refine ⟨?_, ?_⟩
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, hnum1, mul_div_assoc,
      div_self hD, mul_one]
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, hnum2, mul_div_assoc,
      div_self hD, mul_one]

/-- The `i`-th coordinate functional of `EuclideanSpace ℝ (Fin n)` is the inner product with
`EuclideanSpace.single i 1`. -/
theorem inner_single_one (i : Fin n) (w : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (EuclideanSpace.single i (1 : ℝ)) w = w i := by
  rw [EuclideanSpace.inner_single_left]
  simp

/-- `EuclideanSpace.single i 1` is a unit vector. -/
theorem inner_single_one_self (i : Fin n) :
    inner ℝ (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ)) = (1 : ℝ) := by
  rw [inner_single_one]
  simp

/-- Distinct coordinate unit vectors are orthogonal. -/
theorem inner_single_one_ne {i j : Fin n} (hij : i ≠ j) :
    inner ℝ (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) = (0 : ℝ) := by
  rw [inner_single_one]
  simp [hij]

/-- The pencil functional attached to two coordinate directions reads off two coordinates. -/
theorem pencilFun_single_apply (i j : Fin n) (θ : ℝ) (w : EuclideanSpace ℝ (Fin n)) :
    pencilFun (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) θ w
      = Real.cos θ * w i + Real.sin θ * w j := by
  rw [pencilFun_apply, inner_single_one, inner_single_one]

/-- **A nondegenerate minor makes a whole neighbourhood of coordinate pairs attainable.**

If `x, y, z` lie in a convex set `S` and the `(i,j)`-minor of `y - x`, `z - x` does not vanish,
then every pair `(r', s')` within an explicit `ε` of the projected centroid is realised as
`(w i, w j)` for some `w ∈ S` — by an explicit convex combination of `x, y, z`.  This is the
step that makes the *rational* flats enough. -/
theorem exists_mem_coords {S : Set (EuclideanSpace ℝ (Fin n))} (hS : Convex ℝ S)
    {x y z : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) {i j : Fin n}
    (hD : (y i - x i) * (z j - x j) - (y j - x j) * (z i - x i) ≠ 0) :
    ∃ ε > 0, ∀ r' s' : ℝ,
      |r' - (x i + (y i - x i) / 3 + (z i - x i) / 3)| ≤ ε →
      |s' - (x j + (y j - x j) / 3 + (z j - x j) / 3)| ≤ ε →
      ∃ w ∈ S, w i = r' ∧ w j = s' := by
  set ui : ℝ := y i - x i with hui
  set uj : ℝ := y j - x j with huj
  set vi : ℝ := z i - x i with hvi
  set vj : ℝ := z j - x j with hvj
  have hDabs : 0 < |ui * vj - uj * vi| := abs_pos.mpr hD
  set M : ℝ := 1 + |ui| + |uj| + |vi| + |vj| with hMdef
  have hMpos : 0 < M := by
    have h1 := abs_nonneg ui; have h2 := abs_nonneg uj
    have h3 := abs_nonneg vi; have h4 := abs_nonneg vj
    rw [hMdef]; linarith
  have hM0 : M ≠ 0 := ne_of_gt hMpos
  refine ⟨|ui * vj - uj * vi| / (6 * M), div_pos hDabs (by linarith), ?_⟩
  intro r' s' hr hs
  set ε : ℝ := |ui * vj - uj * vi| / (6 * M) with hεdef
  have hεpos : 0 < ε := div_pos hDabs (by linarith)
  have hεM : ε * M = |ui * vj - uj * vi| / 6 := by
    rw [hεdef]; field_simp
  set dr : ℝ := r' - (x i + ui / 3 + vi / 3) with hdr
  set ds : ℝ := s' - (x j + uj / 3 + vj / 3) with hds
  have hdrb : |dr| ≤ ε := hr
  have hdsb : |ds| ≤ ε := hs
  have hbd : ∀ p q c₁ c₂ : ℝ, |p| ≤ ε → |q| ≤ ε → |c₁| + |c₂| ≤ M →
      |(p * c₁ - q * c₂) / (ui * vj - uj * vi)| ≤ 1 / 6 := by
    intro p q c₁ c₂ hp hq hc
    have htri : |p * c₁ - q * c₂| ≤ |p * c₁| + |q * c₂| := by
      have h := abs_add_le (p * c₁) (-(q * c₂))
      simpa [abs_neg, sub_eq_add_neg] using h
    rw [abs_mul, abs_mul] at htri
    have hc1 : |p| * |c₁| ≤ ε * |c₁| := mul_le_mul_of_nonneg_right hp (abs_nonneg c₁)
    have hc2 : |q| * |c₂| ≤ ε * |c₂| := mul_le_mul_of_nonneg_right hq (abs_nonneg c₂)
    have hsum : ε * |c₁| + ε * |c₂| ≤ ε * M := by nlinarith [hεpos.le]
    rw [abs_div, div_le_iff₀ hDabs]
    linarith
  have hαb : |(dr * vj - ds * vi) / (ui * vj - uj * vi)| ≤ 1 / 6 := by
    refine hbd dr ds vj vi hdrb hdsb ?_
    have h1 := abs_nonneg ui; have h2 := abs_nonneg uj
    rw [hMdef]; linarith
  have hβb : |(ds * ui - dr * uj) / (ui * vj - uj * vi)| ≤ 1 / 6 := by
    refine hbd ds dr ui uj hdsb hdrb ?_
    have h1 := abs_nonneg vi; have h2 := abs_nonneg vj
    rw [hMdef]; linarith
  set α : ℝ := 1 / 3 + (dr * vj - ds * vi) / (ui * vj - uj * vi) with hα
  set β : ℝ := 1 / 3 + (ds * ui - dr * uj) / (ui * vj - uj * vi) with hβ
  have hα0 : 1 / 6 ≤ α := by rw [hα]; linarith [(abs_le.mp hαb).1]
  have hα1 : α ≤ 1 / 2 := by rw [hα]; linarith [(abs_le.mp hαb).2]
  have hβ0 : 1 / 6 ≤ β := by rw [hβ]; linarith [(abs_le.mp hβb).1]
  have hβ1 : β ≤ 1 / 2 := by rw [hβ]; linarith [(abs_le.mp hβb).2]
  have hmem : (1 - α - β) • x + (α • y + β • z) ∈ S :=
    convex_three_mem hS hx hy hz (by linarith) (by linarith) (by linarith) (by ring)
  obtain ⟨hsolve1, hsolve2⟩ := pencil_solve (ui := ui) (uj := uj) (vi := vi) (vj := vj)
    (dr := dr) (ds := ds) hD
  refine ⟨(1 - α - β) • x + (α • y + β • z), hmem, ?_, ?_⟩
  · have hco : ((1 - α - β) • x + (α • y + β • z) : EuclideanSpace ℝ (Fin n)) i
        = (1 - α - β) * x i + (α * y i + β * z i) := rfl
    have hyi : y i = x i + ui := by rw [hui]; ring
    have hzi : z i = x i + vi := by rw [hvi]; ring
    have hr' : r' = x i + ui / 3 + vi / 3 + dr := by rw [hdr]; ring
    rw [hco, hyi, hzi, hr', hα, hβ]
    linear_combination hsolve1
  · have hco : ((1 - α - β) • x + (α • y + β • z) : EuclideanSpace ℝ (Fin n)) j
        = (1 - α - β) * x j + (α * y j + β * z j) := rfl
    have hyj : y j = x j + uj := by rw [huj]; ring
    have hzj : z j = x j + vj := by rw [hvj]; ring
    have hs' : s' = x j + uj / 3 + vj / 3 + ds := by rw [hds]; ring
    rw [hco, hyj, hzj, hs', hα, hβ]
    linear_combination hsolve2

/-- **Combinatorial thinness — the geometric payoff of the rational-flat enumeration.**

Let `S` be convex and suppose that for every pair of distinct coordinates `i ≠ j` and every pair
of *rationals* `(r, s)` the set `S` lies on one side of some hyperplane of the pencil through the
flat `{w | w i = r ∧ w j = s}`.  Then every `2 × 2` minor of every pair of difference vectors of
points of `S` vanishes — that is, `S` has affine dimension at most one.

**This is thinness obtained combinatorially, not metrically.**  No diameter decays, and by
`Arlib.le_diam_of_sign_separated` none can; but the family of rational coordinate flats is
countable and each one, once cut through, is permanently excluded, while a set of affine
dimension `≥ 2` still has a rational flat cutting *through* it.  The proof is exactly that: from
three points with a nonvanishing minor, `Arlib.exists_mem_coords` realises a whole
`ε`-neighbourhood of coordinate pairs inside `S`; a rational pair in that neighbourhood, pushed
`ε/2` along the cut normal, then produces a point of `S` strictly on the far side of the cut. -/
theorem minor_eq_of_pencil_exhaustion {S : Set (EuclideanSpace ℝ (Fin n))} (hS : Convex ℝ S)
    (hex : ∀ i j : Fin n, i ≠ j → ∀ r s : ℚ, ∃ (θ : ℝ) (side : Bool),
      S ⊆ halfSpace (pencilFun (EuclideanSpace.single i (1 : ℝ))
        (EuclideanSpace.single j (1 : ℝ)) θ) (pencilLevel (r : ℝ) (s : ℝ) θ) side)
    {x y z : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) (i j : Fin n) :
    (y i - x i) * (z j - x j) = (y j - x j) * (z i - x i) := by
  rcases eq_or_ne i j with rfl | hij
  · ring
  by_contra hne
  obtain ⟨ε, hεpos, hsolve⟩ := exists_mem_coords hS hx hy hz (sub_ne_zero.mpr hne)
  set r₀ : ℝ := x i + (y i - x i) / 3 + (z i - x i) / 3 with hr₀
  set s₀ : ℝ := x j + (y j - x j) / 3 + (z j - x j) / 3 with hs₀
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show r₀ - ε / 2 < r₀ + ε / 2 by linarith)
  obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn (show s₀ - ε / 2 < s₀ + ε / 2 by linarith)
  obtain ⟨θ, side, hsub⟩ := hex i j hij r s
  have hrhalf : |(r : ℝ) - r₀| ≤ ε / 2 := by rw [abs_le]; constructor <;> linarith
  have hshalf : |(s : ℝ) - s₀| ≤ ε / 2 := by rw [abs_le]; constructor <;> linarith
  obtain ⟨w₀, hw₀S, hw₀i, hw₀j⟩ := hsolve (r : ℝ) (s : ℝ) (by linarith [hrhalf])
    (by linarith [hshalf])
  have hcos : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
  have hsin : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
  have hshift : ∀ c u : ℝ, |c| ≤ 1 → |u| ≤ ε / 2 → |u + ε / 2 * c| ≤ ε := by
    intro c u hc hu
    have h2 : |ε / 2 * c| ≤ ε / 2 := by
      rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < ε / 2)]
      nlinarith [abs_nonneg c]
    calc |u + ε / 2 * c| ≤ |u| + |ε / 2 * c| := abs_add_le _ _
      _ ≤ ε := by linarith
  have hrshift : |((r : ℝ) + ε / 2 * Real.cos θ) - r₀| ≤ ε := by
    have h : ((r : ℝ) + ε / 2 * Real.cos θ) - r₀ = ((r : ℝ) - r₀) + ε / 2 * Real.cos θ := by ring
    rw [h]
    exact hshift _ _ hcos hrhalf
  have hsshift : |((s : ℝ) + ε / 2 * Real.sin θ) - s₀| ≤ ε := by
    have h : ((s : ℝ) + ε / 2 * Real.sin θ) - s₀ = ((s : ℝ) - s₀) + ε / 2 * Real.sin θ := by ring
    rw [h]
    exact hshift _ _ hsin hshalf
  obtain ⟨w₁, hw₁S, hw₁i, hw₁j⟩ := hsolve _ _ hrshift hsshift
  have hpy := Real.sin_sq_add_cos_sq θ
  have hL₀ : pencilFun (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) θ w₀
      = pencilLevel (r : ℝ) (s : ℝ) θ := by
    rw [pencilFun_single_apply, hw₀i, hw₀j, pencilLevel]
  have hL₁ : pencilFun (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) θ w₁
      = pencilLevel (r : ℝ) (s : ℝ) θ + ε / 2 := by
    rw [pencilFun_single_apply, hw₁i, hw₁j, pencilLevel]
    linear_combination (ε / 2) * hpy
  cases side
  · have hin := hsub hw₀S
    rw [halfSpace_false, mem_setOf_eq, hL₀] at hin
    exact lt_irrefl _ hin
  · have hin := hsub hw₁S
    rw [halfSpace_true, mem_setOf_eq, hL₁] at hin
    linarith

/-- Vanishing of all `2 × 2` minors of all difference vectors is exactly collinearity. -/
theorem collinear_of_minor_eq {S : Set (EuclideanSpace ℝ (Fin n))}
    (h : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, ∀ i j : Fin n,
      (y i - x i) * (z j - x j) = (y j - x j) * (z i - x i)) :
    Collinear ℝ S := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact collinear_empty ℝ _
  rw [collinear_iff_of_mem hx]
  by_cases hall : ∀ y ∈ S, y = x
  · exact ⟨0, fun p hp => ⟨0, by rw [hall p hp]; simp⟩⟩
  push_neg at hall
  obtain ⟨y, hy, hyx⟩ := hall
  have hex : ∃ i₀ : Fin n, y i₀ - x i₀ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hyx (PiLp.ext fun i => by have := hcon i; linarith)
  obtain ⟨i₀, hi₀⟩ := hex
  refine ⟨y - x, fun z hz => ⟨(z i₀ - x i₀) / (y i₀ - x i₀), PiLp.ext fun j => ?_⟩⟩
  have hco : ((((z i₀ - x i₀) / (y i₀ - x i₀)) • (y - x) +ᵥ x : EuclideanSpace ℝ (Fin n)) j)
      = (z i₀ - x i₀) / (y i₀ - x i₀) * (y j - x j) + x j := rfl
  rw [hco]
  have hm := h x hx y hy z hz i₀ j
  field_simp
  linarith [hm]

/-- **The localisation chain over the rational coordinate flats: the limit body is a segment.**

Every rational coordinate flat is cut through at its own stage of the chain, and by
`Arlib.minor_eq_of_pencil_exhaustion` that forces `⋂ m, C m` to be collinear.  Along the whole
chain `∫ g₁ = 0` **exactly** and `∫ g₂ > 0`.

This is the Lovász–Simonovits localisation induction with *combinatorial* thinness — no diameter
decays (`Arlib.le_diam_of_sign_separated` forbids it) and none is asked for. -/
theorem exists_flat_cut_chain_collinear (hn : 2 ≤ n) {g₁ g₂ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg₁ : Integrable g₁) (hg₂ : Integrable g₂) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKconv : Convex ℝ K)
    (hz : ∫ x in K, g₁ x = 0) (hp : 0 < ∫ x in K, g₂ x) :
    ∃ C : ℕ → Set (EuclideanSpace ℝ (Fin n)), C 0 = K ∧ (∀ m, C (m + 1) ⊆ C m) ∧
      (∀ m, MeasurableSet (C m) ∧ C m ⊆ K ∧ Convex ℝ (C m) ∧
        (∫ x in C m, g₁ x) = 0 ∧ 0 < ∫ x in C m, g₂ x) ∧
      Collinear ℝ (⋂ m, C m) := by
  classical
  have hne : Nonempty {p : Fin n × Fin n // p.1 ≠ p.2} :=
    ⟨⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.ext_iff]⟩⟩
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ({p : Fin n × Fin n // p.1 ≠ p.2} × ℚ × ℚ), Function.Surjective f :=
    exists_surjective_nat _
  obtain ⟨C, hC0, hCmono, hCinv, hCcut⟩ := exists_flat_cut_chain
    (d₁ := fun m => EuclideanSpace.single (f m).1.1.1 (1 : ℝ))
    (d₂ := fun m => EuclideanSpace.single (f m).1.1.2 (1 : ℝ))
    (fun m => inner_single_one_self _) (fun m => inner_single_one_self _)
    (fun m => inner_single_one_ne (f m).1.2)
    (fun m => ((f m).2.1 : ℝ)) (fun m => ((f m).2.2 : ℝ)) hK hg₁ hg₂ hz hp
  refine ⟨C, hC0, hCmono, fun m => ⟨(hCinv m).1, (hCinv m).2.1, (hCinv m).2.2.1 hKconv,
    (hCinv m).2.2.2.1, (hCinv m).2.2.2.2⟩, ?_⟩
  refine collinear_of_minor_eq (fun x hx y hy z hz' => ?_)
  refine minor_eq_of_pencil_exhaustion (convex_iInter fun m => (hCinv m).2.2.1 hKconv)
    (fun i j hij r s => ?_) hx hy hz'
  obtain ⟨m, hm⟩ := hf (⟨(i, j), hij⟩, r, s)
  obtain ⟨θ, side, hsub⟩ := hCcut m
  rw [hm] at hsub
  exact ⟨θ, side, (iInter_subset C (m + 1)).trans hsub⟩

/-- **Non-vacuity of the localisation chain.**

Every hypothesis of `Arlib.exists_flat_cut_chain_collinear` is met simultaneously by the unit
ball of the Euclidean plane with `g₁ = 0` and `g₂` the indicator of that ball, and the chain it
produces has *positive* `g₂`-mass at every stage together with a collinear limit body.  So the
theorem is not a statement about an empty configuration.

`g₁ = 0` is the degenerate-but-legitimate choice here: what the witness certifies is that the
typeclass bundle, the measurability and integrability hypotheses, and the two mass invariants can
hold at once with `0 < ∫ g₂`. -/
theorem exists_flat_cut_chain_collinear_ball :
    ∃ C : ℕ → Set (EuclideanSpace ℝ (Fin 2)),
      C 0 = Metric.closedBall 0 1 ∧ (∀ m, C (m + 1) ⊆ C m) ∧
      (∀ m, MeasurableSet (C m) ∧ C m ⊆ Metric.closedBall 0 1 ∧ Convex ℝ (C m) ∧
        (∫ _x in C m, (0 : ℝ)) = 0 ∧
        0 < ∫ x in C m, Set.indicator (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
          (fun _ => (1 : ℝ)) x) ∧
      Collinear ℝ (⋂ m, C m) := by
  have hKm : MeasurableSet (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    measurableSet_closedBall
  have hKfin : volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) ≠ ⊤ :=
    measure_closedBall_lt_top.ne
  have hKpos : 0 < volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    measure_closedBall_pos volume 0 one_pos
  have hg₂ : Integrable (Set.indicator (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
      (fun _ => (1 : ℝ))) := (integrable_indicator_iff hKm).mpr (integrableOn_const hKfin)
  have hp : 0 < ∫ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
      Set.indicator (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
        (fun _ => (1 : ℝ)) x := by
    rw [setIntegral_indicator hKm, Set.inter_self, setIntegral_const, smul_eq_mul, mul_one,
      measureReal_def]
    exact ENNReal.toReal_pos hKpos.ne' hKfin
  exact exists_flat_cut_chain_collinear (by norm_num) (integrable_zero _ _ _) hg₂ hKm
    (convex_closedBall _ _) (integral_zero _ _) hp

end Coordinates

/-! ### Strictness: what the perturbation of `g₂` buys -/

section Strictness

variable {E : Type*} [MeasurableSpace E] {μ : Measure E}

/-- **The perturbation that converts `≥ 0` into `> 0` in the limit.**

Running the chain with `g₂` replaced by `g₂ - ε · 1_K` keeps, at every stage, not merely
`∫_{C} g₂ > 0` but the *quantitative* `∫_C g₂ > ε · vol C`.  Dividing by `vol C`, the normalised
`g₂`-masses stay bounded below by `ε`, so any limit of them is `≥ ε > 0` — which is exactly the
strict inequality the equality form of the Localization Lemma asserts for `g₂`, and the only
place a perturbation is needed (`g₁` keeps its equality for free). -/
theorem lt_setIntegral_of_perturbed {C K : Set E} (hCK : C ⊆ K) (hC : MeasurableSet C)
    (hCfin : μ C ≠ ⊤) {g₂ : E → ℝ} (hg₂ : IntegrableOn g₂ C μ) {ε : ℝ}
    (h : 0 < ∫ x in C, (g₂ x - ε * K.indicator (fun _ => (1 : ℝ)) x) ∂μ) :
    ε * (μ C).toReal < ∫ x in C, g₂ x ∂μ := by
  have hind : ∀ x ∈ C, K.indicator (fun _ => (1 : ℝ)) x = 1 := fun x hx =>
    Set.indicator_of_mem (hCK hx) _
  have hcongr : (∫ x in C, (g₂ x - ε * K.indicator (fun _ => (1 : ℝ)) x) ∂μ)
      = ∫ x in C, (g₂ x - ε) ∂μ := by
    refine setIntegral_congr_fun hC (fun x hx => ?_)
    rw [hind x hx, mul_one]
  rw [hcongr, integral_sub hg₂ (integrableOn_const hCfin), setIntegral_const, smul_eq_mul,
    Measure.real] at h
  linarith

end Strictness

/-! ### The two conclusions of the equality form, in the limit -/

section NeedleConclusion

variable {m : ℕ}

/-- **The equality form's two conclusions, delivered by the limit passage.**

Take the limit passage exactly as `Arlib.tendsto_average_setIntegral_of_profile` states it — same
hypotheses, same shape — and feed it the two invariants that the localisation chain of
`Arlib.exists_flat_cut_chain` maintains:

* `∫_{C k} g₁ = 0` at every stage, and
* `ε · vol (C k) ≤ ∫_{C k} g₂` at every stage (the quantitative form of positivity that the
  perturbed integrand of `Arlib.lt_setIntegral_of_perturbed` provides).

Then the limiting **needle integrals** satisfy `∫ W(t) g₁(axis t) dt = 0` *exactly* and
`∫ W(t) g₂(axis t) dt ≥ ε > 0`.  These are precisely the two conclusions of the equality-refined
Localization Lemma (KLS 1995, Corollary 2.4) once `W` is recognised as `ℓ^{n-1}`.

The equality really is free: the `g₁` sequence is *identically zero*, so no limit theorem can
degrade it.  Strictness for `g₂` is bought entirely by the perturbation, which is why only `g₂`
needs one. -/
theorem needleIntegral_eq_zero_and_ge {C : ℕ → Set (Fin (m + 1) → ℝ)}
    (hCm : ∀ k, MeasurableSet (C k)) (hCfin : ∀ k, volume (C k) ≠ ⊤)
    (hCpos : ∀ k, 0 < volume (C k)) (hslab : ∀ k, ∀ x ∈ C k, x 0 ∈ Icc (0 : ℝ) 1)
    {g₁ g₂ : (Fin (m + 1) → ℝ) → ℝ} (hg₁m : Measurable g₁) (hg₂m : Measurable g₂)
    {M : ℝ} (hM₁ : ∀ x, |g₁ x| ≤ M) (hM₂ : ∀ x, |g₂ x| ≤ M)
    {δ : ℕ → ℝ}
    (hδ₁ : ∀ k, ∀ x ∈ C k, |g₁ x - g₁ (Fin.cons (x 0) (0 : Fin m → ℝ))| ≤ δ k)
    (hδ₂ : ∀ k, ∀ x ∈ C k, |g₂ x - g₂ (Fin.cons (x 0) (0 : Fin m → ℝ))| ≤ δ k)
    (hδ0 : Tendsto δ atTop (𝓝 0)) {W : ℝ → ℝ} {B : ℝ}
    (hB : ∀ k, ∀ t : ℝ, (volume (slice (C k) t)).toReal / (volume (C k)).toReal ≤ B)
    (hlim : ∀ t : ℝ, Tendsto
      (fun k => (volume (slice (C k) t)).toReal / (volume (C k)).toReal) atTop (𝓝 (W t)))
    (hzero : ∀ k, (∫ x in C k, g₁ x) = 0)
    {ε : ℝ} (hεpos : 0 < ε) (hge : ∀ k, ε * (volume (C k)).toReal ≤ ∫ x in C k, g₂ x) :
    (∫ t : ℝ, W t * g₁ (Fin.cons t (0 : Fin m → ℝ))) = 0 ∧
      0 < ∫ t : ℝ, W t * g₂ (Fin.cons t (0 : Fin m → ℝ)) := by
  have hVpos : ∀ k, 0 < (volume (C k)).toReal := fun k =>
    ENNReal.toReal_pos (hCpos k).ne' (hCfin k)
  constructor
  · have h := tendsto_average_setIntegral_of_profile hCm hCfin hCpos hslab hg₁m hM₁ hδ₁ hδ0 hB hlim
    have hconst : (fun k => (∫ x in C k, g₁ x) / (volume (C k)).toReal) = fun _ => (0 : ℝ) := by
      funext k; rw [hzero k, zero_div]
    rw [hconst] at h
    exact (tendsto_nhds_unique tendsto_const_nhds h).symm
  · have h := tendsto_average_setIntegral_of_profile hCm hCfin hCpos hslab hg₂m hM₂ hδ₂ hδ0 hB hlim
    have hεle : ε ≤ ∫ t : ℝ, W t * g₂ (Fin.cons t (0 : Fin m → ℝ)) := by
      refine ge_of_tendsto' h (fun k => ?_)
      rw [le_div_iff₀ (hVpos k)]
      exact (hge k).trans_eq (by ring_nf)
    linarith

end NeedleConclusion

end Arlib

/-! ### Axiom audit -/

#print axioms Arlib.pencilFun_apply
#print axioms Arlib.pencilFun_eq_pencilLevel
#print axioms Arlib.pencilFun_add_pi
#print axioms Arlib.pencilLevel_add_pi
#print axioms Arlib.pencilFun_ne_zero
#print axioms Arlib.continuous_pencilMass
#print axioms Arlib.exists_pencil_bisecting
#print axioms Arlib.exists_flat_cut_zero_pos
#print axioms Arlib.notMem_interior_halfSpace
#print axioms Arlib.notMem_interior_of_subset_halfSpace
#print axioms Arlib.exists_flat_cut_chain
#print axioms Arlib.notMem_interior_of_pencil_cut
#print axioms Arlib.interior_nonempty_of_setIntegral_pos
#print axioms Arlib.convex_three_mem
#print axioms Arlib.pencil_solve
#print axioms Arlib.inner_single_one
#print axioms Arlib.inner_single_one_self
#print axioms Arlib.inner_single_one_ne
#print axioms Arlib.pencilFun_single_apply
#print axioms Arlib.exists_mem_coords
#print axioms Arlib.minor_eq_of_pencil_exhaustion
#print axioms Arlib.collinear_of_minor_eq
#print axioms Arlib.exists_flat_cut_chain_collinear
#print axioms Arlib.exists_flat_cut_chain_collinear_ball
#print axioms Arlib.lt_setIntegral_of_perturbed
#print axioms Arlib.needleIntegral_eq_zero_and_ge
