/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.Cheeger
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# From the spectral gap to a total-variation decay rate

`Arlib.MarkovChains.Continuous.Cheeger` proves Cheeger's inequality `Φ²/2 ≤ gap ≤ 2 Φ`.
A spectral gap is not yet a mixing bound: what a sampler consumes is a *total variation*
statement about the law of the chain.  This module supplies the two missing steps — the
`L²` contraction of the chain's action on densities, and the `χ²`/`L²` → TV comparison —
and assembles them with Cheeger into the Lovász–Simonovits decay bound

`d_TV(mu_s, pi) ≤ √M (1 − phi²/2)^s`,

which is exactly the `hdecay` hypothesis that
`Arlib.MarkovChains.mixesWithin_of_conductance_decay` leaves to its caller.
`mixesWithin_of_conductance` discharges it.

## The three steps

1. **`L²` contraction from the spectral gap** — `varianceReal_markovIter_le`:
   `Var(T^t f) ≤ (1 − gap)^{2t} Var(f)`, where `T` (`markovOp`) is the Markov operator
   `(T f)(x) = ∫ f dP_x`.  Note the exponent `2t`: a `(1 − gap)^t` bound is **false** in
   general — the deterministic two-cycle on `Bool` is reversible with `gap = 2` and does not
   contract at all — which is what `HasNonnegSpectrum` is there to rule out.
2. **`χ²`/`L²` → TV** — `tvLe_withDensity`: a law with density `h` against `pi` is within
   total variation `√(Var_pi h)` of `pi`.  Cauchy–Schwarz, no Markov chain involved.
3. **Assembly** — `tvLe_iterate_of_isWarm`, then `tvLe_iterate_of_conductance` and
   `mixesWithin_of_conductance`.

## The linchpin: swap-invariance of `pi ⊗ₘ P`

`IsReversible` is a statement about measurable *rectangles*.  `ext_of_generate_finite` on
the π-system of rectangles upgrades it to `map_swap_compProd_of_isReversible`:
`(pi ⊗ₘ P).map Prod.swap = pi ⊗ₘ P`.  Everything else — self-adjointness of `T`
(`pairing_comm`), the identity `E(f,f) = ‖f‖² − ⟪f,f⟫` (`dirichletFormReal_eq_sub_pairing`),
and the fact that the chain acts on densities by `T` (`step_withDensity_ofReal`) — is a
corollary of that one lemma.

## The hypotheses, and why none of them assumes the conclusion

* `IsReversible P pi` — detailed balance.
* `HasNonnegSpectrum P pi` — `∫ f · (T f) dpi ≥ 0` for `f ∈ L²(pi)`.  A property of the
  *kernel*: it is what laziness buys, and it mentions neither the conductance, nor the
  spectral gap, nor any mixing rate.  Without it the `L²` contraction is false, not merely
  unproven.  `hasNonnegSpectrum_const` is a witness.
* `(rayleighSet P pi).Nonempty` — the hypothesis of Cheeger's hard direction, forced by
  `sInf ∅ = 0` over `ℝ`.
* `IsWarm (ENNReal.ofReal M) mu0 pi` and `phi ≤ (conductance P pi).toReal` — the warm start
  and the conductance bound.

There is no `def`, `structure` field or predicate in this file that names the mixing bound,
the Cheeger inequality or an isoperimetric constant and stands in for its proof.
`exists_hasNonnegSpectrum_and_conductance` exhibits one chain satisfying every hypothesis
simultaneously, so none of the statements below is vacuous.

## References

* Lovász–Simonovits, *Random walks in a convex body and an improved volume algorithm*,
  RSA 1993, Theorem 4.1 (`vol3_journal.tex:523`).
* Cousins–Vempala, *Gaussian cooling and `O*(n³)` algorithms for volume and Gaussian
  volume*, §4.1.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## The two-step measure `pi ⊗ₘ P` of a reversible chain

Detailed balance says the flow across a measurable rectangle is symmetric.  Since the
rectangles form a π-system generating the product σ-algebra, that setwise statement upgrades
to an equality of *measures*: `pi ⊗ₘ P` is invariant under swapping the two coordinates.
Every self-adjointness statement below is a consequence of this one lemma. -/

/-- The `pi ⊗ₘ P`-measure of a measurable rectangle is the ergodic flow across it. -/
theorem compProd_apply_prod_eq_flow (P : Kernel Ω Ω) [IsMarkovKernel P] (pi : Measure Ω)
    [IsProbabilityMeasure pi] {S T : Set Ω} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (pi ⊗ₘ P) (S ×ˢ T) = flow P pi S T :=
  Measure.compProd_apply_prod hS hT

/-- **Detailed balance is symmetry of `pi ⊗ₘ P`.**  The measure of the one-step pair
`(X₀, X₁)` started from stationarity is unchanged by exchanging the two coordinates.

This is `IsReversible` — a statement about rectangles — promoted to a statement about all
measurable sets, by `ext_of_generate_finite` on the π-system of rectangles. -/
theorem map_swap_compProd_of_isReversible {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) :
    (pi ⊗ₘ P).map Prod.swap = pi ⊗ₘ P := by
  have hswap : Measurable (Prod.swap : Ω × Ω → Ω × Ω) := measurable_swap
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro _ ⟨S, hS, T, hT, rfl⟩
    simp only [Set.mem_setOf_eq] at hS hT
    rw [Measure.map_apply hswap (hS.prod hT)]
    have hpre : Prod.swap ⁻¹' (S ×ˢ T) = T ×ˢ S := by
      ext p; simp [Set.mem_prod, and_comm]
    rw [hpre, compProd_apply_prod_eq_flow P pi hT hS,
      compProd_apply_prod_eq_flow P pi hS hT, hrev T S hT hS]
  · rw [Measure.map_apply hswap MeasurableSet.univ]
    simp

/-- **The swap-invariance, in `ℝ≥0∞` integral form.** -/
theorem lintegral_compProd_swap {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) {F : Ω × Ω → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ p, F (p.2, p.1) ∂(pi ⊗ₘ P) = ∫⁻ p, F p ∂(pi ⊗ₘ P) := by
  have hswap : Measurable (Prod.swap : Ω × Ω → Ω × Ω) := measurable_swap
  calc ∫⁻ p, F (p.2, p.1) ∂(pi ⊗ₘ P)
      = ∫⁻ p, F p ∂((pi ⊗ₘ P).map Prod.swap) := (lintegral_map hF hswap).symm
    _ = ∫⁻ p, F p ∂(pi ⊗ₘ P) := by rw [map_swap_compProd_of_isReversible hrev]

/-- **The swap-invariance, in Bochner integral form.** -/
theorem integral_compProd_swap {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) {F : Ω × Ω → ℝ}
    (hF : AEStronglyMeasurable F (pi ⊗ₘ P)) :
    ∫ p, F (p.2, p.1) ∂(pi ⊗ₘ P) = ∫ p, F p ∂(pi ⊗ₘ P) := by
  have hswap : Measurable (Prod.swap : Ω × Ω → Ω × Ω) := measurable_swap
  have hmap := map_swap_compProd_of_isReversible hrev
  calc ∫ p, F (p.2, p.1) ∂(pi ⊗ₘ P)
      = ∫ p, F p ∂((pi ⊗ₘ P).map Prod.swap) := by
        rw [integral_map hswap.aemeasurable (by rwa [hmap])]
        rfl
    _ = ∫ p, F p ∂(pi ⊗ₘ P) := by rw [hmap]

/-! ## The two marginals -/

/-- The first marginal of `pi ⊗ₘ P` is `pi`. -/
theorem map_fst_compProd (P : Kernel Ω Ω) [IsMarkovKernel P] (pi : Measure Ω)
    [IsProbabilityMeasure pi] : (pi ⊗ₘ P).map Prod.fst = pi :=
  Measure.fst_compProd pi P

/-- The second marginal of `pi ⊗ₘ P` is `pi`, for a reversible chain. -/
theorem map_snd_compProd_of_isReversible {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) :
    (pi ⊗ₘ P).map Prod.snd = pi := by
  have hswap : Measurable (Prod.swap : Ω × Ω → Ω × Ω) := measurable_swap
  calc (pi ⊗ₘ P).map Prod.snd
      = ((pi ⊗ₘ P).map Prod.swap).map Prod.fst := by
        rw [Measure.map_map measurable_fst hswap]; rfl
    _ = pi := by rw [map_swap_compProd_of_isReversible hrev, map_fst_compProd P pi]

/-- Integrability of a function of the *first* coordinate is integrability against `pi`. -/
theorem integrable_comp_fst {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] {F : Ω → ℝ} (hF : Measurable F) (h : Integrable F pi) :
    Integrable (fun p : Ω × Ω => F p.1) (pi ⊗ₘ P) := by
  rw [← map_fst_compProd P pi] at h
  exact (integrable_map_measure hF.aestronglyMeasurable measurable_fst.aemeasurable).1 h

/-- Integrability of a function of the *second* coordinate is integrability against `pi`,
for a reversible (hence stationary) chain. -/
theorem integrable_comp_snd {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) {F : Ω → ℝ} (hF : Measurable F)
    (h : Integrable F pi) : Integrable (fun p : Ω × Ω => F p.2) (pi ⊗ₘ P) := by
  rw [← map_snd_compProd_of_isReversible hrev] at h
  exact (integrable_map_measure hF.aestronglyMeasurable measurable_snd.aemeasurable).1 h

/-- Integrating a function of the first coordinate is integrating against `pi`. -/
theorem integral_comp_fst {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] {F : Ω → ℝ} (hF : Measurable F) :
    ∫ p, F p.1 ∂(pi ⊗ₘ P) = ∫ x, F x ∂pi := by
  conv_rhs => rw [← map_fst_compProd P pi]
  exact (integral_map measurable_fst.aemeasurable hF.aestronglyMeasurable).symm

/-- Integrating a function of the second coordinate is integrating against `pi`. -/
theorem integral_comp_snd {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) {F : Ω → ℝ} (hF : Measurable F) :
    ∫ p, F p.2 ∂(pi ⊗ₘ P) = ∫ x, F x ∂pi := by
  conv_rhs => rw [← map_snd_compProd_of_isReversible hrev]
  exact (integral_map measurable_snd.aemeasurable hF.aestronglyMeasurable).symm

/-! ## The Markov operator

`(T f)(x) = ∫ f(y) dP_x(y)` is the action of the chain on *observables*; it is adjoint to
the action `step` on laws.  Everything in this file is an identity or an inequality about
`T` on `L²(pi)`. -/

/-- The **Markov operator** of the kernel `P`: `(T f)(x) = ∫ f(y) dP_x(y)`, the expected
value of `f` one step after `x`.  Total, with the Bochner junk value `0` where `f` fails to
be `P x`-integrable. -/
noncomputable def markovOp (P : Kernel Ω Ω) (f : Ω → ℝ) : Ω → ℝ := fun x => ∫ y, f y ∂(P x)

/-- Unfolding lemma for `markovOp`. -/
theorem markovOp_apply (P : Kernel Ω Ω) (f : Ω → ℝ) (x : Ω) :
    markovOp P f x = ∫ y, f y ∂(P x) := rfl

/-- `T f` is measurable whenever `f` is. -/
theorem measurable_markovOp (P : Kernel Ω Ω) [IsSFiniteKernel P] {f : Ω → ℝ}
    (hf : Measurable f) : Measurable (markovOp P f) :=
  (StronglyMeasurable.integral_kernel_prod_right' (κ := P)
    (hf.comp measurable_snd).stronglyMeasurable).measurable

/-- `T` preserves nonnegativity. -/
theorem markovOp_nonneg (P : Kernel Ω Ω) {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) (x : Ω) :
    0 ≤ markovOp P f x :=
  integral_nonneg fun _ => hf _

/-- **`T` preserves the mean**: `∫ T f dpi = ∫ f dpi`, because `pi` is stationary. -/
theorem integral_markovOp {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) {f : Ω → ℝ} (hf : Measurable f)
    (hint : Integrable f pi) : ∫ x, markovOp P f x ∂pi = ∫ x, f x ∂pi := by
  calc ∫ x, markovOp P f x ∂pi = ∫ p, f p.2 ∂(pi ⊗ₘ P) :=
        (Measure.integral_compProd (integrable_comp_snd hrev hf hint)).symm
    _ = ∫ x, f x ∂pi := integral_comp_snd hrev hf

/-! ## The Dirichlet pairing

`⟪f, g⟫ = ∫∫ f(x) g(y) d(pi ⊗ₘ P)` is `∫ f · (T g) dpi` written symmetrically.  Its
symmetry in `f` and `g` — self-adjointness of `T` — is `map_swap_compProd_of_isReversible`
and nothing else. -/

/-- The **Dirichlet pairing** `⟪f, g⟫_P = ∫∫ f(x) g(y) d(pi ⊗ₘ P)(x,y)`, i.e.
`∫ f · (T g) dpi` (`pairing_eq_integral_mul_markovOp`). -/
noncomputable def pairing (P : Kernel Ω Ω) (pi : Measure Ω) (f g : Ω → ℝ) : ℝ :=
  ∫ p, f p.1 * g p.2 ∂(pi ⊗ₘ P)

/-- Unfolding lemma for `pairing`. -/
theorem pairing_apply (P : Kernel Ω Ω) (pi : Measure Ω) (f g : Ω → ℝ) :
    pairing P pi f g = ∫ p, f p.1 * g p.2 ∂(pi ⊗ₘ P) := rfl

/-- **The product `f(x) g(y)` is `pi ⊗ₘ P`-integrable** for measurable `f, g ∈ L²(pi)`: it
is dominated by `(f(x)² + g(y)²)/2` and both marginals of `pi ⊗ₘ P` are `pi`. -/
theorem integrable_mul_compProd {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) {f g : Ω → ℝ} (hf : Measurable f)
    (hg : Measurable g) (hfm : MemLp f 2 pi) (hgm : MemLp g 2 pi) :
    Integrable (fun p : Ω × Ω => f p.1 * g p.2) (pi ⊗ₘ P) := by
  have h1 : Integrable (fun p : Ω × Ω => f p.1 ^ 2) (pi ⊗ₘ P) :=
    integrable_comp_fst (hf.pow_const 2) hfm.integrable_sq
  have h2 : Integrable (fun p : Ω × Ω => g p.2 ^ 2) (pi ⊗ₘ P) :=
    integrable_comp_snd hrev (hg.pow_const 2) hgm.integrable_sq
  refine Integrable.mono' ((h1.add h2).div_const 2)
    ((hf.comp measurable_fst).mul (hg.comp measurable_snd)).aestronglyMeasurable ?_
  filter_upwards with p
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|f p.1| - |g p.2|), sq_abs (f p.1), sq_abs (g p.2)]

/-- **Self-adjointness of the Markov operator**, in pairing form: `⟪f, g⟫ = ⟪g, f⟫`.

The proof is the swap-invariance of `pi ⊗ₘ P`; no integrability hypothesis is needed
because `integral_map` holds unconditionally. -/
theorem pairing_comm {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) {f g : Ω → ℝ} (hf : Measurable f)
    (hg : Measurable g) : pairing P pi f g = pairing P pi g f := by
  have hswap := integral_compProd_swap hrev (F := fun p : Ω × Ω => f p.1 * g p.2)
    ((hf.comp measurable_fst).mul (hg.comp measurable_snd)).aestronglyMeasurable
  rw [pairing, pairing, ← hswap]
  exact integral_congr_ae (Filter.Eventually.of_forall fun p => mul_comm _ _)

/-- **The pairing is `∫ f · (T g) dpi`.** -/
theorem pairing_eq_integral_mul_markovOp {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] {f g : Ω → ℝ}
    (hint : Integrable (fun p : Ω × Ω => f p.1 * g p.2) (pi ⊗ₘ P)) :
    pairing P pi f g = ∫ x, f x * markovOp P g x ∂pi := by
  rw [pairing, Measure.integral_compProd hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show ∫ y, f x * g y ∂(P x) = f x * markovOp P g x
  exact integral_const_mul _ _

/-! ## The Dirichlet form is `‖f‖² − ⟪f, f⟫` -/

/-- The `ℝ`-valued Dirichlet form as a single integral against `pi ⊗ₘ P`. -/
theorem two_mul_dirichletFormReal_eq (P : Kernel Ω Ω) [IsMarkovKernel P] (pi : Measure Ω)
    [IsProbabilityMeasure pi] {f : Ω → ℝ}
    (hint : Integrable (fun p : Ω × Ω => (f p.1 - f p.2) ^ 2) (pi ⊗ₘ P)) :
    2 * dirichletFormReal P pi f = ∫ p, (f p.1 - f p.2) ^ 2 ∂(pi ⊗ₘ P) := by
  rw [Measure.integral_compProd hint, dirichletFormReal]
  ring

/-- **`E(f, f) = ∫ f² dpi − ⟪f, f⟫`.**  Expanding `(f x − f y)²` and using that both
marginals of `pi ⊗ₘ P` are `pi`.  This is the identity that turns the spectral gap — a
statement about `E` — into a bound on the pairing, i.e. on `T`. -/
theorem dirichletFormReal_eq_sub_pairing {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) {f : Ω → ℝ} (hf : Measurable f)
    (hmem : MemLp f 2 pi) :
    dirichletFormReal P pi f = (∫ x, f x ^ 2 ∂pi) - pairing P pi f f := by
  have hinv := hrev.invariant
  have hsub : Integrable (fun p : Ω × Ω => (f p.1 - f p.2) ^ 2) (pi ⊗ₘ P) :=
    integrable_sq_sub_compProd hinv hf hmem
  have h1 : Integrable (fun p : Ω × Ω => f p.1 ^ 2) (pi ⊗ₘ P) :=
    integrable_comp_fst (hf.pow_const 2) hmem.integrable_sq
  have h2 : Integrable (fun p : Ω × Ω => f p.2 ^ 2) (pi ⊗ₘ P) :=
    integrable_comp_snd hrev (hf.pow_const 2) hmem.integrable_sq
  have h3 : Integrable (fun p : Ω × Ω => f p.1 * f p.2) (pi ⊗ₘ P) :=
    integrable_mul_compProd hrev hf hf hmem hmem
  have key : 2 * dirichletFormReal P pi f
      = ((∫ x, f x ^ 2 ∂pi) + ∫ x, f x ^ 2 ∂pi) - 2 * pairing P pi f f := by
    rw [two_mul_dirichletFormReal_eq P pi hsub]
    have hcongr : ∫ p, (f p.1 - f p.2) ^ 2 ∂(pi ⊗ₘ P)
        = ∫ p, ((f p.1 ^ 2 + f p.2 ^ 2) - 2 * (f p.1 * f p.2)) ∂(pi ⊗ₘ P) :=
      integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
    have h12 : Integrable (fun p : Ω × Ω => f p.1 ^ 2 + f p.2 ^ 2) (pi ⊗ₘ P) := h1.add h2
    have h3' : Integrable (fun p : Ω × Ω => 2 * (f p.1 * f p.2)) (pi ⊗ₘ P) := h3.const_mul 2
    rw [hcongr, integral_sub h12 h3', integral_add h1 h2,
      integral_const_mul, integral_comp_fst (hf.pow_const 2),
      integral_comp_snd hrev (hf.pow_const 2), pairing]
  linarith

/-! ## `T` is an `L²(pi)` contraction (Jensen)

Before the spectral gap can improve the contraction factor to `1 − gap`, one needs to know
that `T` maps `L²(pi)` to itself at all.  That is Jensen's inequality `(T f)² ≤ T (f²)`
followed by stationarity of `pi`. -/

/-- `‖r‖ₑ² = ofReal (r²)` for a real `r`. -/
theorem enorm_sq_eq_ofReal_sq (r : ℝ) : ‖r‖ₑ ^ 2 = ENNReal.ofReal (r ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

/-- **Jensen's inequality for one step of the chain**: `(T f)(x)² ≤ (T f²)(x)`.

Proved from `‖∫ f‖ₑ ≤ ∫⁻ ‖f‖ₑ` and Hölder with `p = q = 2` on the probability measure
`P x`; no integrability hypothesis is needed because the Bochner junk value is `0`. -/
theorem ofReal_sq_markovOp_le (P : Kernel Ω Ω) [IsMarkovKernel P] {f : Ω → ℝ}
    (hf : Measurable f) (x : Ω) :
    ENNReal.ofReal (markovOp P f x ^ 2) ≤ ∫⁻ y, ENNReal.ofReal (f y ^ 2) ∂(P x) := by
  have hpow : ∀ z : ℝ≥0∞, z ^ (2 : ℝ) = z ^ 2 := by
    intro z
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  set A : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal (f y ^ 2) ∂(P x) with hA
  have hAeq : ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂(P x) = A := by
    rw [hA]
    exact lintegral_congr fun y => by rw [hpow, enorm_sq_eq_ofReal_sq]
  have hCS : ∫⁻ y, ‖f y‖ₑ ∂(P x) ≤ A ^ (1 / 2 : ℝ) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (P x) Real.HolderConjugate.two_two
      hf.enorm.aemeasurable (aemeasurable_const (b := (1 : ℝ≥0∞)))
    simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ] at h
    rw [hAeq] at h
    simpa using h
  calc ENNReal.ofReal (markovOp P f x ^ 2) = ‖markovOp P f x‖ₑ ^ 2 :=
        (enorm_sq_eq_ofReal_sq _).symm
    _ ≤ (∫⁻ y, ‖f y‖ₑ ∂(P x)) ^ 2 := by
        gcongr
        exact enorm_integral_le_lintegral_enorm _
    _ ≤ (A ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = A := rpow_half_sq A

/-- **`T` does not increase the `L²(pi)` norm.**  Jensen pointwise, then stationarity of
`pi` to collapse the double integral. -/
theorem lintegral_sq_markovOp_le {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hinv : Kernel.Invariant P pi) {f : Ω → ℝ} (hf : Measurable f) :
    ∫⁻ x, ENNReal.ofReal (markovOp P f x ^ 2) ∂pi
      ≤ ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂pi := by
  have hm : Measurable fun x => ENNReal.ofReal (f x ^ 2) := (hf.pow_const 2).ennreal_ofReal
  calc ∫⁻ x, ENNReal.ofReal (markovOp P f x ^ 2) ∂pi
      ≤ ∫⁻ x, (∫⁻ y, ENNReal.ofReal (f y ^ 2) ∂(P x)) ∂pi :=
        lintegral_mono fun x => ofReal_sq_markovOp_le P hf x
    _ = ∫⁻ p, ENNReal.ofReal (f p.2 ^ 2) ∂(pi ⊗ₘ P) :=
        (Measure.lintegral_compProd (hm.comp measurable_snd)).symm
    _ = ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂pi := lintegral_compProd_snd_of_invariant hinv hm

/-- **`T` maps `L²(pi)` to itself.** -/
theorem memLp_markovOp {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hinv : Kernel.Invariant P pi) {f : Ω → ℝ} (hf : Measurable f)
    (hmem : MemLp f 2 pi) : MemLp (markovOp P f) 2 pi := by
  refine (memLp_two_iff_integrable_sq (measurable_markovOp P hf).aestronglyMeasurable).2 ?_
  refine ⟨((measurable_markovOp P hf).pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => sq_nonneg _)]
  exact lt_of_le_of_lt (lintegral_sq_markovOp_le hinv hf)
    (lintegral_sq_ne_top_of_memLp hmem).lt_top

/-! ## `T` is affine: the a.e. shift lemma

`T (f − c) = T f − c` requires `f` to be `P x`-integrable, which holds for `pi`-a.e. `x`
when `f ∈ L¹(pi)` and `pi` is stationary.  This is what lets a statement about *centred*
functions be applied to a density. -/

/-- **A `pi`-integrable `f` is `P x`-integrable for `pi`-almost every `x`.** -/
theorem ae_integrable_kernel {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) {f : Ω → ℝ} (hf : Measurable f)
    (hint : Integrable f pi) : ∀ᵐ x ∂pi, Integrable f (P x) := by
  have h := integrable_comp_snd hrev hf hint
  exact ((Measure.integrable_compProd_iff
    (hf.comp measurable_snd).aestronglyMeasurable).1 h).1

/-- **`T` commutes with subtracting a constant**, `pi`-almost everywhere. -/
theorem markovOp_sub_const {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) {f : Ω → ℝ} (hf : Measurable f)
    (hint : Integrable f pi) (c : ℝ) :
    markovOp P (fun y => f y - c) =ᵐ[pi] fun x => markovOp P f x - c := by
  filter_upwards [ae_integrable_kernel hrev hf hint] with x hx
  show ∫ y, (f y - c) ∂(P x) = markovOp P f x - c
  rw [integral_sub hx (integrable_const c), integral_const]
  simp [markovOp]

/-! ## The spectral gap as a bound on the pairing -/

/-- **The spectral gap bounds the pairing on centred functions**:
`⟪f, f⟫ ≤ (1 − gap) ∫ f² dpi` whenever `∫ f dpi = 0`.

This is `dirichletFormReal_eq_sub_pairing` combined with `spectralGap ≤ E / Var` and
`Var f = ∫ f²` for centred `f`.  The degenerate case `∫ f² = 0` is handled separately: there
`f` is not admissible, but `E(f,f) ≥ 0` already gives `⟪f,f⟫ ≤ 0`. -/
theorem pairing_self_le_of_integral_eq_zero {P : Kernel Ω Ω} [IsMarkovKernel P]
    {pi : Measure Ω} [IsProbabilityMeasure pi] (hrev : IsReversible P pi) {f : Ω → ℝ}
    (hf : Measurable f) (hmem : MemLp f 2 pi) (hmean : ∫ x, f x ∂pi = 0) :
    pairing P pi f f ≤ (1 - spectralGap P pi) * ∫ x, f x ^ 2 ∂pi := by
  have hE : dirichletFormReal P pi f = (∫ x, f x ^ 2 ∂pi) - pairing P pi f f :=
    dirichletFormReal_eq_sub_pairing hrev hf hmem
  have hvar : varianceReal pi f = ∫ x, f x ^ 2 ∂pi := by
    rw [varianceReal_eq_sub hmem, hmean]; ring
  have hA0 : 0 ≤ ∫ x, f x ^ 2 ∂pi := integral_nonneg fun _ => sq_nonneg _
  have hEnn := dirichletFormReal_nonneg P pi f
  rcases eq_or_lt_of_le hA0 with h0 | h0
  · rw [← h0] at hE ⊢
    rw [hE] at hEnn
    simp only [mul_zero]
    linarith
  · have hgap := spectralGap_le_rayleighQuotient P pi hmem (by rw [hvar]; exact h0.ne')
    rw [rayleighQuotient, hvar, hE, le_div_iff₀ h0] at hgap
    have hring : (1 - spectralGap P pi) * ∫ x, f x ^ 2 ∂pi
        = (∫ x, f x ^ 2 ∂pi) - spectralGap P pi * ∫ x, f x ^ 2 ∂pi := by ring
    linarith

/-! ## Nonnegative spectrum

A reversible chain with a spectral gap `g` contracts `L²` by `1 − g` *per step* only if its
Markov operator has no large negative eigenvalue; the deterministic two-cycle on `{0,1}` has
`gap = 2` and does not contract at all.  The standard fix in the sampling literature is
laziness.  The property that is actually used is the following one, which mentions neither
the conductance nor any mixing rate: the quadratic form of the Markov operator is
nonnegative.

`hasNonnegSpectrum_const` below is a witness, so the hypothesis is not vacuous. -/

/-- **The Markov operator is positive semidefinite**: `∫ f · (T f) dpi ≥ 0` for every
`f ∈ L²(pi)`.  For a lazy chain `P = (I + Q)/2` this holds because
`⟪f, P f⟫ = (‖f‖² + ⟪f, Q f⟫)/2 ≥ 0`.

This is a property of the *kernel* — it says nothing about conductance, spectral gap, or
mixing — and is the hypothesis under which the spectral gap gives a per-step `L²`
contraction. -/
def HasNonnegSpectrum (P : Kernel Ω Ω) (pi : Measure Ω) : Prop :=
  ∀ f : Ω → ℝ, Measurable f → MemLp f 2 pi → 0 ≤ pairing P pi f f

/-- **Expanding the quadratic form.** -/
theorem pairing_add_const_mul {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) {f g : Ω → ℝ} (hf : Measurable f)
    (hg : Measurable g) (hfm : MemLp f 2 pi) (hgm : MemLp g 2 pi) (t : ℝ) :
    pairing P pi (fun x => f x + t * g x) (fun x => f x + t * g x)
      = pairing P pi f f + 2 * t * pairing P pi f g + t ^ 2 * pairing P pi g g := by
  have I11 : Integrable (fun p : Ω × Ω => f p.1 * f p.2) (pi ⊗ₘ P) :=
    integrable_mul_compProd hrev hf hf hfm hfm
  have I12 : Integrable (fun p : Ω × Ω => t * (f p.1 * g p.2)) (pi ⊗ₘ P) :=
    (integrable_mul_compProd hrev hf hg hfm hgm).const_mul t
  have I21 : Integrable (fun p : Ω × Ω => t * (g p.1 * f p.2)) (pi ⊗ₘ P) :=
    (integrable_mul_compProd hrev hg hf hgm hfm).const_mul t
  have I22 : Integrable (fun p : Ω × Ω => t ^ 2 * (g p.1 * g p.2)) (pi ⊗ₘ P) :=
    (integrable_mul_compProd hrev hg hg hgm hgm).const_mul (t ^ 2)
  have hsym : pairing P pi g f = pairing P pi f g := pairing_comm hrev hg hf
  have hexp : ∫ p, (f p.1 + t * g p.1) * (f p.2 + t * g p.2) ∂(pi ⊗ₘ P)
      = ∫ p, (f p.1 * f p.2 + (t * (f p.1 * g p.2)
          + (t * (g p.1 * f p.2) + t ^ 2 * (g p.1 * g p.2)))) ∂(pi ⊗ₘ P) :=
    integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
  have J3 : Integrable
      (fun p : Ω × Ω => t * (g p.1 * f p.2) + t ^ 2 * (g p.1 * g p.2)) (pi ⊗ₘ P) := I21.add I22
  have J2 : Integrable (fun p : Ω × Ω =>
      t * (f p.1 * g p.2) + (t * (g p.1 * f p.2) + t ^ 2 * (g p.1 * g p.2))) (pi ⊗ₘ P) :=
    I12.add J3
  simp only [pairing] at hsym ⊢
  rw [hexp, integral_add I11 J2, integral_add I12 J3,
    integral_add I21 I22, integral_const_mul, integral_const_mul, integral_const_mul, hsym]
  ring

/-- **Cauchy–Schwarz for the Dirichlet pairing.**  A positive semidefinite symmetric
bilinear form satisfies `⟪f, g⟫² ≤ ⟪f, f⟫ ⟪g, g⟫`; the proof is the discriminant of the
nonnegative quadratic `t ↦ ⟪f + t g, f + t g⟫`. -/
theorem pairing_sq_le {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) (hpsd : HasNonnegSpectrum P pi)
    {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g) (hfm : MemLp f 2 pi)
    (hgm : MemLp g 2 pi) :
    (pairing P pi f g) ^ 2 ≤ pairing P pi f f * pairing P pi g g := by
  have hquad : ∀ t : ℝ, 0 ≤ pairing P pi g g * (t * t)
      + 2 * pairing P pi f g * t + pairing P pi f f := by
    intro t
    have h := hpsd (fun x => f x + t * g x) (hf.add (hg.const_mul t))
      (hfm.add (hgm.const_mul t))
    rw [pairing_add_const_mul hrev hf hg hfm hgm t] at h
    nlinarith [h]
  have hd := discrim_le_zero hquad
  rw [discrim] at hd
  nlinarith [hd]

/-! ## The `L²` contraction from the spectral gap -/

/-- **One step of the chain contracts the `L²(pi)` norm of a centred function by
`1 − gap`.**

`‖T f‖² = ⟪f, T f⟫` (self-adjointness), Cauchy–Schwarz bounds that by
`√(⟪f,f⟫ ⟪Tf,Tf⟫)`, and the spectral gap bounds each of `⟪f,f⟫, ⟪Tf,Tf⟫` by `(1 − gap)`
times the corresponding norm.  Solving gives `‖Tf‖² ≤ (1 − gap)² ‖f‖²`. -/
theorem integral_sq_markovOp_le {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) (hpsd : HasNonnegSpectrum P pi)
    {f : Ω → ℝ} (hf : Measurable f) (hmem : MemLp f 2 pi) (hmean : ∫ x, f x ∂pi = 0) :
    ∫ x, markovOp P f x ^ 2 ∂pi ≤ (1 - spectralGap P pi) ^ 2 * ∫ x, f x ^ 2 ∂pi := by
  have hu : Measurable (markovOp P f) := measurable_markovOp P hf
  have humem : MemLp (markovOp P f) 2 pi := memLp_markovOp hrev.invariant hf hmem
  have humean : ∫ x, markovOp P f x ∂pi = 0 := by
    rw [integral_markovOp hrev hf (hmem.integrable (by norm_num)), hmean]
  have hb : pairing P pi (markovOp P f) f = ∫ x, markovOp P f x ^ 2 ∂pi := by
    rw [pairing_eq_integral_mul_markovOp (integrable_mul_compProd hrev hu hf humem hmem)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => (pow_two _).symm)
  have hfu : pairing P pi f (markovOp P f) = ∫ x, markovOp P f x ^ 2 ∂pi := by
    rw [← pairing_comm hrev hu hf]; exact hb
  have hCS : (pairing P pi f (markovOp P f)) ^ 2
      ≤ pairing P pi f f * pairing P pi (markovOp P f) (markovOp P f) :=
    pairing_sq_le hrev hpsd hf hu hmem humem
  have hff := pairing_self_le_of_integral_eq_zero hrev hf hmem hmean
  have huu := pairing_self_le_of_integral_eq_zero hrev hu humem humean
  have hff0 : 0 ≤ pairing P pi f f := hpsd f hf hmem
  have huu0 : 0 ≤ pairing P pi (markovOp P f) (markovOp P f) := hpsd _ hu humem
  have hb0 : 0 ≤ ∫ x, markovOp P f x ^ 2 ∂pi := integral_nonneg fun _ => sq_nonneg _
  have hA0 : 0 ≤ ∫ x, f x ^ 2 ∂pi := integral_nonneg fun _ => sq_nonneg _
  have h1 : (∫ x, markovOp P f x ^ 2 ∂pi) ^ 2
      ≤ ((1 - spectralGap P pi) * ∫ x, f x ^ 2 ∂pi)
        * ((1 - spectralGap P pi) * ∫ x, markovOp P f x ^ 2 ∂pi) := by
    calc (∫ x, markovOp P f x ^ 2 ∂pi) ^ 2 = (pairing P pi f (markovOp P f)) ^ 2 := by rw [hfu]
      _ ≤ pairing P pi f f * pairing P pi (markovOp P f) (markovOp P f) := hCS
      _ ≤ _ := mul_le_mul hff huu huu0 (hff0.trans hff)
  rcases eq_or_lt_of_le hb0 with h | h
  · rw [← h]
    exact mul_nonneg (sq_nonneg _) hA0
  · have h2 : (∫ x, markovOp P f x ^ 2 ∂pi) * (∫ x, markovOp P f x ^ 2 ∂pi)
        ≤ ((1 - spectralGap P pi) ^ 2 * ∫ x, f x ^ 2 ∂pi)
          * (∫ x, markovOp P f x ^ 2 ∂pi) := by nlinarith [h1]
    exact le_of_mul_le_mul_right h2 h

/-- **The variance form of the one-step contraction.**  Centring `f` at its mean and using
that `T` commutes with the shift (`markovOp_sub_const`). -/
theorem varianceReal_markovOp_le {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) (hpsd : HasNonnegSpectrum P pi)
    {f : Ω → ℝ} (hf : Measurable f) (hmem : MemLp f 2 pi) :
    varianceReal pi (markovOp P f)
      ≤ (1 - spectralGap P pi) ^ 2 * varianceReal pi f := by
  have hint : Integrable f pi := hmem.integrable (by norm_num)
  set m : ℝ := ∫ x, f x ∂pi with hm
  set g : Ω → ℝ := fun x => f x - m with hg
  have hgmeas : Measurable g := hf.sub measurable_const
  have hgmem : MemLp g 2 pi := hmem.sub (memLp_const m)
  have hgmean : ∫ x, g x ∂pi = 0 := by
    rw [hg, integral_sub hint (integrable_const m), integral_const]
    simp [← hm]
  have hgvar : ∫ x, g x ^ 2 ∂pi = varianceReal pi f := by
    have h1 : varianceReal pi g = ∫ x, g x ^ 2 ∂pi := by
      rw [varianceReal_eq_sub hgmem, hgmean]; ring
    have h2 : varianceReal pi g = varianceReal pi f :=
      ProbabilityTheory.variance_sub_const hmem.aestronglyMeasurable m
    linarith
  -- the shift
  have hae : markovOp P g =ᵐ[pi] fun x => markovOp P f x - m :=
    markovOp_sub_const hrev hf hint m
  have hTgmem : MemLp (markovOp P g) 2 pi := memLp_markovOp hrev.invariant hgmeas hgmem
  have hTgmean : ∫ x, markovOp P g x ∂pi = 0 := by
    rw [integral_markovOp hrev hgmeas (hgmem.integrable (by norm_num)), hgmean]
  have hkey : varianceReal pi (markovOp P f) = ∫ x, markovOp P g x ^ 2 ∂pi := by
    have h1 : varianceReal pi (markovOp P f)
        = varianceReal pi (fun x => markovOp P f x - m) :=
      (ProbabilityTheory.variance_sub_const
        (measurable_markovOp P hf).aestronglyMeasurable m).symm
    have h2 : varianceReal pi (fun x => markovOp P f x - m) = varianceReal pi (markovOp P g) :=
      (ProbabilityTheory.variance_congr hae).symm
    have h3 : varianceReal pi (markovOp P g) = ∫ x, markovOp P g x ^ 2 ∂pi := by
      rw [varianceReal_eq_sub hTgmem, hTgmean]; ring
    rw [h1, h2, h3]
  rw [hkey, ← hgvar]
  exact integral_sq_markovOp_le hrev hpsd hgmeas hgmem hgmean

/-! ## Iterating the Markov operator -/

/-- `T^t f`, the `t`-step Markov operator applied to `f`. -/
noncomputable def markovIter (P : Kernel Ω Ω) (f : Ω → ℝ) : ℕ → (Ω → ℝ)
  | 0 => f
  | t + 1 => markovOp P (markovIter P f t)

@[simp] theorem markovIter_zero (P : Kernel Ω Ω) (f : Ω → ℝ) : markovIter P f 0 = f := rfl

@[simp] theorem markovIter_succ (P : Kernel Ω Ω) (f : Ω → ℝ) (t : ℕ) :
    markovIter P f (t + 1) = markovOp P (markovIter P f t) := rfl

theorem measurable_markovIter (P : Kernel Ω Ω) [IsSFiniteKernel P] {f : Ω → ℝ}
    (hf : Measurable f) (t : ℕ) : Measurable (markovIter P f t) := by
  induction t with
  | zero => exact hf
  | succ t ih => exact measurable_markovOp P ih

theorem markovIter_nonneg (P : Kernel Ω Ω) {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) (t : ℕ) (x : Ω) :
    0 ≤ markovIter P f t x := by
  induction t generalizing x with
  | zero => exact hf x
  | succ t ih => exact markovOp_nonneg P ih x

theorem memLp_markovIter {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hinv : Kernel.Invariant P pi) {f : Ω → ℝ} (hf : Measurable f)
    (hmem : MemLp f 2 pi) (t : ℕ) : MemLp (markovIter P f t) 2 pi := by
  induction t with
  | zero => exact hmem
  | succ t ih => exact memLp_markovOp hinv (measurable_markovIter P hf t) ih

theorem integral_markovIter {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) {f : Ω → ℝ} (hf : Measurable f)
    (hmem : MemLp f 2 pi) (t : ℕ) :
    ∫ x, markovIter P f t x ∂pi = ∫ x, f x ∂pi := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [markovIter_succ, integral_markovOp hrev (measurable_markovIter P hf t)
        ((memLp_markovIter hrev.invariant hf hmem t).integrable (by norm_num)), ih]

/-- **The `L²` contraction, iterated.**  `Var(T^t f) ≤ (1 − gap)^{2t} Var(f)`.

Note the exponent: it is `2t`, not `t`.  A `(1 − gap)^t` bound is *false* in general — the
deterministic two-cycle on `{0,1}` is reversible with `gap = 2` and does not contract at
all — which is what the `HasNonnegSpectrum` hypothesis is there to control. -/
theorem varianceReal_markovIter_le {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) (hpsd : HasNonnegSpectrum P pi)
    {f : Ω → ℝ} (hf : Measurable f) (hmem : MemLp f 2 pi) (t : ℕ) :
    varianceReal pi (markovIter P f t)
      ≤ ((1 - spectralGap P pi) ^ 2) ^ t * varianceReal pi f := by
  induction t with
  | zero => simp
  | succ t ih =>
      have h1 := varianceReal_markovOp_le hrev hpsd (measurable_markovIter P hf t)
        (memLp_markovIter hrev.invariant hf hmem t)
      calc varianceReal pi (markovIter P f (t + 1))
          ≤ (1 - spectralGap P pi) ^ 2 * varianceReal pi (markovIter P f t) := h1
        _ ≤ (1 - spectralGap P pi) ^ 2
              * (((1 - spectralGap P pi) ^ 2) ^ t * varianceReal pi f) :=
            mul_le_mul_of_nonneg_left ih (sq_nonneg _)
        _ = ((1 - spectralGap P pi) ^ 2) ^ (t + 1) * varianceReal pi f := by ring

/-! ## The chain acts on densities by the Markov operator

If `mu = h · pi` then `step P mu = (T h) · pi`.  This is again just the swap-invariance of
`pi ⊗ₘ P`: on a measurable `S` both sides are `∫∫ h(x) 1_S(y)` and `∫∫ 1_S(x) h(y)`. -/

/-- **One step of the chain on densities.** -/
theorem step_withDensity_ofReal {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) {g : Ω → ℝ} (hg : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) (hgint : Integrable g pi) :
    step P (pi.withDensity fun x => ENNReal.ofReal (g x))
      = pi.withDensity fun x => ENNReal.ofReal (markovOp P g x) := by
  have hgm : Measurable fun x => ENNReal.ofReal (g x) := hg.ennreal_ofReal
  have hTgm : Measurable fun x => ENNReal.ofReal (markovOp P g x) :=
    (measurable_markovOp P hg).ennreal_ofReal
  have hae : ∀ᵐ x ∂pi, ENNReal.ofReal (markovOp P g x)
      = ∫⁻ y, ENNReal.ofReal (g y) ∂(P x) := by
    filter_upwards [ae_integrable_kernel hrev hg hgint] with x hx
    exact ofReal_integral_eq_lintegral_ofReal hx (Filter.Eventually.of_forall hg0)
  ext S hS
  have hind : Measurable (Set.indicator S fun _ => (1 : ℝ≥0∞)) := measurable_const.indicator hS
  have hF : Measurable fun p : Ω × Ω =>
      ENNReal.ofReal (g p.1) * Set.indicator S (fun _ => (1 : ℝ≥0∞)) p.2 :=
    (hgm.comp measurable_fst).mul (hind.comp measurable_snd)
  have hF' : Measurable fun p : Ω × Ω =>
      ENNReal.ofReal (g p.2) * Set.indicator S (fun _ => (1 : ℝ≥0∞)) p.1 :=
    (hgm.comp measurable_snd).mul (hind.comp measurable_fst)
  -- the left-hand side
  have hL : step P (pi.withDensity fun x => ENNReal.ofReal (g x)) S
      = ∫⁻ p, ENNReal.ofReal (g p.1) * Set.indicator S (fun _ => (1 : ℝ≥0∞)) p.2
          ∂(pi ⊗ₘ P) := by
    rw [step_apply P _ hS,
      lintegral_withDensity_eq_lintegral_mul pi hgm (Kernel.measurable_coe P hS),
      Measure.lintegral_compProd hF]
    refine lintegral_congr fun x => ?_
    show ENNReal.ofReal (g x) * P x S
        = ∫⁻ b, ENNReal.ofReal (g x) * Set.indicator S (fun _ => (1 : ℝ≥0∞)) b ∂(P x)
    rw [lintegral_const_mul _ hind, lintegral_indicator hS, setLIntegral_one]
  -- the right-hand side
  have hR : (pi.withDensity fun x => ENNReal.ofReal (markovOp P g x)) S
      = ∫⁻ p, ENNReal.ofReal (g p.2) * Set.indicator S (fun _ => (1 : ℝ≥0∞)) p.1
          ∂(pi ⊗ₘ P) := by
    rw [withDensity_apply _ hS, Measure.lintegral_compProd hF']
    have hinner : ∀ x : Ω,
        ∫⁻ y, ENNReal.ofReal (g y) * Set.indicator S (fun _ => (1 : ℝ≥0∞)) x ∂(P x)
          = Set.indicator S (fun _ => (1 : ℝ≥0∞)) x * ∫⁻ y, ENNReal.ofReal (g y) ∂(P x) := by
      intro x
      rw [lintegral_mul_const' _ _ (by
        by_cases hx : x ∈ S <;> simp [hx]), mul_comm]
    rw [lintegral_congr hinner]
    rw [← lintegral_indicator hS]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    by_cases hxS : x ∈ S <;> simp [hxS, hx]
  rw [hL, hR]
  exact (lintegral_compProd_swap hrev hF).symm

/-- **`t` steps of the chain on densities.** -/
theorem iterate_withDensity_ofReal {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) {g : Ω → ℝ} (hg : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) (hgmem : MemLp g 2 pi) (t : ℕ) :
    iterate P (pi.withDensity fun x => ENNReal.ofReal (g x)) t
      = pi.withDensity fun x => ENNReal.ofReal (markovIter P g t x) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [iterate_succ, ih, markovIter_succ]
      exact step_withDensity_ofReal hrev (measurable_markovIter P hg t)
        (markovIter_nonneg P hg0 t)
        ((memLp_markovIter hrev.invariant hg hgmem t).integrable (by norm_num))

/-! ## `L²` ⟹ total variation

For a density `h` with `∫ h dpi = 1`, `|mu S − pi S| = |∫_S (h − 1) dpi| ≤ ∫ |h − 1| dpi`,
and Cauchy–Schwarz on the probability space `pi` bounds that by `‖h − 1‖_{L²(pi)}`, which is
`√(Var h)`.  This is the `χ²` → TV comparison, with no factor `1/2` claimed. -/

/-- **The `L¹` norm of a centred function is at most its `L²` norm** on a probability
space.  This is `Var |g| ≥ 0` in disguise. -/
theorem integral_abs_le_sqrt_integral_sq {pi : Measure Ω} [IsProbabilityMeasure pi]
    {g : Ω → ℝ} (hg : Measurable g) (hmem : MemLp g 2 pi) :
    ∫ x, |g x| ∂pi ≤ Real.sqrt (∫ x, g x ^ 2 ∂pi) := by
  have hgabs : Measurable fun x => |g x| := _root_.continuous_abs.measurable.comp hg
  have hamem : MemLp (fun x => |g x|) 2 pi :=
    hmem.of_le hgabs.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simp)
  have hvar : 0 ≤ ProbabilityTheory.variance (fun x => |g x|) pi :=
    ProbabilityTheory.variance_nonneg _ _
  rw [ProbabilityTheory.variance_eq_sub hamem] at hvar
  simp only [Pi.pow_apply] at hvar
  have hsq : ∫ x, |g x| ^ 2 ∂pi = ∫ x, g x ^ 2 ∂pi :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => sq_abs _)
  rw [hsq] at hvar
  have h0 : 0 ≤ ∫ x, |g x| ∂pi := integral_nonneg fun _ => abs_nonneg _
  have := Real.sqrt_le_sqrt (by linarith : (∫ x, |g x| ∂pi) ^ 2 ≤ ∫ x, g x ^ 2 ∂pi)
  rwa [Real.sqrt_sq h0] at this

/-- **The `χ²`/`L²` → TV comparison.**  A law with density `h` against `pi` is within total
variation distance `√(Var_pi h)` of `pi`.

No Markov chain appears: this is a statement about two measures and a density. -/
theorem tvLe_withDensity {pi : Measure Ω} [IsProbabilityMeasure pi] {h : Ω → ℝ}
    (hmeas : Measurable h) (hnn : ∀ x, 0 ≤ h x) (hmem : MemLp h 2 pi)
    (hmean : ∫ x, h x ∂pi = 1) :
    TVLe (pi.withDensity fun x => ENNReal.ofReal (h x)) pi
      (ENNReal.ofReal (Real.sqrt (varianceReal pi h))) := by
  have hint : Integrable h pi := hmem.integrable (by norm_num)
  have hdmeas : Measurable fun x => h x - 1 := hmeas.sub measurable_const
  have hdmem : MemLp (fun x => h x - 1) 2 pi := hmem.sub (memLp_const 1)
  have hdint : Integrable (fun x => h x - 1) pi := hint.sub (integrable_const 1)
  have hdmean : ∫ x, (h x - 1) ∂pi = 0 := by
    rw [integral_sub hint (integrable_const 1), integral_const, hmean]
    simp
  have hdvar : ∫ x, (h x - 1) ^ 2 ∂pi = varianceReal pi h := by
    have h1 : varianceReal pi (fun x => h x - 1) = ∫ x, (h x - 1) ^ 2 ∂pi := by
      rw [varianceReal_eq_sub hdmem, hdmean]; ring
    have h2 : varianceReal pi (fun x => h x - 1) = varianceReal pi h :=
      ProbabilityTheory.variance_sub_const hmem.aestronglyMeasurable 1
    linarith
  set D : ℝ := Real.sqrt (varianceReal pi h) with hD
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have habs : ∫ x, |h x - 1| ∂pi ≤ D := by
    rw [hD, ← hdvar]
    exact integral_abs_le_sqrt_integral_sq hdmeas hdmem
  -- the two measures
  have hmuuniv : (pi.withDensity fun x => ENNReal.ofReal (h x)) Set.univ = 1 := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn), hmean]
    simp
  haveI : IsProbabilityMeasure (pi.withDensity fun x => ENNReal.ofReal (h x)) := ⟨hmuuniv⟩
  refine tvLe_of_forall_le fun S hS => ?_
  have hmuS : (pi.withDensity fun x => ENNReal.ofReal (h x)) S
      = ENNReal.ofReal (∫ x in S, h x ∂pi) := by
    rw [withDensity_apply _ hS,
      ← ofReal_integral_eq_lintegral_ofReal hint.restrict (Filter.Eventually.of_forall hnn)]
  have hpiS : pi S = ENNReal.ofReal (∫ _x in S, (1 : ℝ) ∂pi) := by
    rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top pi S)]
  have hkey : ∫ x in S, h x ∂pi ≤ (∫ _x in S, (1 : ℝ) ∂pi) + D := by
    have hsplit : ∫ x in S, h x ∂pi
        = (∫ x in S, (h x - 1) ∂pi) + ∫ _x in S, (1 : ℝ) ∂pi := by
      rw [← integral_add hdint.restrict (integrable_const 1)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    have h1 : ∫ x in S, (h x - 1) ∂pi ≤ ∫ x in S, |h x - 1| ∂pi :=
      integral_mono hdint.restrict (hdint.abs.restrict) fun x => le_abs_self _
    have h2 : ∫ x in S, |h x - 1| ∂pi ≤ ∫ x, |h x - 1| ∂pi :=
      setIntegral_le_integral hdint.abs (Filter.Eventually.of_forall fun x => abs_nonneg _)
    rw [hsplit]
    linarith
  rw [hmuS, hpiS, ← ENNReal.ofReal_add (integral_nonneg fun _ => zero_le_one) hD0]
  exact ENNReal.ofReal_le_ofReal hkey

/-! ## The spectral gap of a chain with nonnegative spectrum is at most `1`

Needed so that `1 − gap ≥ 0` and `|1 − gap| = 1 − gap`.  It is a genuine consequence of
`HasNonnegSpectrum`, not an extra assumption: without it, `spectralGap` can be as large as
`2` (the deterministic two-cycle). -/

/-- Every Rayleigh quotient of a chain with nonnegative spectrum is at most `1`. -/
theorem rayleighQuotient_le_one {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) (hpsd : HasNonnegSpectrum P pi)
    {f : Ω → ℝ} (hf : Measurable f) (hmem : MemLp f 2 pi) (hv : varianceReal pi f ≠ 0) :
    rayleighQuotient P pi f ≤ 1 := by
  set m : ℝ := ∫ x, f x ∂pi with hm
  set g : Ω → ℝ := fun x => f x - m with hgdef
  have hgmeas : Measurable g := hf.sub measurable_const
  have hgmem : MemLp g 2 pi := hmem.sub (memLp_const m)
  have hgmean : ∫ x, g x ∂pi = 0 := by
    rw [hgdef, integral_sub (hmem.integrable (by norm_num)) (integrable_const m), integral_const]
    simp [← hm]
  have hgvar : varianceReal pi g = varianceReal pi f :=
    ProbabilityTheory.variance_sub_const hmem.aestronglyMeasurable m
  have hgsq : ∫ x, g x ^ 2 ∂pi = varianceReal pi f := by
    rw [← hgvar, varianceReal_eq_sub hgmem, hgmean]; ring
  have hfg : (fun x => g x + m) = f := by funext x; simp [hgdef]
  have hE : dirichletFormReal P pi f = dirichletFormReal P pi g := by
    rw [← hfg]; exact dirichletFormReal_add_const P pi g m
  have hEg : dirichletFormReal P pi g = (∫ x, g x ^ 2 ∂pi) - pairing P pi g g :=
    dirichletFormReal_eq_sub_pairing hrev hgmeas hgmem
  have hp0 : 0 ≤ pairing P pi g g := hpsd g hgmeas hgmem
  have hvpos : 0 < varianceReal pi f :=
    lt_of_le_of_ne (varianceReal_nonneg pi f) (Ne.symm hv)
  rw [rayleighQuotient, hE, hEg, hgsq, div_le_one hvpos]
  linarith

/-- **`gap ≤ 1` for a chain with nonnegative spectrum.** -/
theorem spectralGap_le_one {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) (hpsd : HasNonnegSpectrum P pi)
    (hne : (rayleighSet P pi).Nonempty) : spectralGap P pi ≤ 1 := by
  obtain ⟨r, f, ⟨hmem, hv⟩, rfl⟩ := hne
  set f' : Ω → ℝ := hmem.aestronglyMeasurable.mk f with hf'def
  have hff' : f =ᵐ[pi] f' := hmem.aestronglyMeasurable.ae_eq_mk
  have hf'meas : Measurable f' := hmem.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hf'mem : MemLp f' 2 pi := MemLp.ae_eq hff' hmem
  have hf'v : varianceReal pi f' ≠ 0 := by
    rwa [varianceReal, ← ProbabilityTheory.variance_congr hff']
  calc spectralGap P pi ≤ rayleighQuotient P pi f' :=
        spectralGap_le_rayleighQuotient P pi hf'mem hf'v
    _ ≤ 1 := rayleighQuotient_le_one hrev hpsd hf'meas hf'mem hf'v

/-! ## Assembling: `d_TV(mu_t, pi) ≤ √M (1 − gap)^t` -/

/-- **The mixing bound from a density.**  Started from `h · pi`, the chain is within total
variation `√(Var h) · |1 − gap|^t` of `pi` at time `t`. -/
theorem tvLe_iterate_withDensity {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) (hpsd : HasNonnegSpectrum P pi)
    {h : Ω → ℝ} (hmeas : Measurable h) (hnn : ∀ x, 0 ≤ h x) (hmem : MemLp h 2 pi)
    (hmean : ∫ x, h x ∂pi = 1) (t : ℕ) :
    TVLe (iterate P (pi.withDensity fun x => ENNReal.ofReal (h x)) t) pi
      (ENNReal.ofReal (Real.sqrt (varianceReal pi h) * |1 - spectralGap P pi| ^ t)) := by
  rw [iterate_withDensity_ofReal hrev hmeas hnn hmem t]
  refine TVLe.mono (tvLe_withDensity (measurable_markovIter P hmeas t)
    (markovIter_nonneg P hnn t) (memLp_markovIter hrev.invariant hmeas hmem t) ?_)
    (ENNReal.ofReal_le_ofReal ?_)
  · rw [integral_markovIter hrev hmeas hmem t]; exact hmean
  · have hv := varianceReal_markovIter_le hrev hpsd hmeas hmem t
    calc Real.sqrt (varianceReal pi (markovIter P h t))
        ≤ Real.sqrt (((1 - spectralGap P pi) ^ 2) ^ t * varianceReal pi h) :=
          Real.sqrt_le_sqrt hv
      _ = Real.sqrt (((1 - spectralGap P pi) ^ t) ^ 2) * Real.sqrt (varianceReal pi h) := by
          rw [← Real.sqrt_mul (by positivity)]
          congr 1
          rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 t]
      _ = Real.sqrt (varianceReal pi h) * |1 - spectralGap P pi| ^ t := by
          rw [Real.sqrt_sq_eq_abs, abs_pow, mul_comm]

/-- **The mixing bound from an `M`-warm start**, `d_TV ≤ √M |1 − gap|^t`.

The density of `mu0` against `pi` is its Radon–Nikodym derivative, which exists because
warmness gives `mu0 ≪ pi`; its second moment is at most `M` because
`∫ h² dpi = ∫ h dmu0 ≤ M ∫ h dpi = M`. -/
theorem tvLe_iterate_of_isWarm {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) (hpsd : HasNonnegSpectrum P pi)
    {mu0 : Measure Ω} [IsProbabilityMeasure mu0] {M : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 pi) (t : ℕ) :
    TVLe (iterate P mu0 t) pi
      (ENNReal.ofReal (Real.sqrt M * |1 - spectralGap P pi| ^ t)) := by
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM
  have hle : mu0 ≤ ENNReal.ofReal M • pi := (isWarm_iff_le_smul _ _).1 hwarm
  have hac : mu0 ≪ pi := by
    refine Measure.AbsolutelyContinuous.mk fun S hS hS0 => ?_
    have h := hwarm S hS
    rw [hS0, mul_zero] at h
    exact nonpos_iff_eq_zero.mp h
  set r : Ω → ℝ≥0∞ := mu0.rnDeriv pi with hrdef
  have hrmeas : Measurable r := Measure.measurable_rnDeriv mu0 pi
  have hrlt : ∀ᵐ x ∂pi, r x < ⊤ := Measure.rnDeriv_lt_top mu0 pi
  set h0 : Ω → ℝ := fun x => (r x).toReal with hh0def
  have hh0meas : Measurable h0 := hrmeas.ennreal_toReal
  have hh0nn : ∀ x, 0 ≤ h0 x := fun _ => ENNReal.toReal_nonneg
  have hofReal : (fun x => ENNReal.ofReal (h0 x)) =ᵐ[pi] r := by
    filter_upwards [hrlt] with x hx
    exact ENNReal.ofReal_toReal hx.ne
  have hmu0 : pi.withDensity (fun x => ENNReal.ofReal (h0 x)) = mu0 := by
    rw [withDensity_congr_ae hofReal]
    exact Measure.withDensity_rnDeriv_eq mu0 pi hac
  have hint1 : ∫⁻ x, r x ∂pi = 1 := by
    have h1 : (pi.withDensity r) Set.univ = 1 := by
      rw [Measure.withDensity_rnDeriv_eq mu0 pi hac]; exact measure_univ
    rwa [withDensity_apply r MeasurableSet.univ, Measure.restrict_univ] at h1
  have hmean : ∫ x, h0 x ∂pi = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hh0nn)
      hh0meas.aestronglyMeasurable, lintegral_congr_ae hofReal, hint1]
    simp
  have hsq_ae : (fun x => ENNReal.ofReal (h0 x ^ 2)) =ᵐ[pi] fun x => r x * r x := by
    filter_upwards [hrlt] with x hx
    rw [pow_two, ENNReal.ofReal_mul (hh0nn x), hh0def, ENNReal.ofReal_toReal hx.ne]
  have hbound : ∫⁻ x, ENNReal.ofReal (h0 x ^ 2) ∂pi ≤ ENNReal.ofReal M := by
    rw [lintegral_congr_ae hsq_ae]
    have h1 : ∫⁻ x, r x ∂(pi.withDensity r) = ∫⁻ x, r x * r x ∂pi := by
      rw [lintegral_withDensity_eq_lintegral_mul pi hrmeas hrmeas]
      rfl
    rw [← h1, Measure.withDensity_rnDeriv_eq mu0 pi hac]
    calc ∫⁻ x, r x ∂mu0 ≤ ∫⁻ x, r x ∂(ENNReal.ofReal M • pi) := lintegral_mono' hle le_rfl
      _ = ENNReal.ofReal M * ∫⁻ x, r x ∂pi := lintegral_smul_measure _ _
      _ = ENNReal.ofReal M := by rw [hint1, mul_one]
  have hh0mem : MemLp h0 2 pi := by
    refine (memLp_two_iff_integrable_sq hh0meas.aestronglyMeasurable).2 ?_
    refine ⟨(hh0meas.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => sq_nonneg _)]
    exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  have hvar : varianceReal pi h0 ≤ M := by
    have hsqint : ∫ x, h0 x ^ 2 ∂pi ≤ M := by
      rw [integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun x => sq_nonneg (h0 x))
        ((hh0meas.pow_const 2).aestronglyMeasurable)]
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
      rwa [ENNReal.toReal_ofReal hM0.le] at h
    rw [varianceReal_eq_sub hh0mem, hmean]
    linarith
  rw [← hmu0]
  refine TVLe.mono (tvLe_iterate_withDensity hrev hpsd hh0meas hh0nn hh0mem hmean t)
    (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hvar) (by positivity)

/-- **The Lovász–Simonovits decay bound.**  For a reversible chain with nonnegative spectrum
and conductance at least `phi`, started from an `M`-warm law,

`d_TV(mu_s, pi) ≤ √M (1 − phi²/2)^s`.

This is exactly the `hdecay` hypothesis of
`Arlib.MarkovChains.mixesWithin_of_conductance_decay`, discharged.  Its ingredients are
Cheeger's inequality (`sq_conductance_div_two_le_spectralGap`, from
`Arlib.MarkovChains.Continuous.Cheeger`), the `L²` contraction
`varianceReal_markovIter_le`, and the `χ²` → TV comparison `tvLe_withDensity`. -/
theorem tvLe_iterate_of_conductance {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) (hpsd : HasNonnegSpectrum P pi)
    (hne : (rayleighSet P pi).Nonempty) {mu0 : Measure Ω} [IsProbabilityMeasure mu0]
    {M phi : ℝ} (hM : 1 ≤ M) (hwarm : IsWarm (ENNReal.ofReal M) mu0 pi) (hphi0 : 0 < phi)
    (hphi : phi ≤ (conductance P pi).toReal) (s : ℕ) :
    TVLe (iterate P mu0 s) pi (ENNReal.ofReal (Real.sqrt M * (1 - phi ^ 2 / 2) ^ s)) := by
  refine TVLe.mono (tvLe_iterate_of_isWarm hrev hpsd hM hwarm s)
    (ENNReal.ofReal_le_ofReal ?_)
  have hgap1 : spectralGap P pi ≤ 1 := spectralGap_le_one hrev hpsd hne
  have hcheeger : (conductance P pi).toReal ^ 2 / 2 ≤ spectralGap P pi :=
    sq_conductance_div_two_le_spectralGap hrev hne
  have hphigap : phi ^ 2 / 2 ≤ spectralGap P pi := by nlinarith
  have h2 : (0 : ℝ) ≤ 1 - spectralGap P pi := by linarith
  have h1 : 1 - spectralGap P pi ≤ 1 - phi ^ 2 / 2 := by linarith
  rw [abs_of_nonneg h2]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg M)
  gcongr

/-- **The acceptance test.**  `Arlib.MarkovChains.mixesWithin_of_conductance_decay` with its
`hdecay` obligation discharged: `O(phi⁻² log(M/eps))` steps of a reversible chain with
nonnegative spectrum, conductance at least `phi` and an `M`-warm start bring the law within
total variation `eps` of `pi`. -/
theorem mixesWithin_of_conductance {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) (hpsd : HasNonnegSpectrum P pi)
    (hne : (rayleighSet P pi).Nonempty) {mu0 : Measure Ω} [IsProbabilityMeasure mu0]
    {M phi eps : ℝ} (hM : 1 ≤ M) (hwarm : IsWarm (ENNReal.ofReal M) mu0 pi) (hphi0 : 0 < phi)
    (hphi1 : phi ≤ 1) (heps : 0 < eps) (hphi : phi ≤ (conductance P pi).toReal) {t : ℕ}
    (ht : conductanceMixingTime M phi eps ≤ t) :
    MixesWithin P pi mu0 t (ENNReal.ofReal eps) :=
  mixesWithin_of_conductance_decay hM hphi0 hphi1 heps
    (fun s => tvLe_iterate_of_conductance hrev hpsd hne hM hwarm hphi0 hphi s) ht

/-- The same decay bound with the conductance hypothesis in its `ℝ≥0∞` form, which is how a
conductance theorem states it.  `hc` is not restrictive: `conductance = ⊤` only on a space
with no measurable set of measure in `(0, 1/2]`. -/
theorem tvLe_iterate_of_ofReal_le_conductance {P : Kernel Ω Ω} [IsMarkovKernel P]
    {pi : Measure Ω} [IsProbabilityMeasure pi] (hrev : IsReversible P pi)
    (hpsd : HasNonnegSpectrum P pi) (hne : (rayleighSet P pi).Nonempty) {mu0 : Measure Ω}
    [IsProbabilityMeasure mu0] {M phi : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 pi) (hphi0 : 0 < phi)
    (hc : conductance P pi ≠ ⊤) (hphi : ENNReal.ofReal phi ≤ conductance P pi) (s : ℕ) :
    TVLe (iterate P mu0 s) pi (ENNReal.ofReal (Real.sqrt M * (1 - phi ^ 2 / 2) ^ s)) := by
  refine tvLe_iterate_of_conductance hrev hpsd hne hM hwarm hphi0 ?_ s
  have h := ENNReal.toReal_mono hc hphi
  rwa [ENNReal.toReal_ofReal hphi0.le] at h

/-! ## Non-vacuity (`CLAUDE.md` §11)

`HasNonnegSpectrum` is a hypothesis of every theorem above, so it must be inhabited.  The
instantly mixing kernel satisfies it: `⟪f, f⟫ = (∫ f dpi)² ≥ 0`. -/

/-- **The instantly mixing kernel has nonnegative spectrum.** -/
theorem hasNonnegSpectrum_const (pi : Measure Ω) [IsProbabilityMeasure pi] :
    HasNonnegSpectrum (Kernel.const Ω pi) pi := by
  intro f hf hmem
  have hint : Integrable (fun p : Ω × Ω => f p.1 * f p.2) (pi ⊗ₘ Kernel.const Ω pi) :=
    integrable_mul_compProd (isReversible_const pi) hf hf hmem hmem
  rw [pairing_eq_integral_mul_markovOp hint]
  have hconst : ∀ x : Ω, markovOp (Kernel.const Ω pi) f x = ∫ y, f y ∂pi := fun _ => rfl
  simp only [hconst]
  rw [integral_mul_const]
  exact mul_self_nonneg _

/-- **Non-vacuity witness.**  The uniform resampler on `Bool` is reversible, has nonnegative
spectrum, a non-empty admissible family and conductance `1/2`; so every hypothesis of
`mixesWithin_of_conductance` is simultaneously satisfiable. -/
theorem exists_hasNonnegSpectrum_and_conductance :
    ∃ (Om : Type) (_ : MeasurableSpace Om) (P : Kernel Om Om) (pi : Measure Om),
      IsMarkovKernel P ∧ IsProbabilityMeasure pi ∧ IsReversible P pi ∧
        HasNonnegSpectrum P pi ∧ (rayleighSet P pi).Nonempty ∧
        conductance P pi = 1 / 2 ∧ spectralGap P pi = 1 :=
  ⟨Bool, inferInstance, Kernel.const Bool piHalf, piHalf, inferInstance, inferInstance,
    isReversible_const piHalf, hasNonnegSpectrum_const piHalf,
    rayleighSet_const_piHalf_nonempty, conductance_const_piHalf, spectralGap_const_piHalf⟩

end Arlib.MarkovChains
