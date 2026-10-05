/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Lattice.Rounding.KernelIntegral
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Lattice.KV97.Escape

/-!
# The continuous tent law on `ℝⁿ` and the escape bound it satisfies

Kannan–Vempala, *Sampling Lattice Points* (STOC '97), phrase the proof of their
Theorem 2 in terms of i.i.d. real random variables `Y₁, …, Yₙ`, each with the
triangular ("tent") density `1 − |t|` on `[−1,1]`:

> Define `{Yᵢ}` to be i.i.d. real random variables each distributed according to
> the density `1 − |t|` on `[−1,1]`. Then for any lattice point `z` and any `p`,
> `density(z + Y = p) = ∏ᵢ (1 − |pᵢ − zᵢ|)`.

`Arlib.Lattice.Rounding.RoundLaw` builds the *lattice-variable* reading of the
same kernel (a two-point law on `ℤ` per coordinate) and
`Arlib.Lattice.Rounding.ProdKernel` builds the *continuous-variable* density
`Arlib.Lattice.Rounding.prodTent`. This file builds the **continuous law itself**:

* `Arlib.Lattice.Rounding.tentReal` — Lebesgue measure on `ℝ` weighted by `tent`;
* `Arlib.Lattice.Rounding.tentPi n` — its `n`-fold product on `Fin n → ℝ`, the law
  of the vector `Y` above.

It then discharges every hypothesis of `Arlib.KV97.escape_prob_le` for `tentPi n`
(measurability, coordinatewise independence, `[−1,1]`-support, mean zero), giving
the continuous escape bound `Arlib.Lattice.Rounding.tentPi_escape_prob_le`.

Finally — and this is what the rest of Theorem 2 consumes — it identifies the law
of `x + Y` with the density `prodTent x`:

  `∫ p in T, prodTent x p = (tentPi n).real {u | x + contDispVec u ∈ T}`

(`Arlib.Lattice.Rounding.setIntegral_prodTent_eq_tentPi_real`), and hence bounds
the **escape mass** of the kernel outside the inflated polytope,

  `∫ p in (Polytope.inflate A b κ)ᶜ, prodTent x p ≤ r · exp(−κ²/2)`

(`Arlib.Lattice.Rounding.setIntegral_prodTent_compl_inflate_le`).

## The bridge between `Measure.pi` and `withDensity`

The one genuinely technical step is
`Arlib.Lattice.Rounding.tentPi_eq_withDensity`:

  `tentPi n = (volume : Measure (Fin n → ℝ)).withDensity (fun u => ofReal (∏ i, tent (u i)))`.

Mathlib has no Fubini theorem for `∫⁻` over a finite product of measures, so the
product formula is routed through the Bochner one
(`MeasureTheory.integral_fintype_prod_eq_prod`) using nonnegativity and
integrability of the tent — see
`Arlib.Lattice.Rounding.lintegral_pi_prod_indicator_tent`.
-/

namespace Arlib.Lattice.Rounding

open MeasureTheory ProbabilityTheory

/-! ## The one-dimensional continuous tent law -/

/-- **The tent law on `ℝ`**: Lebesgue measure weighted by the triangular density
`tent u = max (1 − |u|) 0`. This is the law of a single `Yᵢ` in Kannan–Vempala's
proof of Theorem 2. -/
noncomputable def tentReal : Measure ℝ :=
  volume.withDensity fun u => ENNReal.ofReal (tent u)

/-- The tent's `∫⁻` mass is `1` — the `ℝ≥0∞` form of
`Arlib.Lattice.Rounding.integral_tent`, obtained through
`MeasureTheory.ofReal_integral_eq_lintegral_ofReal`. -/
theorem lintegral_ofReal_tent : ∫⁻ u, ENNReal.ofReal (tent u) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal integrable_tent
    (Filter.Eventually.of_forall tent_nonneg), integral_tent, ENNReal.ofReal_one]

/-- `Arlib.Lattice.Rounding.tentReal` is a probability measure. -/
instance isProbabilityMeasure_tentReal : IsProbabilityMeasure tentReal := by
  constructor
  rw [tentReal, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_ofReal_tent]

/-- `Arlib.Lattice.Rounding.tentReal` of a measurable set is the tent's integral
over it. -/
theorem tentReal_apply {s : Set ℝ} (hs : MeasurableSet s) :
    tentReal s = ENNReal.ofReal (∫ u in s, tent u) := by
  rw [tentReal, withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal integrable_tent.integrableOn
      (Filter.Eventually.of_forall tent_nonneg)]

/-- **Mean zero.** The identity has mean zero under the tent law: unfolding
`withDensity` turns `∫ u ∂tentReal` into `∫ u · tent u`, which is `0` by symmetry
(`Arlib.Lattice.Rounding.integral_id_mul_tent`). -/
theorem integral_id_tentReal : ∫ u, u ∂tentReal = 0 := by
  rw [tentReal, integral_withDensity_eq_integral_toReal_smul
    (continuous_tent.measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall fun u => ENNReal.ofReal_lt_top)]
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (tent_nonneg _)]
  rw [← integral_id_mul_tent]
  exact integral_congr_ae (Filter.Eventually.of_forall fun u => mul_comm _ _)

/-- **Support.** The tent law is supported in `[−1,1]`: the density vanishes
outside (`Arlib.Lattice.Rounding.tent_eq_zero_of_notMem`), so the complement is
null. -/
theorem ae_tentReal_mem_Icc : ∀ᵐ u ∂tentReal, u ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [ae_iff]
  have hmeas : MeasurableSet {u : ℝ | u ∉ Set.Icc (-1 : ℝ) 1} :=
    (measurableSet_Icc (a := (-1 : ℝ)) (b := 1)).compl
  rw [tentReal, withDensity_apply _ hmeas]
  refine setLIntegral_eq_zero hmeas fun u hu => ?_
  simp only [Set.mem_setOf_eq] at hu
  simp [tent_eq_zero_of_notMem hu]

/-! ## The `n`-fold product: the law of the vector `Y`

`tentPi n` is a `MeasureTheory.Measure.pi`, so each of the three facts above
transfers coordinatewise exactly as in `Arlib.Lattice.Rounding.RoundLaw`: the
marginals are `tentReal` (via `MeasureTheory.measurePreserving_eval`), and
independence is `ProbabilityTheory.iIndepFun_pi`.
-/

variable {n : ℕ}

/-- **The continuous tent law on `ℝⁿ`**: `n` i.i.d. coordinates, each with the
triangular density `1 − |t|` on `[−1,1]`. This is the law of Kannan–Vempala's
vector `Y = (Y₁, …, Yₙ)`. -/
noncomputable def tentPi (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ => tentReal

/-- The `n`-dimensional tent law is a probability measure. -/
instance isProbabilityMeasure_tentPi (n : ℕ) : IsProbabilityMeasure (tentPi n) := by
  rw [tentPi]; infer_instance

/-- The `k`-th marginal of `tentPi n` is the one-dimensional law `tentReal`. -/
theorem measurePreserving_tentPi_eval (k : Fin n) :
    MeasurePreserving (Function.eval k) (tentPi n) tentReal :=
  measurePreserving_eval (fun _ => tentReal) k

/-- Coordinate projection on `Fin n → ℝ` is measurable — the `hmeas` hypothesis of
`Arlib.KV97.escape_prob_le`. -/
theorem measurable_tentPi_coord (k : Fin n) : Measurable fun u : Fin n → ℝ => u k :=
  measurable_pi_apply k

/-- **Independence across coordinates.** The coordinates of the tent vector are
independent — immediate, since `tentPi` is a product measure. Stated with an
arbitrary coefficient vector `a`, the form the sub-Gaussian tail bounds consume
(compare `Arlib.Lattice.Rounding.iIndepFun_latDisp`, the discrete analogue). -/
theorem iIndepFun_tentPi (a : Fin n → ℝ) :
    iIndepFun (fun (k : Fin n) (u : Fin n → ℝ) => a k * u k) (tentPi n) :=
  iIndepFun_pi (μ := fun _ : Fin n => tentReal) (X := fun i (t : ℝ) => a i * t)
    fun _ => (measurable_const.mul measurable_id).aemeasurable

/-- **Support, coordinatewise.** Each coordinate of the tent vector lies in
`[−1,1]` almost surely — the `hbdd` hypothesis of `Arlib.KV97.escape_prob_le`. -/
theorem ae_tentPi_mem_Icc (k : Fin n) :
    ∀ᵐ u ∂(tentPi n), u k ∈ Set.Icc (-1 : ℝ) 1 := by
  have h := ae_tentReal_mem_Icc
  rw [ae_iff] at h ⊢
  have hpre : {u : Fin n → ℝ | ¬ (u k ∈ Set.Icc (-1 : ℝ) 1)}
      = Function.eval k ⁻¹' {t : ℝ | ¬ (t ∈ Set.Icc (-1 : ℝ) 1)} := rfl
  have hns : NullMeasurableSet {t : ℝ | t ∉ Set.Icc (-1 : ℝ) 1} tentReal :=
    (measurableSet_Icc (a := (-1 : ℝ)) (b := 1)).compl.nullMeasurableSet
  rw [hpre, (measurePreserving_tentPi_eval k).measure_preimage hns]
  exact h

/-- **Mean zero, coordinatewise.** Each coordinate of the tent vector has mean
zero — the `hmean` hypothesis of `Arlib.KV97.escape_prob_le`. -/
theorem integral_tentPi_coord_eq_zero (k : Fin n) :
    ∫ u, u k ∂(tentPi n) = 0 := by
  rw [tentPi, MeasureTheory.integral_comp_eval (μ := fun _ : Fin n => tentReal) (i := k)
    (f := fun t : ℝ => t) aestronglyMeasurable_id]
  exact integral_id_tentReal

/-! ## The escape bound for the continuous law

Every hypothesis of `Arlib.KV97.escape_prob_le` is now available, so the
continuous instance is a one-liner. Compare `Arlib.KV97.roundLaw_escape_prob_le`,
the discrete instance built from `Arlib.Lattice.Rounding.roundLaw`.
-/

/-- The tent displacement read as a vector of `EuclideanSpace ℝ (Fin n)`, so that
it can be added to a point of an `Arlib.Polytope.body`. The continuous
counterpart of `Arlib.KV97.latDispVec`. -/
noncomputable def contDispVec (u : Fin n → ℝ) : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 u

@[simp]
theorem contDispVec_apply (u : Fin n → ℝ) (k : Fin n) : contDispVec u k = u k := rfl

variable {ι : Type*} [Fintype ι]

/-- **The escape bound under the continuous tent law.** For a point `x` of the
polytope `body A b` and a tent-distributed displacement `Y`, the point `x + Y`
leaves the `κ`-inflation with probability at most `r · exp(−κ²/2)`.

This is `Arlib.KV97.escape_prob_le` instantiated at `tentPi n`; its four
hypotheses are `Arlib.Lattice.Rounding.{measurable_tentPi_coord, iIndepFun_tentPi,
ae_tentPi_mem_Icc, integral_tentPi_coord_eq_zero}`. -/
theorem tentPi_escape_prob_le (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Polytope.body A b)
    {κ r : ℝ} (hκ : 0 ≤ κ) (hr : (Fintype.card ι : ℝ) ≤ r) :
    (tentPi n).real {u | x + contDispVec u ∉ Polytope.inflate A b κ}
      ≤ r * Real.exp (-κ ^ 2 / 2) :=
  KV97.escape_prob_le A b contDispVec
    (fun k => (measurable_tentPi_coord k).aemeasurable)
    (fun i => iIndepFun_tentPi fun k => A i k)
    ae_tentPi_mem_Icc integral_tentPi_coord_eq_zero hx hκ hr

/-- **The escape bound at `κ = Arlib.KV97.kappaOf c r`.** The `√(2 log r)` summand
absorbs the union-bound factor `r`, leaving `exp(−c²/2)` — the constant
`Arlib.Lattice.KV97.Escape` actually proves; see its step-5 section docstring for
why it is `exp(−c²/2)` and not `exp(−c²)`. -/
theorem tentPi_escape_prob_le_exp (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Polytope.body A b)
    {c r : ℝ} (hc : 0 ≤ c) (hr1 : 1 ≤ r) (hr : (Fintype.card ι : ℝ) ≤ r) :
    (tentPi n).real {u | x + contDispVec u ∉ Polytope.inflate A b (KV97.kappaOf c r)}
      ≤ Real.exp (-c ^ 2 / 2) :=
  le_trans (tentPi_escape_prob_le A b hx (KV97.kappaOf_nonneg hc) hr)
    (KV97.mul_exp_kappaOf_le hc hr1)

/-! ## The product law as a density against Lebesgue measure

Mathlib has no Fubini theorem for `∫⁻` over a finite product of measures, so the
identification of `tentPi n` with a `MeasureTheory.Measure.withDensity` is routed
through the Bochner statement `MeasureTheory.integral_fintype_prod_volume_eq_prod`,
using that every factor is nonnegative and integrable.
-/

/-- Fubini for `∫⁻` of a product of nonnegative integrable factors on `Fin n → ℝ`,
obtained from the Bochner version through
`MeasureTheory.ofReal_integral_eq_lintegral_ofReal`. -/
theorem lintegral_ofReal_pi_prod (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Integrable (f i) volume) (hnn : ∀ i t, 0 ≤ f i t) :
    ∫⁻ u : Fin n → ℝ, ENNReal.ofReal (∏ i, f i (u i))
      = ∏ i, ENNReal.ofReal (∫ t, f i t) := by
  have hint : Integrable (fun u : Fin n → ℝ => ∏ i, f i (u i)) volume :=
    Integrable.fintype_prod (μ := fun _ : Fin n => (volume : Measure ℝ)) hf
  have hnn' : ∀ u : Fin n → ℝ, 0 ≤ ∏ i, f i (u i) :=
    fun u => Finset.prod_nonneg fun i _ => hnn i _
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn'),
    integral_fintype_prod_volume_eq_prod (fun i (t : ℝ) => f i t),
    ENNReal.ofReal_prod_of_nonneg fun i _ => integral_nonneg (hnn i)]

/-- **The product tent law is the tent product density against Lebesgue measure.**

`tentPi n = volume.withDensity (fun u => ofReal (∏ i, tent (u i)))`.

This is Kannan–Vempala's sentence *"`{Yᵢ}` i.i.d. with density `1 − |t|`"* read as
a statement about the joint law: independence of the coordinates is the same thing
as the joint density factorizing. Proved by `MeasureTheory.Measure.pi_eq`: both
sides agree on every measurable box, by
`Arlib.Lattice.Rounding.lintegral_ofReal_pi_prod`. -/
theorem tentPi_eq_withDensity (n : ℕ) :
    tentPi n = (volume : Measure (Fin n → ℝ)).withDensity
      fun u => ENNReal.ofReal (∏ i, tent (u i)) := by
  rw [tentPi]
  refine Measure.pi_eq (μ := fun _ : Fin n => tentReal) fun s hs => ?_
  have hpt : ∀ u : Fin n → ℝ,
      (Set.univ.pi s).indicator (fun u : Fin n → ℝ => ENNReal.ofReal (∏ i, tent (u i))) u
        = ENNReal.ofReal (∏ i, (s i).indicator tent (u i)) := by
    intro u
    by_cases hu : u ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hu]
      exact congrArg ENNReal.ofReal
        (Finset.prod_congr rfl fun i _ =>
          (Set.indicator_of_mem (hu i (Set.mem_univ i)) tent).symm)
    · rw [Set.indicator_of_notMem hu]
      simp only [Set.mem_pi, Set.mem_univ, forall_const, not_forall] at hu
      obtain ⟨i, hi⟩ := hu
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi tent),
        ENNReal.ofReal_zero]
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator
    (MeasurableSet.univ_pi hs), lintegral_congr hpt,
    lintegral_ofReal_pi_prod (fun i => (s i).indicator tent)
      (fun i => integrable_tent.indicator (hs i))
      (fun i t => Set.indicator_nonneg (fun t _ => tent_nonneg t) t)]
  exact Finset.prod_congr rfl fun i _ => by
    rw [integral_indicator (hs i), ← tentReal_apply (hs i)]

/-- The tent product density is integrable on `Fin n → ℝ`. -/
theorem integrable_piTent (n : ℕ) :
    Integrable (fun u : Fin n → ℝ => ∏ i, tent (u i)) volume :=
  Integrable.fintype_prod (μ := fun _ : Fin n => (volume : Measure ℝ)) fun _ => integrable_tent

/-- The tent product density is nonnegative. -/
theorem piTent_nonneg (u : Fin n → ℝ) : 0 ≤ ∏ i, tent (u i) :=
  Finset.prod_nonneg fun _ _ => tent_nonneg _

/-- The mass `tentPi n` puts on a measurable set is the integral of the tent
product density over it. -/
theorem tentPi_apply {S : Set (Fin n → ℝ)} (hS : MeasurableSet S) :
    tentPi n S = ENNReal.ofReal (∫ u in S, ∏ i, tent (u i)) := by
  rw [tentPi_eq_withDensity, withDensity_apply _ hS,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_piTent n).integrableOn
      (Filter.Eventually.of_forall piTent_nonneg)]

/-- The real-valued form of `Arlib.Lattice.Rounding.tentPi_apply`. -/
theorem tentPi_real_apply {S : Set (Fin n → ℝ)} (hS : MeasurableSet S) :
    (tentPi n).real S = ∫ u in S, ∏ i, tent (u i) := by
  rw [measureReal_def, tentPi_apply hS,
    ENNReal.toReal_ofReal (integral_nonneg fun u => piTent_nonneg u)]

/-! ## The payoff: `prodTent x` is the density of `x + Y`

The change of variables `p = x + u` identifies the kernel's set integrals with
the tent law's probabilities. Composed with
`Arlib.Lattice.Rounding.tentPi_escape_prob_le` this bounds the **escape mass** of
the rounding kernel outside the inflated polytope — the quantity Theorem 2 has to
control.
-/

/-- **`prodTent x` is the density of `x + Y`.**

`∫ p in T, prodTent x p = Pr[x + Y ∈ T]` for every measurable `T`, where `Y` has
the product tent law `tentPi n`. This is Kannan–Vempala's
*"`density(z + Y = p) = ∏ᵢ (1 − |pᵢ − zᵢ|)`"*, in integrated form.

The proof is two applications of
`MeasureTheory.MeasurePreserving.setIntegral_preimage_emb`: first along the
volume-preserving identification `WithLp.toLp 2 : (Fin n → ℝ) ≃ EuclideanSpace ℝ (Fin n)`,
then along the translation `u ↦ u + x`, which Lebesgue measure is invariant
under. What is left is `Arlib.Lattice.Rounding.tentPi_real_apply`. -/
theorem setIntegral_prodTent_eq_tentPi_real (x : EuclideanSpace ℝ (Fin n))
    {T : Set (EuclideanSpace ℝ (Fin n))} (hT : MeasurableSet T) :
    ∫ p in T, prodTent x p = (tentPi n).real {u : Fin n → ℝ | x + contDispVec u ∈ T} := by
  have hmeasadd : Measurable fun u : Fin n → ℝ => x + contDispVec u :=
    measurable_const.add (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable
  have hSmeas : MeasurableSet {u : Fin n → ℝ | x + contDispVec u ∈ T} := hmeasadd hT
  have hset : (fun v : Fin n → ℝ => v + WithLp.ofLp x) ⁻¹' (WithLp.toLp 2 ⁻¹' T)
      = {u : Fin n → ℝ | x + contDispVec u ∈ T} := by
    ext u
    simp only [Set.mem_preimage, Set.mem_setOf_eq, contDispVec]
    rw [WithLp.toLp_add, WithLp.toLp_ofLp, add_comm]
  have hfun : ∀ u : Fin n → ℝ,
      prodTent x (WithLp.toLp 2 (u + WithLp.ofLp x)) = ∏ i, tent (u i) := by
    intro u
    rw [prodTent]
    refine Finset.prod_congr rfl fun i _ => congrArg tent ?_
    show u i + x i - x i = u i
    ring
  have h1 : ∫ u in (WithLp.toLp 2 ⁻¹' T), prodTent x (WithLp.toLp 2 u)
      = ∫ p in T, prodTent x p :=
    (PiLp.volume_preserving_toLp (Fin n)).setIntegral_preimage_emb
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding (prodTent x) T
  have h2 : ∫ u in ((fun v : Fin n → ℝ => v + WithLp.ofLp x) ⁻¹' (WithLp.toLp 2 ⁻¹' T)),
        prodTent x (WithLp.toLp 2 (u + WithLp.ofLp x))
      = ∫ u in (WithLp.toLp 2 ⁻¹' T), prodTent x (WithLp.toLp 2 u) :=
    (measurePreserving_add_right (volume : Measure (Fin n → ℝ))
        (WithLp.ofLp x)).setIntegral_preimage_emb
      (MeasurableEquiv.addRight (WithLp.ofLp x)).measurableEmbedding
      (fun u => prodTent x (WithLp.toLp 2 u)) (WithLp.toLp 2 ⁻¹' T)
  rw [tentPi_real_apply hSmeas, ← h1, ← h2, hset]
  exact setIntegral_congr_fun hSmeas fun u _ => hfun u

/-- **The escape mass of the rounding kernel — Kannan–Vempala Theorem 2's error
term, unconditionally.**

For `x` in the polytope `body A b`,

  `∫ p in (inflate A b κ)ᶜ, prodTent x p ≤ r · exp(−κ²/2)`,

`r` bounding the number of facets. Combined with
`Arlib.Lattice.Rounding.setIntegral_prodTent_compl` — which says the mass the
kernel puts on `inflate A b κ` is `1` minus this escape mass — it is exactly the
lower bound `Pr[rnd p = x] ≥ (1 − r·exp(−κ²/2)) / Vol(P')`.

Proof: `Arlib.Lattice.Rounding.setIntegral_prodTent_eq_tentPi_real` turns the set
integral into the probability that `x + Y` escapes the inflation, and
`Arlib.Lattice.Rounding.tentPi_escape_prob_le` bounds that. -/
theorem setIntegral_prodTent_compl_inflate_le (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Polytope.body A b)
    {κ r : ℝ} (hκ : 0 ≤ κ) (hr : (Fintype.card ι : ℝ) ≤ r) :
    ∫ p in (Polytope.inflate A b κ)ᶜ, prodTent x p ≤ r * Real.exp (-κ ^ 2 / 2) := by
  rw [setIntegral_prodTent_eq_tentPi_real x (Polytope.measurableSet_inflate A b κ).compl]
  exact tentPi_escape_prob_le A b hx hκ hr

/-- **The escape mass at `κ = Arlib.KV97.kappaOf c r`.** The union-bound factor
`r` is absorbed by the `√(2 log r)` summand, leaving

  `∫ p in (inflate A b (kappaOf c r))ᶜ, prodTent x p ≤ exp(−c²/2)`.

This is the form Theorem 2 consumes; the constant is `exp(−c²/2)`, see the
step-5 section docstring of `Arlib.Lattice.KV97.Escape`. -/
theorem setIntegral_prodTent_compl_inflate_le_exp (A : ι → EuclideanSpace ℝ (Fin n))
    (b : ι → ℝ) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Polytope.body A b)
    {c r : ℝ} (hc : 0 ≤ c) (hr1 : 1 ≤ r) (hr : (Fintype.card ι : ℝ) ≤ r) :
    ∫ p in (Polytope.inflate A b (KV97.kappaOf c r))ᶜ, prodTent x p ≤ Real.exp (-c ^ 2 / 2) :=
  le_trans (setIntegral_prodTent_compl_inflate_le A b hx (KV97.kappaOf_nonneg hc) hr)
    (KV97.mul_exp_kappaOf_le hc hr1)

end Arlib.Lattice.Rounding
