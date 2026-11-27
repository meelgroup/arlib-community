/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.TapeProgram
import ArlibCommunity.Algorithms.CV18.Analysis.ProgramSemantics
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofKernelBridge

/-!
# Random points from the random numbers of the tape

The program of `Model/Program.lean` draws its two kinds of random point from the random
numbers of the tape:

* a ball-walk proposal around `x` of radius `r > 0` is `x + r · u`, for `u` a uniform
  point of the closed unit ball: it has the law `uniformBall n x r`
  (`uniformBall_eq_map`);
* the starting point is `√σ₀² · g`, for `g` a standard Gaussian vector: it has the law
  `initialGaussianLaw q` (`initialGaussianLaw_eq_map`).

`Refines p p'` says that `p'` is `p` with some point draws `μ` replaced by a draw from
`ν` pushed through a measurable `f`, where `μ = ν.map f`.  Such a replacement keeps the
output law whenever `p` is measurable in the sense the accuracy proof already
establishes (`Refines.runEstimate_eq`).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

namespace ArlibCommunity.Algorithms.CV18

/-! ## The standard Gaussian density -/

/-- Tonelli for a product of one-variable functions on `ℝⁿ`. -/
theorem lintegral_pi_prod : ∀ (n : ℕ) (μ : Fin n → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (f : Fin n → ℝ → ℝ≥0∞), (∀ i, Measurable (f i)) →
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ t, f i t ∂μ i
  | 0, μ, _, f, _ => by simp
  | n + 1, μ, _, f, hf => by
      have hmp := measurePreserving_piFinSuccAbove μ 0
      rw [← hmp.symm.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
      simp only [Fin.prod_univ_succ]
      have hsplit : ∀ p : ℝ × (Fin n → ℝ),
          f 0 (((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm p) 0) *
            ∏ i : Fin n, f i.succ (((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm p)
              i.succ) =
          f 0 p.1 * ∏ i : Fin n, f i.succ (p.2 i) := by
        intro p
        simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
      simp_rw [hsplit]
      rw [lintegral_prod_mul (f := f 0) (g := fun y : Fin n → ℝ => ∏ i, f i.succ (y i))
        (hf 0).aemeasurable
        (Finset.measurable_prod _ fun i _ => (hf i.succ).comp (measurable_pi_apply i)).aemeasurable]
      rw [lintegral_pi_prod n (fun j => μ (Fin.succAbove 0 j)) (fun i => f i.succ)
        (fun i => hf i.succ)]
      simp

/-- Independent standard Gaussians in each coordinate have the product density. -/
theorem pi_gaussianReal_eq_withDensity (n : ℕ) :
    Measure.pi (fun _ : Fin n => gaussianReal 0 1) =
      (volume : Measure (Fin n → ℝ)).withDensity
        (fun x => ∏ i, gaussianPDF 0 1 (x i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), volume_pi, Measure.restrict_pi_pi,
    lintegral_pi_prod n _ _ (fun _ => measurable_gaussianPDF 0 1)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero, withDensity_apply _ (hs i)]

/-- The standard Gaussian density on `ℝⁿ`, as a function of the norm:
`φ(r) = (2π)^{-n/2} e^{-r²/2}`. -/
noncomputable def radialDensity (n : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((√(2 * Real.pi))⁻¹ ^ n * Real.exp (-r ^ 2 / 2))

theorem measurable_radialDensity (n : ℕ) : Measurable (radialDensity n) := by
  unfold radialDensity; fun_prop

theorem prod_gaussianPDF_eq (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) :
    ∏ i, gaussianPDF 0 1 (y i) = radialDensity n ‖y‖ := by
  rw [radialDensity, gaussianPDF_def,
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPDFReal_nonneg 0 1 _)]
  congr 1
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_sum,
    EuclideanSpace.real_norm_sq_eq, Finset.sum_neg_distrib, Finset.sum_div, neg_div]

/-- **The standard Gaussian has density `φ(‖x‖)`.** -/
theorem stdGaussian_apply (n : ℕ) {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA : MeasurableSet A) :
    stdGaussian (EuclideanSpace ℝ (Fin n)) A = ∫⁻ y in A, radialDensity n ‖y‖ := by
  rw [← map_pi_eq_stdGaussian, Measure.map_apply (by fun_prop) hA,
    pi_gaussianReal_eq_withDensity, withDensity_apply _ (by measurability)]
  have hemb : MeasurableEmbedding (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) :=
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
  rw [← (PiLp.volume_preserving_toLp (Fin n)).setLIntegral_comp_preimage_emb hemb]
  refine setLIntegral_congr_fun (hemb.measurable hA) fun x _ => ?_
  rw [← prod_gaussianPDF_eq]


/-! ## The two point laws -/

/-- Two probability measures that are multiples of the same measure are equal. -/
theorem eq_of_smul_of_isProbabilityMeasure {X : Type*} [MeasurableSpace X]
    {μ ν m : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (a b : ℝ≥0∞)
    (hμ : μ = a • m) (hν : ν = b • m) : μ = ν := by
  have h1 : a * m univ = 1 := by
    rw [← measure_univ (μ := μ), hμ, Measure.smul_apply, smul_eq_mul]
  have h2 : b * m univ = 1 := by
    rw [← measure_univ (μ := ν), hν, Measure.smul_apply, smul_eq_mul]
  have hm0 : m univ ≠ 0 := fun h => by simp [h] at h1
  have hmtop : m univ ≠ ⊤ := fun h => by
    rw [h] at h1
    rcases eq_or_ne a 0 with ha | ha
    · simp [ha] at h1
    · simp [ENNReal.mul_top ha] at h1
  have hab : a = b := by
    have := h1.trans h2.symm
    exact (ENNReal.mul_left_inj hm0 hmtop).mp this
  rw [hμ, hν, hab]

/-- The uniform law on the closed ball of radius `r > 0` is the unit-ball law scaled by
`r`. -/
theorem centeredBall_eq_map_smul {n : ℕ} [NeZero n] {r : ℝ} (hr : 0 < r) :
    centeredBall n r = (centeredBall n 1).map (r • ·) := by
  let e := MeasurableEquiv.smul₀ (α := AmbientSpace n) r hr.ne'
  have hpre : e ⁻¹' ball (0 : AmbientSpace n) r = ball 0 1 := by
    ext y
    have he : e y = r • y := rfl
    simp only [mem_preimage, mem_ball, dist_zero_right, he, norm_smul, Real.norm_eq_abs,
      abs_of_pos hr]
    constructor
    · intro h; nlinarith [norm_nonneg y]
    · intro h; nlinarith [norm_nonneg y]
  have hmap : (volume.restrict (ball (0 : AmbientSpace n) 1)).map (r • ·) =
      ENNReal.ofReal (abs (r ^ Module.finrank ℝ (AmbientSpace n))⁻¹) •
        volume.restrict (ball (0 : AmbientSpace n) r) := by
    change (volume.restrict (ball (0 : AmbientSpace n) 1)).map e = _
    rw [← hpre, ← MeasurableEquiv.restrict_map]
    change (volume.map (r • ·)).restrict _ = _
    rw [Measure.map_addHaar_smul volume hr.ne', Measure.restrict_smul]
  refine eq_of_smul_of_isProbabilityMeasure (volume (ball (0 : AmbientSpace n) r))⁻¹
    ((volume (ball (0 : AmbientSpace n) 1))⁻¹ *
      ENNReal.ofReal (abs (r ^ Module.finrank ℝ (AmbientSpace n))⁻¹))
    (centeredBall_eq_openBall hr) ?_
  rw [centeredBall_eq_openBall one_pos, Measure.map_smul, hmap, smul_smul]
  fun_prop

/-- **The ball-walk proposal law.**  For `r > 0`, a uniform point of the closed ball of
radius `r` around `x` is `x + r · u` for `u` uniform on the closed unit ball. -/
theorem uniformBall_eq_map {n : ℕ} [NeZero n] (x : AmbientSpace n) {r : ℝ} (hr : 0 < r) :
    uniformBall n x r = (centeredBall n 1).map fun u => x + r • u := by
  rw [uniformBall, centeredBall_eq_map_smul hr, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- The standard Gaussian has density `(2π)^{-n/2} e^{-‖x‖²/2}`. -/
theorem standardGaussian_eq_withDensity (n : ℕ) :
    standardGaussian n =
      volume.withDensity fun y => radialDensity n ‖y‖ := by
  ext A hA
  rw [standardGaussian, stdGaussian_apply n hA, withDensity_apply _ hA]

/-- **The starting-point law.** `initialGaussianLaw q` is the law of `√σ₀² · g` for `g` a
standard Gaussian vector. -/
theorem initialGaussianLaw_eq_map (q : VolumeParams) :
    initialGaussianLaw q =
      (standardGaussian q.n).map (Real.sqrt (initialVariance q) • ·) := by
  set v := initialVariance q
  have hv : 0 < v := initialVariance_pos q
  set s := Real.sqrt v
  have hs : 0 < s := Real.sqrt_pos.mpr hv
  have hn : 0 < q.n := lt_of_lt_of_le (by norm_num) q.dim_ok
  have : NeZero q.n := ⟨hn.ne'⟩
  let m : Measure (AmbientSpace q.n) :=
    volume.withDensity fun x => ENNReal.ofReal (gaussianDensity v x)
  have hZ := initialGaussianIntegral_pos q
  -- the target is a multiple of `m`
  have hlaw : initialGaussianLaw q = ENNReal.ofReal (initialGaussianIntegral q)⁻¹ • m := by
    unfold initialGaussianLaw
    rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    funext x
    rw [Pi.smul_apply, smul_eq_mul, ← ENNReal.ofReal_mul (inv_nonneg.mpr hZ.le), div_eq_mul_inv,
      mul_comm]
  -- the scaled Gaussian is a multiple of `m`
  let e := MeasurableEquiv.smul₀ (α := AmbientSpace q.n) s hs.ne'
  let c : ℝ≥0∞ := ENNReal.ofReal (abs (s ^ Module.finrank ℝ (AmbientSpace q.n))⁻¹)
  have hvol : volume.map e = c • (volume : Measure (AmbientSpace q.n)) :=
    Measure.map_addHaar_smul volume hs.ne'
  have hdens : ∀ x : AmbientSpace q.n,
      radialDensity q.n ‖e.symm x‖ =
        ENNReal.ofReal ((√(2 * Real.pi))⁻¹ ^ q.n) * ENNReal.ofReal (gaussianDensity v x) := by
    intro x
    rw [radialDensity, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hsymm : e.symm x = s⁻¹ • x := rfl
    rw [hsymm, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, gaussianDensity]
    congr 2
    rw [mul_pow, inv_pow, Real.sq_sqrt hv.le]
    field_simp
  have hgauss : (standardGaussian q.n).map (s • ·) =
      (c * ENNReal.ofReal ((√(2 * Real.pi))⁻¹ ^ q.n)) • m := by
    ext A hA
    change (standardGaussian q.n).map e A = _
    rw [Measure.map_apply e.measurable hA, standardGaussian_eq_withDensity,
      withDensity_apply _ (e.measurable hA), Measure.smul_apply, smul_eq_mul,
      withDensity_apply _ hA]
    have hcomp : (fun y : AmbientSpace q.n => radialDensity q.n ‖y‖) =
        (fun x => radialDensity q.n ‖e.symm x‖) ∘ e := by
      funext y; simp
    rw [hcomp, ← lintegral_indicator (e.measurable hA)]
    rw [show (e ⁻¹' A).indicator ((fun x => radialDensity q.n ‖e.symm x‖) ∘ e)
        = (A.indicator fun x => radialDensity q.n ‖e.symm x‖) ∘ e by
      funext y
      by_cases h : e y ∈ A <;> simp [h]]
    simp only [Function.comp_def]
    rw [← lintegral_map_equiv (fun x => A.indicator
      (fun x => radialDensity q.n ‖e.symm x‖) x) e, hvol, lintegral_smul_measure, lintegral_indicator hA]
    simp_rw [hdens]
    rw [lintegral_const_mul _ (by unfold gaussianDensity; fun_prop), mul_assoc]
    rfl
  exact eq_of_smul_of_isProbabilityMeasure _ _ hlaw hgauss


/-! ## Refining a point draw -/

section Refinement

open MembershipOracleProgram

/-- `p'` is `p` with some point draws replaced by draws that produce the same law. -/
inductive Refines {n : ℕ} {α : Type} :
    MembershipOracleProgram n α → MembershipOracleProgram n α → Prop where
  | pure (r : α) : Refines (.pure r) (.pure r)
  | query (x : AmbientSpace n) {k k' : Bool → MembershipOracleProgram n α}
      (h : ∀ b, Refines (k b) (k' b)) : Refines (.query x k) (.query x k')
  | randomNat (law : PMF ℕ) {k k' : ℕ → MembershipOracleProgram n α}
      (h : ∀ s, Refines (k s) (k' s)) : Refines (.randomNat law k) (.randomNat law k')
  | randomPoint (law : Measure (AmbientSpace n)) (hlaw : IsProbabilityMeasure law)
      {k k' : AmbientSpace n → MembershipOracleProgram n α}
      (h : ∀ y, Refines (k y) (k' y)) :
      Refines (.randomPoint law hlaw k) (.randomPoint law hlaw k')
  | randomReal (law : Measure ℝ) (hlaw : IsProbabilityMeasure law)
      {k k' : ℝ → MembershipOracleProgram n α}
      (h : ∀ v, Refines (k v) (k' v)) :
      Refines (.randomReal law hlaw k) (.randomReal law hlaw k')
  /-- A point draw from `μ` becomes a draw `g` from `ν`, then `f g`. -/
  | push (μ : Measure (AmbientSpace n)) (hμ : IsProbabilityMeasure μ)
      (ν : Measure (AmbientSpace n)) (hν : IsProbabilityMeasure ν)
      (f : AmbientSpace n → AmbientSpace n) (hf : Measurable f) (heq : μ = ν.map f)
      {k k' : AmbientSpace n → MembershipOracleProgram n α}
      (h : ∀ y, Refines (k y) (k' y)) :
      Refines (.randomPoint μ hμ k) (.randomPoint ν hν fun g => k' (f g))

variable {n : ℕ} {α β : Type}

theorem Refines.refl : ∀ p : MembershipOracleProgram n α, Refines p p
  | .pure r => .pure r
  | .query x k => .query x fun b => Refines.refl (k b)
  | .randomNat law k => .randomNat law fun s => Refines.refl (k s)
  | .randomPoint law h k => .randomPoint law h fun y => Refines.refl (k y)
  | .randomReal law h k => .randomReal law h fun v => Refines.refl (k v)

/-- Refinement is preserved by sequential composition. -/
theorem Refines.bind {p p' : MembershipOracleProgram n α}
    {f f' : α → MembershipOracleProgram n β} (hp : Refines p p')
    (hf : ∀ a, Refines (f a) (f' a)) : Refines (p.bind f) (p'.bind f') := by
  induction hp with
  | pure r => exact hf r
  | query x h ih => exact .query x ih
  | randomNat law h ih => exact .randomNat law ih
  | randomPoint law hlaw h ih => exact .randomPoint law hlaw ih
  | randomReal law hlaw h ih => exact .randomReal law hlaw ih
  | push μ hμ ν hν g hg heq h ih => exact .push μ hμ ν hν g hg heq ih

/-- Refinement is preserved by the global query cap. -/
theorem Refines.withQueryCap {p p' : MembershipOracleProgram n α} (hp : Refines p p')
    (budget : ℕ) : Refines (p.withQueryCap budget) (p'.withQueryCap budget) := by
  induction hp generalizing budget with
  | pure r => exact .pure _
  | query x h ih =>
      cases budget with
      | zero => exact .pure _
      | succ budget => exact .query x fun b => ih b budget
  | randomNat law h ih => exact .randomNat law fun s => ih s budget
  | randomPoint law hlaw h ih => exact .randomPoint law hlaw fun y => ih y budget
  | randomReal law hlaw h ih => exact .randomReal law hlaw fun v => ih v budget
  | push μ hμ ν hν g hg heq h ih => exact .push μ hμ ν hν g hg heq fun y => ih y budget

/-- Binding a pushforward: `(ν.map f).bind R = ν.bind (R ∘ f)`. -/
theorem bind_map' {γ : Type} [MeasurableSpace γ] (ν : Measure (AmbientSpace n))
    (f : AmbientSpace n → AmbientSpace n) (hf : Measurable f)
    (R : AmbientSpace n → Measure γ) (hR : Measurable R) :
    (ν.map f).bind R = ν.bind fun g => R (f g) := by
  ext s hs
  have hRs : Measurable fun y => R y s := (Measure.measurable_coe hs).comp hR
  rw [Measure.bind_apply hs hR.aemeasurable, lintegral_map hRs hf,
    Measure.bind_apply hs (f := fun g => R (f g)) (hR.comp hf).aemeasurable]

/-- **Refining keeps the output law** of a program that is measurable in the sense of the
accuracy proof. -/
theorem Refines.runEstimate_eq [MeasurableSpace α] (oracle : AmbientSpace n → Bool)
    {p p' : MembershipOracleProgram n α} (hp : Refines p p')
    (hmeas : p.StronglyMeasurable oracle) :
    p'.runEstimate oracle = p.runEstimate oracle := by
  induction hp with
  | pure r => rfl
  | query x h ih => exact ih _ hmeas
  | randomNat law h ih =>
      simp only [runEstimate]
      congr 1
      funext s
      exact ih s (hmeas.2 s)
  | randomPoint law hlaw h ih =>
      simp only [runEstimate]
      congr 1
      funext y
      exact ih y (hmeas.2 y)
  | randomReal law hlaw h ih =>
      simp only [runEstimate]
      congr 1
      funext v
      exact ih v (hmeas.2 v)
  | push μ hμ ν hν g hg heq h ih =>
      simp only [runEstimate]
      have hk : ∀ y, (_ : MembershipOracleProgram n α).runEstimate oracle = _ :=
        fun y => ih y (hmeas.2 y)
      simp_rw [hk, heq]
      exact (bind_map' ν g hg _ hmeas.1).symm

end Refinement

end ArlibCommunity.Algorithms.CV18
