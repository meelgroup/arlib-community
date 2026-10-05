/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofProperCostedRestart
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofKernelBridge
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAverageConductanceLV

/-!
# The lazy proper-proposal clock

This file gives the proposal mark to the lazy Metropolis Gaussian walk while
preserving the fact that a proper proposal is a proposal which lands in the
body, whether or not its Metropolis test changes the state.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

variable {n : ℕ}

/-- One lazy Gaussian Metropolis step with its proper-proposal mark exposed.
On a proper proposal, the state follows one lazy speedy step; an improper
proposal leaves the state fixed. -/
noncomputable def lazyProperProposalGaussianAux
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K) (delta s : ℝ) :
    Kernel (EuclideanSpace ℝ (Fin n)) (Bool × EuclideanSpace ℝ (Fin n)) where
  toFun x := ell K delta x •
      (lazy (speedyMetropolisGaussian K delta s) x).map (fun y => (true, y)) +
    (1 - ell K delta x) • Measure.dirac (false, x)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun t ht => ?_
    have htrue : Measurable (fun y : EuclideanSpace ℝ (Fin n) => (true, y)) :=
      measurable_const.prodMk measurable_id
    have hfalse : Measurable (fun x : EuclideanSpace ℝ (Fin n) => (false, x)) :=
      measurable_const.prodMk measurable_id
    simp_rw [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      Measure.map_apply htrue ht, Measure.dirac_apply' _ ht]
    exact ((measurable_ell hK delta).mul
      (Kernel.measurable_coe (lazy (speedyMetropolisGaussian K delta s)) (htrue ht))).add
      ((measurable_const.sub (measurable_ell hK delta)).mul
        (measurable_one.indicator (hfalse ht)))

theorem lazyProperProposalGaussianAux_apply_set
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (delta s : ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    {t : Set (Bool × EuclideanSpace ℝ (Fin n))} (ht : MeasurableSet t) :
    lazyProperProposalGaussianAux K hK delta s x t =
      ell K delta x * lazy (speedyMetropolisGaussian K delta s) x
          ((fun y : EuclideanSpace ℝ (Fin n) => (true, y)) ⁻¹' t) +
        (1 - ell K delta x) * t.indicator 1 (false, x) := by
  change (ell K delta x •
      (lazy (speedyMetropolisGaussian K delta s) x).map (fun y => (true, y)) +
    (1 - ell K delta x) • Measure.dirac (false, x)) t = _
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    smul_eq_mul, smul_eq_mul,
    Measure.map_apply (by fun_prop :
      Measurable (fun y : EuclideanSpace ℝ (Fin n) => (true, y))) ht,
    Measure.dirac_apply' _ ht]

instance isMarkovKernel_lazyProperProposalGaussianAux
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K) (delta s : ℝ) :
    IsMarkovKernel (lazyProperProposalGaussianAux K hK delta s) := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [lazyProperProposalGaussianAux_apply_set hK delta s x MeasurableSet.univ]
  simp only [Set.preimage_univ, measure_univ, Set.indicator_of_mem, Set.mem_univ,
    Pi.one_apply, mul_one]
  exact add_tsub_cancel_of_le (ell_le_one K delta x)

theorem mul_inv_two_add_one_sub_eq_inv_two_mul_one_sub_add_inv_two
    {a : ℝ≥0∞} (ha : a ≤ 1) :
    a * (2 : ℝ≥0∞)⁻¹ + (1 - a) =
      (2 : ℝ≥0∞)⁻¹ * (1 - a) + (2 : ℝ≥0∞)⁻¹ := by
  have hatop : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ha
  have hsubtop : 1 - a ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hhalf : (2 : ℝ≥0∞)⁻¹ ≠ ⊤ := by norm_num
  have haprod : a * (2 : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.mul_ne_top hatop hhalf
  have hhprod : (2 : ℝ≥0∞)⁻¹ * (1 - a) ≠ ⊤ := ENNReal.mul_ne_top hhalf hsubtop
  have hleft : a * (2 : ℝ≥0∞)⁻¹ + (1 - a) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨haprod, hsubtop⟩
  have hright : (2 : ℝ≥0∞)⁻¹ * (1 - a) + (2 : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hhprod, hhalf⟩
  apply (ENNReal.toReal_eq_toReal_iff' hleft hright).mp
  rw [ENNReal.toReal_add haprod hsubtop,
    ENNReal.toReal_add hhprod hhalf,
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_sub_of_le ha (by simp)]
  norm_num
  ring

/-- Forgetting the proposal mark gives exactly the lazy ordinary Metropolis
kernel used by the executable CV18 step. -/
theorem map_snd_lazyProperProposalGaussianAux_apply
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (delta s : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (lazyProperProposalGaussianAux K hK delta s x).map Prod.snd =
      lazy (metropolisGaussian K delta s) x := by
  ext t ht
  rw [Measure.map_apply measurable_snd ht,
    lazyProperProposalGaussianAux_apply_set hK delta s x (measurable_snd ht),
    lazy_apply_set _ x ht,
    metropolisGaussian_apply_eq_properProposalMixture hK delta s x,
    Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    smul_eq_mul, smul_eq_mul, Measure.dirac_apply' _ ht]
  change ell K delta x * lazy (speedyMetropolisGaussian K delta s) x t +
      (1 - ell K delta x) * t.indicator 1 x = _
  rw [lazy_apply_set _ x ht]
  by_cases hx : x ∈ t
  · simp only [Set.indicator_of_mem hx, Pi.one_apply]
    calc
      ell K delta x * ((2 : ℝ≥0∞)⁻¹ * speedyMetropolisGaussian K delta s x t +
            (2 : ℝ≥0∞)⁻¹ * 1) + (1 - ell K delta x) * 1 =
          (2 : ℝ≥0∞)⁻¹ *
              (ell K delta x * speedyMetropolisGaussian K delta s x t) +
            (ell K delta x * (2 : ℝ≥0∞)⁻¹ + (1 - ell K delta x)) := by ring
      _ = (2 : ℝ≥0∞)⁻¹ *
              (ell K delta x * speedyMetropolisGaussian K delta s x t) +
            ((2 : ℝ≥0∞)⁻¹ * (1 - ell K delta x) + (2 : ℝ≥0∞)⁻¹) := by
        rw [mul_inv_two_add_one_sub_eq_inv_two_mul_one_sub_add_inv_two
          (ell_le_one K delta x)]
      _ = (2 : ℝ≥0∞)⁻¹ *
            (ell K delta x * speedyMetropolisGaussian K delta s x t +
              (1 - ell K delta x) * 1) + (2 : ℝ≥0∞)⁻¹ * 1 := by ring
  · simp only [Set.indicator_of_notMem hx, mul_zero, add_zero]
    ring

/-- The homogeneous lifted lazy marked chain. -/
noncomputable def lazyProperProposalGaussianLift
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K) (delta s : ℝ) :
    Kernel (Bool × EuclideanSpace ℝ (Fin n))
      (Bool × EuclideanSpace ℝ (Fin n)) :=
  Kernel.comap (lazyProperProposalGaussianAux K hK delta s) Prod.snd measurable_snd

@[simp] theorem lazyProperProposalGaussianLift_apply
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K) (delta s : ℝ)
    (p : Bool × EuclideanSpace ℝ (Fin n)) :
    lazyProperProposalGaussianLift K hK delta s p =
      lazyProperProposalGaussianAux K hK delta s p.2 := rfl

instance isMarkovKernel_lazyProperProposalGaussianLift
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K) (delta s : ℝ) :
    IsMarkovKernel (lazyProperProposalGaussianLift K hK delta s) := by
  rw [lazyProperProposalGaussianLift]
  infer_instance

theorem lazyProperProposalGaussianLift_apply_false_singleton
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (delta s : ℝ)
    (p : Bool × EuclideanSpace ℝ (Fin n)) :
    lazyProperProposalGaussianLift K hK delta s p {(false, p.2)} =
      1 - ell K delta p.2 := by
  have hempty :
      (fun y : EuclideanSpace ℝ (Fin n) => (true, y)) ⁻¹' {(false, p.2)} = ∅ := by
    ext y
    simp
  rw [lazyProperProposalGaussianLift_apply,
    lazyProperProposalGaussianAux_apply_set hK delta s p.2 (measurableSet_singleton _),
    hempty, measure_empty, mul_zero, zero_add]
  simp

theorem lazyProperProposalGaussianLift_apply_true_prod
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (delta s : ℝ)
    (p : Bool × EuclideanSpace ℝ (Fin n)) {t : Set (EuclideanSpace ℝ (Fin n))}
    (ht : MeasurableSet t) :
    lazyProperProposalGaussianLift K hK delta s p ({true} ×ˢ t) =
      ell K delta p.2 * lazy (speedyMetropolisGaussian K delta s) p.2 t := by
  rw [lazyProperProposalGaussianLift_apply,
    lazyProperProposalGaussianAux_apply_set hK delta s p.2
      (measurableSet_singleton true |>.prod ht)]
  simp

theorem map_snd_lazyProperProposalGaussianLift_apply
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (delta s : ℝ)
    (p : Bool × EuclideanSpace ℝ (Fin n)) :
    (lazyProperProposalGaussianLift K hK delta s p).map Prod.snd =
      lazy (metropolisGaussian K delta s) p.2 := by
  rw [lazyProperProposalGaussianLift_apply]
  exact map_snd_lazyProperProposalGaussianAux_apply hK delta s p.2

theorem map_snd_lazyProperProposalGaussianLift
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (delta s : ℝ) :
    Kernel.map (lazyProperProposalGaussianLift K hK delta s) Prod.snd =
      Kernel.comap (lazy (metropolisGaussian K delta s)) Prod.snd measurable_snd := by
  ext p
  rw [Kernel.map_apply _ measurable_snd, Kernel.comap_apply,
    map_snd_lazyProperProposalGaussianLift_apply hK delta s]

/-- At every deterministic time, the state coordinate of the marked lazy
trajectory has the same law as the actual lazy Metropolis trajectory. -/
theorem map_state_eval_pathMeasure_lazyProperProposalGaussianLift
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (delta s : ℝ)
    (p : Bool × EuclideanSpace ℝ (Fin n)) (a : ℕ) :
    (pathMeasure (lazyProperProposalGaussianLift K hK delta s)
      (Measure.dirac p)).map (fun omega => (omega a).2) =
    (pathMeasure (lazy (metropolisGaussian K delta s))
      (Measure.dirac p.2)).map (fun omega => omega a) := by
  induction a with
  | zero =>
      rw [show (fun omega : ℕ → Bool × EuclideanSpace ℝ (Fin n) => (omega 0).2) =
          Prod.snd ∘ (fun omega : ℕ → Bool × EuclideanSpace ℝ (Fin n) => omega 0) from rfl,
        ← Measure.map_map measurable_snd (measurable_pi_apply 0),
        map_eval_pathMeasure_zero, map_eval_pathMeasure_zero,
        Measure.map_dirac]
  | succ a ih =>
      have ih' :
          (pathMeasure (lazyProperProposalGaussianLift K hK delta s)
              (Measure.dirac p)).map (Prod.snd ∘ fun omega => omega a) =
            (pathMeasure (lazy (metropolisGaussian K delta s))
              (Measure.dirac p.2)).map (fun omega => omega a) := by
        change (pathMeasure (lazyProperProposalGaussianLift K hK delta s)
            (Measure.dirac p)).map (fun omega => (omega a).2) = _
        exact ih
      rw [show (fun omega : ℕ → Bool × EuclideanSpace ℝ (Fin n) =>
          (omega (a + 1)).2) =
          Prod.snd ∘ (fun omega : ℕ → Bool × EuclideanSpace ℝ (Fin n) =>
            omega (a + 1)) from rfl,
        ← Measure.map_map measurable_snd (measurable_pi_apply (a + 1)),
        map_eval_pathMeasure_succ, Measure.map_comp _ _ measurable_snd,
        map_snd_lazyProperProposalGaussianLift hK delta s,
        bind_comap, Measure.map_map measurable_snd (measurable_pi_apply a),
        ih', map_eval_pathMeasure_succ]

theorem pathMeasure_lazyProperProposalGaussianLift_dirac_holdsUntil
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (delta s : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    pathMeasure (lazyProperProposalGaussianLift K hK delta s)
        (Measure.dirac (false, x))
        {omega : ℕ → Bool × EuclideanSpace ℝ (Fin n) |
          ∀ i ≤ k, omega i = (false, x)} =
      (1 - ell K delta x) ^ k := by
  rw [pathMeasure_dirac_holdsUntil,
    lazyProperProposalGaussianLift_apply_false_singleton hK delta s]

theorem lintegral_firstProperTime_pathMeasure_lazyProperProposalGaussianLift
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (delta s : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ∫⁻ omega, (∑' k : ℕ,
        {omega' : ℕ → Bool × EuclideanSpace ℝ (Fin n) |
          ∀ i ≤ k, omega' i = (false, x)}.indicator
            (1 : (ℕ → Bool × EuclideanSpace ℝ (Fin n)) → ℝ≥0∞) omega)
      ∂(pathMeasure (lazyProperProposalGaussianLift K hK delta s)
        (Measure.dirac (false, x))) =
      (ell K delta x)⁻¹ := by
  rw [lintegral_tsum fun k =>
    (measurable_one.indicator (measurableSet_holdsUntil (false, x) k)).aemeasurable]
  simp_rw [lintegral_indicator_one (measurableSet_holdsUntil (false, x) _),
    pathMeasure_lazyProperProposalGaussianLift_dirac_holdsUntil hK delta s]
  rw [ENNReal.tsum_geometric,
    ENNReal.sub_sub_cancel ENNReal.one_ne_top (ell_le_one K delta x)]

/-- A first-proper cylinder for the lazy marked trajectory has the same
geometric waiting factor and a lazy-speedy terminal transition. -/
theorem pathMeasure_lazy_firstProperCylinder
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (delta s : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) {t : Set (EuclideanSpace ℝ (Fin n))}
    (ht : MeasurableSet t) (j : ℕ) :
    pathMeasure (lazyProperProposalGaussianLift K hK delta s)
        (Measure.dirac (false, x)) (firstProperCylinder x t j) =
      (1 - ell K delta x) ^ j *
        (ell K delta x * lazy (speedyMetropolisGaussian K delta s) x t) := by
  rw [firstProperCylinder, pathMeasure_dirac_holdsUntil_then_mem _ _ _
      (measurableSet_singleton true |>.prod ht),
    lazyProperProposalGaussianLift_apply_false_singleton hK delta s,
    lazyProperProposalGaussianLift_apply_true_prod hK delta s
      (p := (false, x)) (t := t) ht]

theorem pathMeasure_lazy_iUnion_firstProperCylinder
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (delta s : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) {t : Set (EuclideanSpace ℝ (Fin n))}
    (ht : MeasurableSet t) (hell : ell K delta x ≠ 0) :
    pathMeasure (lazyProperProposalGaussianLift K hK delta s)
        (Measure.dirac (false, x)) (⋃ j : ℕ, firstProperCylinder x t j) =
      lazy (speedyMetropolisGaussian K delta s) x t := by
  rw [measure_iUnion (pairwise_disjoint_firstProperCylinder x t)
      (measurableSet_firstProperCylinder x ht)]
  simp_rw [pathMeasure_lazy_firstProperCylinder hK delta s x ht]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric,
    ENNReal.sub_sub_cancel ENNReal.one_ne_top (ell_le_one K delta x),
    ← mul_assoc, ENNReal.inv_mul_cancel hell
      (ne_top_of_le_ne_top ENNReal.one_ne_top (ell_le_one K delta x)), one_mul]

/-- Stopping the lazy marked trajectory at its first proper proposal gives
exactly one lazy speedy transition. -/
theorem map_first_markedChain_pathMeasure_lazyProperProposalGaussianLift
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (delta s : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (hell : ell K delta x ≠ 0) :
    (pathMeasure (lazyProperProposalGaussianLift K hK delta s)
      (Measure.dirac (false, x))).map firstProperMarkedState =
      lazy (speedyMetropolisGaussian K delta s) x := by
  let mu := pathMeasure (lazyProperProposalGaussianLift K hK delta s)
    (Measure.dirac (false, x))
  let stop := firstProperMarkedState (n := n)
  have hstop : Measurable stop := measurable_firstProperMarkedState
  ext t ht
  rw [Measure.map_apply hstop ht]
  let U : Set (ℕ → Bool × EuclideanSpace ℝ (Fin n)) :=
    ⋃ j : ℕ, firstProperCylinder x Set.univ j
  have hU : mu U = mu Set.univ := by
    calc
      mu U = lazy (speedyMetropolisGaussian K delta s) x Set.univ := by
        exact pathMeasure_lazy_iUnion_firstProperCylinder
          hK delta s x MeasurableSet.univ hell
      _ = 1 := measure_univ
      _ = mu Set.univ := measure_univ.symm
  have hUtop : mu U ≠ ∞ := by rw [hU, measure_univ]; exact ENNReal.one_ne_top
  have hinter := Measure.measure_inter_eq_of_measure_eq (hstop ht) hU
    (Set.subset_univ U) hUtop
  change mu (stop ⁻¹' t) = _
  calc
    mu (stop ⁻¹' t) = mu (U ∩ stop ⁻¹' t) := by
      simpa only [Set.univ_inter] using hinter.symm
    _ = mu (⋃ j : ℕ, firstProperCylinder x t j) := by
      rw [iUnion_firstProperCylinder_eq_inter_markedChain]
      rfl
    _ = lazy (speedyMetropolisGaussian K delta s) x t :=
      pathMeasure_lazy_iUnion_firstProperCylinder hK delta s x ht hell

/-! ## Stopped and costed lazy kernels -/

noncomputable def lazyProperProposalTrajectoryKernel
    (K : Set (GaussianState n)) (hK : MeasurableSet K) (delta s : ℝ) :
    Kernel (GaussianState n) (LiftedGaussianPath n) :=
  Kernel.comap
    (Kernel.traj (X := fun _ : ℕ => Bool × GaussianState n)
      (chainKernel (lazyProperProposalGaussianLift K hK delta s)) 0)
    (fun x (_ : ↥(Finset.Iic 0)) => (false, x))
    (measurable_pi_lambda _ fun _ => measurable_const.prodMk measurable_id)

instance (K : Set (GaussianState n)) (hK : MeasurableSet K) (delta s : ℝ) :
    IsMarkovKernel (lazyProperProposalTrajectoryKernel K hK delta s) := by
  rw [lazyProperProposalTrajectoryKernel]
  infer_instance

theorem lazyProperProposalTrajectoryKernel_apply
    (K : Set (GaussianState n)) (hK : MeasurableSet K) (delta s : ℝ)
    (x : GaussianState n) :
    lazyProperProposalTrajectoryKernel K hK delta s x =
      pathMeasure (lazyProperProposalGaussianLift K hK delta s)
        (Measure.dirac (false, x)) := by
  rw [lazyProperProposalTrajectoryKernel, Kernel.comap_apply, pathMeasure,
    Kernel.trajMeasure, Measure.map_dirac]
  rw [Measure.dirac_bind (Kernel.measurable _)]
  congr 2

noncomputable def lazyProperProposalStoppedKernel
    (K : Set (GaussianState n)) (hK : MeasurableSet K) (delta s : ℝ) :
    Kernel (GaussianState n) (GaussianState n) :=
  Kernel.map (lazyProperProposalTrajectoryKernel K hK delta s)
    firstProperMarkedState

instance (K : Set (GaussianState n)) (hK : MeasurableSet K) (delta s : ℝ) :
    IsMarkovKernel (lazyProperProposalStoppedKernel K hK delta s) := by
  rw [lazyProperProposalStoppedKernel]
  exact Kernel.IsMarkovKernel.map _ measurable_firstProperMarkedState

theorem lazyProperProposalStoppedKernel_apply_eq_lazy_speedy
    {K : Set (GaussianState n)} (hK : MeasurableSet K) (delta s : ℝ)
    (x : GaussianState n) (hell : ell K delta x ≠ 0) :
    lazyProperProposalStoppedKernel K hK delta s x =
      lazy (speedyMetropolisGaussian K delta s) x := by
  rw [lazyProperProposalStoppedKernel,
    Kernel.map_apply _ measurable_firstProperMarkedState,
    lazyProperProposalTrajectoryKernel_apply]
  exact map_first_markedChain_pathMeasure_lazyProperProposalGaussianLift
    hK delta s x hell

noncomputable def lazyProperProposalStartedTrajectoryKernel
    (K : Set (GaussianState n)) (hK : MeasurableSet K) (delta s : ℝ) :
    Kernel (GaussianState n) (GaussianState n × LiftedGaussianPath n) :=
  Kernel.compProd Kernel.id
    (Kernel.prodMkLeft (GaussianState n)
      (lazyProperProposalTrajectoryKernel K hK delta s))

instance (K : Set (GaussianState n)) (hK : MeasurableSet K) (delta s : ℝ) :
    IsMarkovKernel (lazyProperProposalStartedTrajectoryKernel K hK delta s) := by
  unfold lazyProperProposalStartedTrajectoryKernel
  infer_instance

theorem lazyProperProposalStartedTrajectoryKernel_apply
    (K : Set (GaussianState n)) (hK : MeasurableSet K) (delta s : ℝ)
    (x : GaussianState n) :
    lazyProperProposalStartedTrajectoryKernel K hK delta s x =
      (lazyProperProposalTrajectoryKernel K hK delta s x).map
        (fun omega => (x, omega)) := by
  ext A hA
  rw [lazyProperProposalStartedTrajectoryKernel, Kernel.compProd_apply hA,
    Kernel.id_apply, lintegral_dirac']
  · rw [Kernel.prodMkLeft_apply, Measure.map_apply (by fun_prop) hA]
  · exact Kernel.measurable_kernel_prodMk_left' hA x

/-- One honest lazy-speedy transition together with the number of executable
lazy raw transitions through its first proper proposal. -/
noncomputable def lazyProperProposalCostedKernelRaw
    (K : Set (GaussianState n)) (hK : MeasurableSet K) (delta s : ℝ) :
    Kernel (GaussianState n) (ℝ≥0∞ × GaussianState n) :=
  Kernel.map (lazyProperProposalStartedTrajectoryKernel K hK delta s)
    (fun p => (properProposalWaitCost p, firstProperMarkedState p.2))

instance (K : Set (GaussianState n)) (hK : MeasurableSet K) (delta s : ℝ) :
    IsMarkovKernel (lazyProperProposalCostedKernelRaw K hK delta s) := by
  unfold lazyProperProposalCostedKernelRaw
  exact Kernel.IsMarkovKernel.map _
    (measurable_properProposalWaitCost.prodMk
      (measurable_firstProperMarkedState.comp measurable_snd))

theorem lintegral_fst_lazyProperProposalCostedKernelRaw
    {K : Set (GaussianState n)} (hK : MeasurableSet K) (delta s : ℝ)
    (x : GaussianState n) :
    ∫⁻ y, y.1 ∂(lazyProperProposalCostedKernelRaw K hK delta s x) =
      (ell K delta x)⁻¹ := by
  have hpair : Measurable
      (fun p : GaussianState n × LiftedGaussianPath n =>
        (properProposalWaitCost p, firstProperMarkedState p.2)) :=
    measurable_properProposalWaitCost.prodMk
      (measurable_firstProperMarkedState.comp measurable_snd)
  rw [lazyProperProposalCostedKernelRaw, Kernel.map_apply _ hpair,
    lintegral_map measurable_fst hpair,
    lazyProperProposalStartedTrajectoryKernel_apply,
    lintegral_map, lazyProperProposalTrajectoryKernel_apply]
  · have hcost : ∀ omega : LiftedGaussianPath n,
        properProposalWaitCost (x, omega) =
          ∑' k : ℕ, {omega' : LiftedGaussianPath n |
            ∀ i ≤ k, omega' i = (false, x)}.indicator
              (1 : LiftedGaussianPath n → ℝ≥0∞) omega := by
      intro omega
      unfold properProposalWaitCost
      apply tsum_congr
      intro k
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
    rw [lintegral_congr hcost]
    exact lintegral_firstProperTime_pathMeasure_lazyProperProposalGaussianLift
      hK delta s x
  · exact measurable_properProposalWaitCost
  · fun_prop

/-- A zero-cost lift of a state kernel. -/
noncomputable def ennrealZeroCostKernel (P : Kernel (GaussianState n) (GaussianState n)) :
    Kernel (GaussianState n) (ℝ≥0∞ × GaussianState n) :=
  P.map (fun y => (0, y))

instance (P : Kernel (GaussianState n) (GaussianState n)) [IsMarkovKernel P] :
    IsMarkovKernel (ennrealZeroCostKernel P) := by
  unfold ennrealZeroCostKernel
  exact Kernel.IsMarkovKernel.map P (by fun_prop)

/-- Totalized lazy cost kernel. At an ambient stuck point it follows the
prescribed lazy-speedy state law at zero operational cost. -/
noncomputable def lazyProperProposalCostedKernel
    (K : Set (GaussianState n)) (hK : MeasurableSet K) (delta s : ℝ) :
    Kernel (GaussianState n) (ℝ≥0∞ × GaussianState n) := by
  classical
  exact Kernel.piecewise (measurableSet_stuckPoints hK delta)
    (ennrealZeroCostKernel (lazy (speedyMetropolisGaussian K delta s)))
    (lazyProperProposalCostedKernelRaw K hK delta s)

instance (K : Set (GaussianState n)) (hK : MeasurableSet K) (delta s : ℝ) :
    IsMarkovKernel (lazyProperProposalCostedKernel K hK delta s) := by
  classical
  unfold lazyProperProposalCostedKernel
  infer_instance

theorem map_snd_lazyProperProposalCostedKernel_eq_lazy_speedy
    {K : Set (GaussianState n)} (hK : MeasurableSet K) (delta s : ℝ)
    (x : GaussianState n) :
    (lazyProperProposalCostedKernel K hK delta s x).map Prod.snd =
      lazy (speedyMetropolisGaussian K delta s) x := by
  classical
  rw [lazyProperProposalCostedKernel, Kernel.piecewise_apply]
  split_ifs with hx
  · rw [ennrealZeroCostKernel, Kernel.map_apply _ (by fun_prop),
      Measure.map_map measurable_snd (by fun_prop)]
    rw [show Prod.snd ∘ (fun y : GaussianState n => ((0 : ℝ≥0∞), y)) = id by
      funext y
      rfl, Measure.map_id]
  · have hpair : Measurable
        (fun p : GaussianState n × LiftedGaussianPath n =>
          (properProposalWaitCost p, firstProperMarkedState p.2)) :=
      measurable_properProposalWaitCost.prodMk
        (measurable_firstProperMarkedState.comp measurable_snd)
    rw [lazyProperProposalCostedKernelRaw, Kernel.map_apply _ hpair,
      lazyProperProposalStartedTrajectoryKernel_apply,
      Measure.map_map measurable_snd hpair,
      Measure.map_map (measurable_snd.comp hpair) (by fun_prop)]
    change (lazyProperProposalTrajectoryKernel K hK delta s x).map
      firstProperMarkedState = _
    rw [← Kernel.map_apply _ measurable_firstProperMarkedState,
      ← lazyProperProposalStoppedKernel]
    exact lazyProperProposalStoppedKernel_apply_eq_lazy_speedy
      hK delta s x (by
        simpa only [StuckPoints, Set.mem_ofPred_eq] using hx)

theorem lintegral_fst_lazyProperProposalCostedKernel_le_inv_ell
    {K : Set (GaussianState n)} (hK : MeasurableSet K)
    (delta s : ℝ) (x : GaussianState n) :
    ∫⁻ y, y.1 ∂(lazyProperProposalCostedKernel K hK delta s x) ≤
      (ell K delta x)⁻¹ := by
  classical
  rw [lazyProperProposalCostedKernel, Kernel.piecewise_apply]
  split_ifs
  · rw [ennrealZeroCostKernel, Kernel.map_apply _ (by fun_prop),
      lintegral_map measurable_fst (by fun_prop)]
    simp
  · rw [lintegral_fst_lazyProperProposalCostedKernelRaw hK delta s x]

/-- Independently restarting the stopped marked trajectory for `t` proper
proposals has exactly the `t`-step lazy-speedy output law. -/
theorem map_lazyProperProposalCostedExecution_output
    {K : Set (GaussianState n)} (hK : MeasurableSet K) (delta s : ℝ)
    (mu : Measure (GaussianState n)) [IsProbabilityMeasure mu] (t : ℕ) :
    (restartedCostExecution (lazyProperProposalCostedKernel K hK delta s) mu).map
        (fun omega => (omega t).2) =
      iterate (lazy (speedyMetropolisGaussian K delta s)) mu t :=
  map_restartedCostExecution_output _ _
    (map_snd_lazyProperProposalCostedKernel_eq_lazy_speedy hK delta s) mu t

theorem mul_sum_lintegral_inv_ell_iterate_lazySpeedyMetropolisGaussian_le
    {K : Set (GaussianState n)} (hK : MeasurableSet K)
    {delta : ℝ} (hdelta : 0 < delta) (variance : ℝ)
    (hZ0 : ellGaussianMeasure K delta variance Set.univ ≠ 0)
    (hZtop : ellGaussianMeasure K delta variance Set.univ ≠ ⊤)
    {lambda M : ℝ≥0∞}
    (hlambda : lambda * (∫⁻ x in K, gaussianWeight variance x) ≤
      ellGaussianMeasure K delta variance Set.univ)
    {mu : Measure (GaussianState n)}
    (hwarm : IsWarm M mu (ellGaussianProb K delta variance)) (t : ℕ) :
    lambda * ∑ i ∈ Finset.range t,
        ∫⁻ x, (ell K delta x)⁻¹
          ∂(iterate (lazy (speedyMetropolisGaussian K delta variance)) mu i) ≤
      (t : ℝ≥0∞) * M := by
  have hinv : Kernel.Invariant (lazy (speedyMetropolisGaussian K delta variance))
      (ellGaussianProb K delta variance) :=
    (isReversible_lazy
      (isReversible_speedyMetropolisGaussian_prob hK delta variance)).invariant
  have hsum := sum_lintegral_iterate_le_of_isWarm hwarm
    (step_invariant hinv) (fun x => (ell K delta x)⁻¹) t
  have hstationary := mul_lintegral_inv_ell_ellGaussianProb_le_one
    hK hdelta variance hZ0 hZtop hlambda
  calc
    lambda * ∑ i ∈ Finset.range t,
        ∫⁻ x, (ell K delta x)⁻¹
          ∂(iterate (lazy (speedyMetropolisGaussian K delta variance)) mu i) ≤
      lambda * ((t : ℝ≥0∞) *
        (M * ∫⁻ x, (ell K delta x)⁻¹
          ∂(ellGaussianProb K delta variance))) := by gcongr
    _ = (t : ℝ≥0∞) * M *
        (lambda * ∫⁻ x, (ell K delta x)⁻¹
          ∂(ellGaussianProb K delta variance)) := by ring
    _ ≤ (t : ℝ≥0∞) * M * 1 := by gcongr
    _ = (t : ℝ≥0∞) * M := mul_one _

/-- Expected executable lazy raw transitions used by independently restarted
proper steps satisfy the paper's warm-start bound. -/
theorem mul_lintegral_lazyProperProposalTotalCost_le
    {K : Set (GaussianState n)} (hK : MeasurableSet K)
    {delta : ℝ} (hdelta : 0 < delta) (variance : ℝ)
    (hZ0 : ellGaussianMeasure K delta variance Set.univ ≠ 0)
    (hZtop : ellGaussianMeasure K delta variance Set.univ ≠ ⊤)
    {lambda M : ℝ≥0∞}
    (hlambda : lambda * (∫⁻ x in K, gaussianWeight variance x) ≤
      ellGaussianMeasure K delta variance Set.univ)
    {mu : Measure (GaussianState n)} [IsProbabilityMeasure mu]
    (hwarm : IsWarm M mu (ellGaussianProb K delta variance)) (t : ℕ) :
    lambda * (∫⁻ omega, restartedTotalCost t omega
        ∂(restartedCostExecution
          (lazyProperProposalCostedKernel K hK delta variance) mu)) ≤
      (t : ℝ≥0∞) * M := by
  rw [lintegral_restartedTotalCost_eq_sum_stateMeans _
    (lazy (speedyMetropolisGaussian K delta variance))
    (map_snd_lazyProperProposalCostedKernel_eq_lazy_speedy hK delta variance)]
  calc
    lambda * ∑ i ∈ Finset.range t,
        ∫⁻ x, (∫⁻ y, y.1 ∂lazyProperProposalCostedKernel K hK delta variance x)
          ∂(iterate (lazy (speedyMetropolisGaussian K delta variance)) mu i) ≤
      lambda * ∑ i ∈ Finset.range t,
        ∫⁻ x, (ell K delta x)⁻¹
          ∂(iterate (lazy (speedyMetropolisGaussian K delta variance)) mu i) := by
        gcongr with i hi x
        exact lintegral_fst_lazyProperProposalCostedKernel_le_inv_ell
          hK delta variance x
    _ ≤ (t : ℝ≥0∞) * M :=
      mul_sum_lintegral_inv_ell_iterate_lazySpeedyMetropolisGaussian_le
        hK hdelta variance hZ0 hZtop hlambda hwarm t

theorem mul_mul_measure_lazyProperProposalTotalCost_ge_le
    {K : Set (GaussianState n)} (hK : MeasurableSet K)
    {delta : ℝ} (hdelta : 0 < delta) (variance : ℝ)
    (hZ0 : ellGaussianMeasure K delta variance Set.univ ≠ 0)
    (hZtop : ellGaussianMeasure K delta variance Set.univ ≠ ⊤)
    {lambda M : ℝ≥0∞}
    (hlambda : lambda * (∫⁻ x in K, gaussianWeight variance x) ≤
      ellGaussianMeasure K delta variance Set.univ)
    {mu : Measure (GaussianState n)} [IsProbabilityMeasure mu]
    (hwarm : IsWarm M mu (ellGaussianProb K delta variance))
    (t : ℕ) (cutoff : ℝ≥0∞) :
    lambda * cutoff *
        restartedCostExecution
          (lazyProperProposalCostedKernel K hK delta variance) mu
          {omega | cutoff ≤ restartedTotalCost t omega} ≤
      (t : ℝ≥0∞) * M := by
  have hmarkov := mul_meas_ge_le_lintegral
    (measurable_restartedTotalCost (S := GaussianState n) t) cutoff
    (μ := restartedCostExecution
      (lazyProperProposalCostedKernel K hK delta variance) mu)
  calc
    lambda * cutoff *
        restartedCostExecution
          (lazyProperProposalCostedKernel K hK delta variance) mu
          {omega | cutoff ≤ restartedTotalCost t omega} =
      lambda * (cutoff *
        restartedCostExecution
          (lazyProperProposalCostedKernel K hK delta variance) mu
          {omega | cutoff ≤ restartedTotalCost t omega}) := by ring
    _ ≤ lambda * (∫⁻ omega, restartedTotalCost t omega
        ∂(restartedCostExecution
          (lazyProperProposalCostedKernel K hK delta variance) mu)) := by gcongr
    _ ≤ (t : ℝ≥0∞) * M :=
      mul_lintegral_lazyProperProposalTotalCost_le hK hdelta variance
        hZ0 hZtop hlambda hwarm t

/-- Advertised-step expected-cost bound for the lazy proper clock. -/
theorem half_mul_lintegral_lazyProperProposalTotalCost_le_LVStep
    (hn : 2 ≤ n) {K : Set (GaussianState n)}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKfin : volume K ≠ ⊤)
    (hball : ball (0 : GaussianState n) 1 ⊆ K)
    {sigma delta : ℝ} (hsigma : 0 < sigma) (hdelta : 0 < delta)
    (hstep : delta ≤ min sigma 1 / (4096 * Real.sqrt n))
    {M : ℝ≥0∞} {mu : Measure (GaussianState n)} [IsProbabilityMeasure mu]
    (hwarm : IsWarm M mu (ellGaussianProb K delta (sigma ^ 2))) (t : ℕ) :
    ENNReal.ofReal (1 / 2) * (∫⁻ omega, restartedTotalCost t omega
        ∂(restartedCostExecution
          (lazyProperProposalCostedKernel K hKcl.measurableSet delta (sigma ^ 2)) mu)) ≤
      (t : ℝ≥0∞) * M := by
  exact mul_lintegral_lazyProperProposalTotalCost_le hKcl.measurableSet hdelta (sigma ^ 2)
    (ellGaussianMeasure_ne_zero_of_LVStep
      hn hKc hKcl hKfin hball hsigma hdelta hstep)
    (ellGaussianMeasure_ne_top_cv18 hKfin delta (by positivity))
    (half_mul_lintegral_gaussianWeight_le_ellGaussianMeasure_univ_direct
      hn hKc hKcl hKfin hball hsigma hdelta hstep)
    hwarm t

/-- Advertised-step cutoff bound for the lazy proper clock. -/
theorem half_mul_mul_measure_lazyProperProposalTotalCost_ge_le_LVStep
    (hn : 2 ≤ n) {K : Set (GaussianState n)}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKfin : volume K ≠ ⊤)
    (hball : ball (0 : GaussianState n) 1 ⊆ K)
    {sigma delta : ℝ} (hsigma : 0 < sigma) (hdelta : 0 < delta)
    (hstep : delta ≤ min sigma 1 / (4096 * Real.sqrt n))
    {M : ℝ≥0∞} {mu : Measure (GaussianState n)} [IsProbabilityMeasure mu]
    (hwarm : IsWarm M mu (ellGaussianProb K delta (sigma ^ 2)))
    (t : ℕ) (cutoff : ℝ≥0∞) :
    ENNReal.ofReal (1 / 2) * cutoff *
        restartedCostExecution
          (lazyProperProposalCostedKernel K hKcl.measurableSet delta (sigma ^ 2)) mu
          {omega | cutoff ≤ restartedTotalCost t omega} ≤
      (t : ℝ≥0∞) * M := by
  exact mul_mul_measure_lazyProperProposalTotalCost_ge_le hKcl.measurableSet hdelta
    (sigma ^ 2)
    (ellGaussianMeasure_ne_zero_of_LVStep
      hn hKc hKcl hKfin hball hsigma hdelta hstep)
    (ellGaussianMeasure_ne_top_cv18 hKfin delta (by positivity))
    (half_mul_lintegral_gaussianWeight_le_ellGaussianMeasure_univ_direct
      hn hKc hKcl hKfin hball hsigma hdelta hstep)
    hwarm t cutoff

end Arlib.MarkovChains

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory Arlib.MarkovChains

/-- At one step, forgetting the proper-proposal mark recovers exactly the
kernel executed by Figure 1. -/
theorem map_snd_lazyProperProposalGaussianAux_figureOne
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) (x : AmbientSpace q.n) :
    (lazyProperProposalGaussianAux (truncatedBody q I)
      (truncatedBody_measurable q I) (figureOneProposalRadius q sigma2)
      sigma2 x).map Prod.snd =
        truncatedMetropolisKernel q I oracle sigma2 x := by
  rw [map_snd_lazyProperProposalGaussianAux_apply,
    truncatedMetropolisKernel_eq_lazy_metropolisGaussian q I oracle hsigma2]

/-- At every deterministic raw time, the marked construction has exactly the
same state law as the executable Figure-1 trajectory. -/
theorem map_state_eval_lazyProperProposalGaussianLift_figureOne
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (p : Bool × AmbientSpace q.n) (a : ℕ) :
    (pathMeasure
        (lazyProperProposalGaussianLift (truncatedBody q I)
          (truncatedBody_measurable q I) (figureOneProposalRadius q sigma2)
          sigma2)
        (Measure.dirac p)).map (fun omega => (omega a).2) =
      (pathMeasure (truncatedMetropolisKernel q I oracle sigma2)
        (Measure.dirac p.2)).map (fun omega => omega a) := by
  rw [map_state_eval_pathMeasure_lazyProperProposalGaussianLift]
  induction a with
  | zero =>
      rw [map_eval_pathMeasure_zero, map_eval_pathMeasure_zero]
  | succ a ih =>
      rw [map_eval_pathMeasure_succ, map_eval_pathMeasure_succ, ih]
      apply Measure.bind_congr_right
      filter_upwards with x
      exact congrArg (fun P : Kernel (AmbientSpace q.n) (AmbientSpace q.n) => P x)
        (truncatedMetropolisKernel_eq_lazy_metropolisGaussian
          q I oracle hsigma2) |>.symm

end ArlibCommunity.Algorithms.CV18
