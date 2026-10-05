/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofProperMarkedTrajectory

/-!
# The stopped proper-proposal trajectory

This file starts the finite-cylinder construction of the proper-proposal stopped chain.  Its
first ingredient is a generic exact cylinder formula: hold at a point for `k` transitions and
then enter a measurable set.  Applied to the lifted proper-proposal kernel, it identifies the
law of every possible first-proper-proposal cylinder.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ## A terminal-set refinement of the geometric holding-time formula -/

section TerminalCylinder

variable {Om : Type*} [MeasurableSpace Om] [MeasurableSingletonClass Om]

/-- The exact probability of holding at `x` through time `k` and then entering `s`. -/
theorem pathMeasure_dirac_holdsUntil_then_mem (P : Kernel Om Om) [IsMarkovKernel P]
    (x : Om) (k : ℕ) {s : Set Om} (hs : MeasurableSet s) :
    pathMeasure P (Measure.dirac x)
        {ω : ℕ → Om | (∀ i ≤ k, ω i = x) ∧ ω (k + 1) ∈ s}
      = (P x {x}) ^ k * P x s := by
  rw [pathMeasure]
  let ν : Measure (ℕ → Om) :=
    Kernel.trajMeasure (X := fun _ : ℕ => Om) (Measure.dirac x) (chainKernel P)
  let H : Set ((_i : ↥(Finset.Iic k)) → Om) := {h | ∀ i, h i = x}
  have hH : MeasurableSet H := measurableSet_constHistory x k
  have hjoint := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ : ℕ => Om) (μ₀ := Measure.dirac x) (κ := chainKernel P) (a := k)
  have happ := congrArg
    (fun m : Measure (((_i : ↥(Finset.Iic k)) → Om) × Om) => m (H ×ˢ s)) hjoint
  rw [Measure.compProd_apply_prod hH hs,
    Measure.map_apply (by fun_prop) (hH.prod hs)] at happ
  have hL :
      ∫⁻ h in H, (chainKernel P k) h s ∂(ν.map (Preorder.frestrictLe k)) =
        P x s * ν.map (Preorder.frestrictLe k) H := by
    rw [setLIntegral_congr_fun (g := fun _ => P x s) hH (fun h hh => by
      simp only [chainKernel_apply]
      rw [hh ⟨k, Finset.mem_Iic.2 le_rfl⟩]), setLIntegral_const, mul_comm]
  have hR :
      (fun ω : ℕ → Om => (Preorder.frestrictLe k ω, ω (k + 1))) ⁻¹' (H ×ˢ s) =
        {ω : ℕ → Om | (∀ i ≤ k, ω i = x) ∧ ω (k + 1) ∈ s} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_setOf_eq, H,
      Preorder.frestrictLe_apply]
    constructor
    · rintro ⟨hconst, hnext⟩
      exact ⟨fun i hi => hconst ⟨i, Finset.mem_Iic.2 hi⟩, hnext⟩
    · rintro ⟨hconst, hnext⟩
      exact ⟨fun i => hconst i.1 (Finset.mem_Iic.1 i.2), hnext⟩
  have hmu : ν.map (Preorder.frestrictLe k) H = (P x {x}) ^ k := by
    rw [Measure.map_apply (Preorder.measurable_frestrictLe k) hH]
    change pathMeasure P (Measure.dirac x)
      ((Preorder.frestrictLe k) ⁻¹'
        {h : (_i : ↥(Finset.Iic k)) → Om | ∀ i, h i = x}) = _
    rw [preimage_frestrictLe_constHistory]
    exact pathMeasure_dirac_holdsUntil P x k
  rw [hL, hR, hmu] at happ
  rw [← happ, mul_comm]

end TerminalCylinder

/-! ## First proper-proposal cylinders -/

variable {n : ℕ}

/-- Exactly `j` improper proposals from `x`, followed by a proper proposal whose resulting
state lies in `t`. -/
def firstProperCylinder (x : EuclideanSpace ℝ (Fin n))
    (t : Set (EuclideanSpace ℝ (Fin n))) (j : ℕ) :
    Set (ℕ → Bool × EuclideanSpace ℝ (Fin n)) :=
  {ω | (∀ i ≤ j, ω i = (false, x)) ∧ ω (j + 1) ∈ ({true} ×ˢ t)}

theorem measurableSet_firstProperCylinder (x : EuclideanSpace ℝ (Fin n))
    {t : Set (EuclideanSpace ℝ (Fin n))} (ht : MeasurableSet t) (j : ℕ) :
    MeasurableSet (firstProperCylinder x t j) := by
  exact (measurableSet_holdsUntil (false, x) j).inter
    ((measurable_pi_apply (j + 1)) (measurableSet_singleton true |>.prod ht))

/-- Exact mass of a first-proper-proposal cylinder. -/
theorem pathMeasure_firstProperCylinder
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (δ s : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) {t : Set (EuclideanSpace ℝ (Fin n))}
    (ht : MeasurableSet t) (j : ℕ) :
    pathMeasure (properProposalGaussianLift K hK δ s) (Measure.dirac (false, x))
        (firstProperCylinder x t j) =
      (1 - ell K δ x) ^ j *
        (ell K δ x * speedyMetropolisGaussian K δ s x t) := by
  rw [firstProperCylinder, pathMeasure_dirac_holdsUntil_then_mem _ _ _
      (measurableSet_singleton true |>.prod ht),
    properProposalGaussianLift_apply_false_singleton hK δ s,
    properProposalGaussianLift_apply_true_prod hK δ s (p := (false, x)) (t := t) ht]

/-- First-proper-proposal cylinders with different waiting times are disjoint. -/
theorem pairwise_disjoint_firstProperCylinder (x : EuclideanSpace ℝ (Fin n))
    (t : Set (EuclideanSpace ℝ (Fin n))) :
    Pairwise (Function.onFun Disjoint (firstProperCylinder x t)) := by
  intro i j hij
  apply Set.disjoint_left.2
  intro ω hi hj
  rcases hi with ⟨hiHold, hiTrue⟩
  rcases hj with ⟨hjHold, hjTrue⟩
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hfalse := hjHold (i + 1) (Nat.succ_le_of_lt hijlt)
    have htrue : (ω (i + 1)).1 = true := by
      exact hiTrue.1
    have : (ω (i + 1)).1 = false := by simpa using congrArg Prod.fst hfalse
    simp_all
  · have hfalse := hiHold (j + 1) (Nat.succ_le_of_lt hjilt)
    have htrue : (ω (j + 1)).1 = true := by
      exact hjTrue.1
    have : (ω (j + 1)).1 = false := by simpa using congrArg Prod.fst hfalse
    simp_all

/-- Summing over every possible number of preceding improper proposals gives exactly one
speedy transition.  The hypothesis `ell(x) ≠ 0` says that a proper proposal eventually occurs
almost surely. -/
theorem pathMeasure_iUnion_firstProperCylinder
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (δ s : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) {t : Set (EuclideanSpace ℝ (Fin n))}
    (ht : MeasurableSet t) (hell : ell K δ x ≠ 0) :
    pathMeasure (properProposalGaussianLift K hK δ s) (Measure.dirac (false, x))
        (⋃ j : ℕ, firstProperCylinder x t j) =
      speedyMetropolisGaussian K δ s x t := by
  rw [measure_iUnion (pairwise_disjoint_firstProperCylinder x t)
      (measurableSet_firstProperCylinder x ht)]
  simp_rw [pathMeasure_firstProperCylinder hK δ s x ht]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric,
    ENNReal.sub_sub_cancel ENNReal.one_ne_top (ell_le_one K δ x),
    ← mul_assoc, ENNReal.inv_mul_cancel hell
      (ne_top_of_le_ne_top ENNReal.one_ne_top (ell_le_one K δ x)), one_mul]

/-! ## Identification with the first marked stopping time -/

/-- If the first true mark is at transition `j`, its marked hitting time is `j+1`. -/
theorem markedTime_one_eq_succ_of_first_true {mark : ℕ → Bool} {j : ℕ}
    (hbefore : ∀ i < j, mark i = false) (hat : mark j = true) :
    markedTime mark 1 = j + 1 := by
  have hzero : ∀ t ≤ j, markedCount mark t = 0 := by
    intro t ht
    induction t with
    | zero => rfl
    | succ t ih =>
        rw [markedCount_succ_of_false (hbefore t (by omega)), ih (by omega)]
  have hone : markedCount mark (j + 1) = 1 := by
    rw [markedCount_succ_of_true hat, hzero j le_rfl]
  have hex : ∃ t, 1 ≤ markedCount mark t := ⟨j + 1, by rw [hone]⟩
  apply le_antisymm (markedTime_le (by rw [hone]))
  by_contra hlt
  have htime : markedTime mark 1 ≤ j := by omega
  have hc := markedCount_markedTime hex
  rw [hzero (markedTime mark 1) htime] at hc
  omega

/-- On the event that some first proper proposal occurs, stopping `markedChain` at mark `1`
selects exactly the terminal state of its unique first-proper cylinder. -/
theorem iUnion_firstProperCylinder_eq_inter_markedChain
    (x : EuclideanSpace ℝ (Fin n)) (t : Set (EuclideanSpace ℝ (Fin n))) :
    (⋃ j : ℕ, firstProperCylinder x t j) =
      (⋃ j : ℕ, firstProperCylinder x Set.univ j) ∩
        {ω | markedChain (fun q => (ω q).2) (fun q => (ω (q + 1)).1) 1 ∈ t} := by
  ext ω
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hjHold, hjTerm⟩
    have htime : markedTime (fun q => (ω (q + 1)).1) 1 = j + 1 :=
      markedTime_one_eq_succ_of_first_true
        (fun i hi => by
          have hp := hjHold (i + 1) (by omega)
          simpa using congrArg Prod.fst hp)
        hjTerm.1
    refine ⟨⟨j, hjHold, ?_⟩, ?_⟩
    · exact ⟨hjTerm.1, Set.mem_univ _⟩
    · rw [markedChain_apply, htime]
      exact hjTerm.2
  · rintro ⟨⟨j, hjHold, hjTerm⟩, hmem⟩
    have htime : markedTime (fun q => (ω (q + 1)).1) 1 = j + 1 :=
      markedTime_one_eq_succ_of_first_true
        (fun i hi => by
          have hp := hjHold (i + 1) (by omega)
          simpa using congrArg Prod.fst hp)
        hjTerm.1
    refine ⟨j, hjHold, hjTerm.1, ?_⟩
    rw [markedChain_apply, htime] at hmem
    exact hmem

/-- **One stopped transition is exactly one speedy transition.**  This is the first genuine
random-time law: take the actual lifted Metropolis trajectory, stop at its first proper mark,
and forget the mark.  Its state has exactly the speedy Gaussian Metropolis law. -/
theorem map_first_markedChain_pathMeasure_properProposalGaussianLift
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (δ s : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (hell : ell K δ x ≠ 0) :
    (pathMeasure (properProposalGaussianLift K hK δ s) (Measure.dirac (false, x))).map
        (fun ω => markedChain (fun q => (ω q).2) (fun q => (ω (q + 1)).1) 1) =
      speedyMetropolisGaussian K δ s x := by
  let μ := pathMeasure (properProposalGaussianLift K hK δ s) (Measure.dirac (false, x))
  let stop : (ℕ → Bool × EuclideanSpace ℝ (Fin n)) → EuclideanSpace ℝ (Fin n) :=
    fun ω => markedChain (fun q => (ω q).2) (fun q => (ω (q + 1)).1) 1
  have hstate : Measurable
      (fun ω : ℕ → Bool × EuclideanSpace ℝ (Fin n) => fun q => (ω q).2) :=
    measurable_pi_lambda _ fun q => measurable_snd.comp (measurable_pi_apply q)
  have hmark : Measurable
      (fun ω : ℕ → Bool × EuclideanSpace ℝ (Fin n) => fun q => (ω (q + 1)).1) :=
    measurable_pi_lambda _ fun q => measurable_fst.comp (measurable_pi_apply (q + 1))
  have hstop : Measurable stop :=
    (measurable_markedChain 1).comp (hstate.prodMk hmark)
  ext t ht
  rw [Measure.map_apply hstop ht]
  let U : Set (ℕ → Bool × EuclideanSpace ℝ (Fin n)) :=
    ⋃ j : ℕ, firstProperCylinder x Set.univ j
  have hU : μ U = μ Set.univ := by
    calc
      μ U = speedyMetropolisGaussian K δ s x Set.univ := by
        exact pathMeasure_iUnion_firstProperCylinder hK δ s x MeasurableSet.univ hell
      _ = 1 := measure_univ
      _ = μ Set.univ := measure_univ.symm
  have hUtop : μ U ≠ ∞ := by rw [hU, measure_univ]; exact ENNReal.one_ne_top
  have hinter := Measure.measure_inter_eq_of_measure_eq (hstop ht) hU
    (Set.subset_univ U) hUtop
  change μ (stop ⁻¹' t) = _
  calc
    μ (stop ⁻¹' t) = μ (U ∩ stop ⁻¹' t) := by
      simpa only [Set.univ_inter] using hinter.symm
    _ = μ (⋃ j : ℕ, firstProperCylinder x t j) := by
      rw [iUnion_firstProperCylinder_eq_inter_markedChain]
      rfl
    _ = speedyMetropolisGaussian K δ s x t :=
      pathMeasure_iUnion_firstProperCylinder hK δ s x ht hell

/-! ## The stopped experiment as a Markov kernel -/

/-- State selected by the first proper mark of a lifted path. -/
noncomputable def firstProperMarkedState
    (ω : ℕ → Bool × EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  markedChain (fun q => (ω q).2) (fun q => (ω (q + 1)).1) 1

theorem measurable_firstProperMarkedState :
    Measurable (firstProperMarkedState (n := n)) := by
  have hstate : Measurable
      (fun ω : ℕ → Bool × EuclideanSpace ℝ (Fin n) => fun q => (ω q).2) :=
    measurable_pi_lambda _ fun q => measurable_snd.comp (measurable_pi_apply q)
  have hmark : Measurable
      (fun ω : ℕ → Bool × EuclideanSpace ℝ (Fin n) => fun q => (ω (q + 1)).1) :=
    measurable_pi_lambda _ fun q => measurable_fst.comp (measurable_pi_apply (q + 1))
  exact (measurable_markedChain 1).comp (hstate.prodMk hmark)

/-- Kernel from an initial position to the whole lifted marked trajectory. -/
noncomputable def properProposalTrajectoryKernel
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K) (δ s : ℝ) :
    Kernel (EuclideanSpace ℝ (Fin n)) (ℕ → Bool × EuclideanSpace ℝ (Fin n)) :=
  Kernel.comap
    (Kernel.traj (X := fun _ : ℕ => Bool × EuclideanSpace ℝ (Fin n))
      (chainKernel (properProposalGaussianLift K hK δ s)) 0)
    (fun x (_ : ↥(Finset.Iic 0)) => (false, x))
    (measurable_pi_lambda _ fun _ => measurable_const.prodMk measurable_id)

instance isMarkovKernel_properProposalTrajectoryKernel
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K) (δ s : ℝ) :
    IsMarkovKernel (properProposalTrajectoryKernel K hK δ s) := by
  rw [properProposalTrajectoryKernel]
  infer_instance

/-- Run ordinary lifted Metropolis transitions until the first proper proposal and output its
state.  This is a Markov kernel because the stopped-state map is measurable. -/
noncomputable def properProposalStoppedKernel
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K) (δ s : ℝ) :
    Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
  Kernel.map (properProposalTrajectoryKernel K hK δ s) firstProperMarkedState

instance isMarkovKernel_properProposalStoppedKernel
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K) (δ s : ℝ) :
    IsMarkovKernel (properProposalStoppedKernel K hK δ s) := by
  rw [properProposalStoppedKernel]
  exact Kernel.IsMarkovKernel.map _ measurable_firstProperMarkedState

/-- Applying the trajectory kernel at `x` is the `pathMeasure` used above. -/
theorem properProposalTrajectoryKernel_apply
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K) (δ s : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    properProposalTrajectoryKernel K hK δ s x =
      pathMeasure (properProposalGaussianLift K hK δ s) (Measure.dirac (false, x)) := by
  rw [properProposalTrajectoryKernel, Kernel.comap_apply, pathMeasure,
    Kernel.trajMeasure, Measure.map_dirac]
  rw [Measure.dirac_bind (Kernel.measurable _) ]
  congr 2

/-- At every non-stuck point, applying the stopped kernel is exactly a speedy transition. -/
theorem properProposalStoppedKernel_apply_eq_speedy
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (δ s : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (hell : ell K δ x ≠ 0) :
    properProposalStoppedKernel K hK δ s x = speedyMetropolisGaussian K δ s x := by
  rw [properProposalStoppedKernel,
    Kernel.map_apply _ measurable_firstProperMarkedState,
    properProposalTrajectoryKernel_apply]
  exact map_first_markedChain_pathMeasure_properProposalGaussianLift hK δ s x hell

/-- Total version of the stopped kernel.  On the measurable set of points where no proper
proposal can ever occur, it uses the speedy kernel's prescribed parked behavior; elsewhere it
runs the actual lifted Metropolis trajectory until the first proper proposal. -/
noncomputable def properProposalStoppedKernelTotal
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K) (δ s : ℝ) :
    Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) := by
  classical
  exact Kernel.piecewise (measurableSet_stuckPoints hK δ)
    (speedyMetropolisGaussian K δ s) (properProposalStoppedKernel K hK δ s)

instance isMarkovKernel_properProposalStoppedKernelTotal
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K) (δ s : ℝ) :
    IsMarkovKernel (properProposalStoppedKernelTotal K hK δ s) := by
  classical
  rw [properProposalStoppedKernelTotal]
  infer_instance

/-- The total stopped-experiment kernel is exactly the speedy Gaussian kernel. -/
theorem properProposalStoppedKernelTotal_eq_speedy
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (δ s : ℝ) :
    properProposalStoppedKernelTotal K hK δ s = speedyMetropolisGaussian K δ s := by
  classical
  ext x
  rw [properProposalStoppedKernelTotal, Kernel.piecewise_apply]
  split_ifs with hx
  · rfl
  · rw [properProposalStoppedKernel_apply_eq_speedy hK δ s x (by
      simpa only [StuckPoints, Set.mem_setOf_eq] using hx)]

/-- Consequently, every finite iterate of independently restarted stopped experiments is
exactly the corresponding speedy-chain iterate. -/
theorem iterate_properProposalStoppedKernelTotal_eq_speedy
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (δ s : ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (t : ℕ) :
    iterate (properProposalStoppedKernelTotal K hK δ s) μ t =
      iterate (speedyMetropolisGaussian K δ s) μ t := by
  rw [properProposalStoppedKernelTotal_eq_speedy hK δ s]

end Arlib.MarkovChains

#print axioms Arlib.MarkovChains.pathMeasure_dirac_holdsUntil_then_mem
#print axioms Arlib.MarkovChains.pathMeasure_firstProperCylinder
#print axioms Arlib.MarkovChains.pathMeasure_iUnion_firstProperCylinder
#print axioms Arlib.MarkovChains.map_first_markedChain_pathMeasure_properProposalGaussianLift
#print axioms Arlib.MarkovChains.properProposalStoppedKernel_apply_eq_speedy
#print axioms Arlib.MarkovChains.properProposalStoppedKernelTotal_eq_speedy
#print axioms Arlib.MarkovChains.iterate_properProposalStoppedKernelTotal_eq_speedy
