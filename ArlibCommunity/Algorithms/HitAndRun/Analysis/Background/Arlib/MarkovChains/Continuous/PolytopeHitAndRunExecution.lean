/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.PolytopeChord

/-!
# A finite-facet presentation of the hit-and-run proposal

This file turns the measurable facet endpoints from `PolytopeChord` into a parameterized
uniform interval kernel.  It then samples a sphere direction, samples the interval, and
maps `(x, theta, t)` to `x + t • theta`.
-/

namespace Arlib.MarkovChains.PolytopeHitAndRunExecution

open MeasureTheory ProbabilityTheory Set Metric
open Arlib.MarkovChains Arlib.MarkovChains.PolytopeChord
open scoped InnerProductSpace ENNReal Classical

variable {n : Nat} {ι : Type*} [Fintype ι]

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev Direction (n : Nat) := Metric.sphere (0 : State n) 1

/-- Uniform line-parameter law on the interval computed by the finite facet scan. -/
noncomputable def intervalKernel (A : ι → State n) (b : ι → Real) :
    Kernel (State n × State n) Real where
  toFun p := Arlib.uniformOn volume
    (Icc (lower A b p.1 p.2) (upper A b p.1 p.2))
  measurable' := by
    apply Measure.measurable_of_measurable_coe _
    intro T hT
    let S : Set ((State n × State n) × Real) :=
      {q | (q.2 ∈ T ∧ lower A b q.1.1 q.1.2 ≤ q.2) ∧
        q.2 ≤ upper A b q.1.1 q.1.2}
    let U : Set ((State n × State n) × Real) :=
      {q | lower A b q.1.1 q.1.2 ≤ q.2 ∧ q.2 ≤ upper A b q.1.1 q.1.2}
    have hS : MeasurableSet S := by
      exact (hT.preimage measurable_snd).inter
        (measurableSet_le ((measurable_lower A b).comp measurable_fst) measurable_snd) |>.inter
        (measurableSet_le measurable_snd ((measurable_upper A b).comp measurable_fst))
    have hU : MeasurableSet U := by
      exact (measurableSet_le ((measurable_lower A b).comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd ((measurable_upper A b).comp measurable_fst))
    have hnum : Measurable (fun p => volume {t | (p, t) ∈ S}) :=
      measurable_measure_prodMk_left hS
    have hden : Measurable (fun p => volume {t | (p, t) ∈ U}) :=
      measurable_measure_prodMk_left hU
    have hquot := hnum.div hden
    convert hquot using 1
    funext p
    rw [Arlib.uniformOn_apply volume measurableSet_Icc hT]
    congr 1
    · congr 1
      ext t
      simp only [S, mem_inter_iff, mem_Icc, mem_setOf_eq]
      tauto
theorem intervalKernel_apply (A : ι → State n) (b : ι → Real)
    (p : State n × State n) :
    intervalKernel A b p = Arlib.uniformOn volume
      (Icc (lower A b p.1 p.2) (upper A b p.1 p.2)) := rfl

instance (A : ι → State n) (b : ι → Real) : IsFiniteKernel (intervalKernel A b) := by
  refine ⟨1, ENNReal.one_lt_top, fun p => ?_⟩
  rw [intervalKernel_apply, Arlib.uniformOn_def, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  exact ENNReal.inv_mul_le_one _

/-- Keep the starting point while drawing an independent sphere direction. -/
noncomputable def startDirectionKernel : Kernel (State n) (State n × Direction n) :=
  Kernel.prod Kernel.id (Kernel.const (State n) (unifSphere n))

instance [NeZero n] : IsMarkovKernel (startDirectionKernel (n := n)) := by
  unfold startDirectionKernel
  infer_instance

instance : IsFiniteKernel (startDirectionKernel (n := n)) := by
  unfold startDirectionKernel
  infer_instance

/-- The interval kernel with the subtype direction coerced to the ambient vector. -/
noncomputable def subtypeIntervalKernel (A : ι → State n) (b : ι → Real) :
    Kernel (State n × Direction n) Real :=
  Kernel.comap (intervalKernel A b)
    (fun p => (p.1, (p.2 : State n)))
    (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))

instance (A : ι → State n) (b : ι → Real) :
    IsFiniteKernel (subtypeIntervalKernel A b) := by
  unfold subtypeIntervalKernel
  infer_instance

instance (A : ι → State n) (b : ι → Real) :
    IsFiniteKernel (Kernel.prodMkLeft (State n) (subtypeIntervalKernel A b)) := by
  infer_instance

/-- Joint law of start, direction, and line parameter. -/
noncomputable def lineDrawKernel (A : ι → State n) (b : ι → Real) :
    Kernel (State n) ((State n × Direction n) × Real) :=
  Kernel.compProd startDirectionKernel
    (Kernel.prodMkLeft (State n) (subtypeIntervalKernel A b))

/-- Map a finite-facet line draw to its endpoint. -/
def lineEndpoint (q : (State n × Direction n) × Real) : State n :=
  q.1.1 + q.2 • (q.1.2 : State n)

theorem measurable_lineEndpoint : Measurable (lineEndpoint (n := n)) := by
  exact (continuous_fst.comp continuous_fst).add
    (continuous_snd.smul (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))) |>.measurable

/-- For a fixed start, the direction-indexed mapped interval law is a kernel. -/
noncomputable def directionEndpointKernel (A : ι → State n) (b : ι → Real)
    (x : State n) : Kernel (Direction n) (State n) where
  toFun theta := Measure.map (fun t : Real => x + t • (theta : State n))
    (Arlib.uniformOn volume (Icc (lower A b x theta) (upper A b x theta)))
  measurable' := by
    let pull : Direction n → State n × State n := fun theta => (x, (theta : State n))
    let base : Kernel (Direction n) Real := Kernel.comap (intervalKernel A b) pull (by fun_prop)
    let joint : Kernel (Direction n) (Direction n × Real) :=
      Kernel.compProd Kernel.id (Kernel.prodMkLeft (Direction n) base)
    let out : Direction n × Real → State n := fun q => x + q.2 • (q.1 : State n)
    have hout : Measurable out := by fun_prop
    have hmap : Measurable fun theta => Kernel.map joint out theta := Kernel.measurable _
    convert hmap using 1
    funext theta
    ext T hT
    rw [Kernel.map_apply joint hout, Measure.map_apply hout hT]
    dsimp only [joint]
    rw [Kernel.compProd_apply (hT.preimage hout)]
    simp only [Kernel.id_apply, Kernel.prodMkLeft_apply, base, Kernel.comap_apply,
      intervalKernel_apply]
    rw [lintegral_dirac theta, Measure.map_apply (by fun_prop) hT]
    rfl

theorem directionEndpointKernel_apply (A : ι → State n) (b : ι → Real)
    (x : State n) (theta : Direction n) :
    directionEndpointKernel A b x theta =
      Measure.map (fun t : Real => x + t • (theta : State n))
        (Arlib.uniformOn volume (Icc (lower A b x theta) (upper A b x theta))) := rfl

/-- The finite-facet proposal kernel. -/
noncomputable def finiteFacetProposal (A : ι → State n) (b : ι → Real) :
    Kernel (State n) (State n) :=
  Kernel.map (lineDrawKernel A b) lineEndpoint

theorem finiteFacetProposal_apply
    (A : ι → State n) (b : ι → Real) (x : State n) :
    finiteFacetProposal A b x =
      (unifSphere n).bind (fun theta =>
        Measure.map (fun t : Real => x + t • (theta : State n))
          (Arlib.uniformOn volume
            (Icc (lower A b x theta) (upper A b x theta)))) := by
  ext T hT
  rw [finiteFacetProposal, Kernel.map_apply _ measurable_lineEndpoint,
    Measure.map_apply measurable_lineEndpoint hT,
    lineDrawKernel, Kernel.compProd_apply (hT.preimage measurable_lineEndpoint),
    Measure.bind_apply hT
      ((Kernel.aemeasurable (directionEndpointKernel A b x)).congr
        (Filter.Eventually.of_forall fun theta => directionEndpointKernel_apply A b x theta))]
  simp only [startDirectionKernel, Kernel.prod_apply, Kernel.id_apply,
    Kernel.const_apply, Kernel.prodMkLeft_apply]
  rw [lintegral_prod _
    ((Kernel.measurable_kernel_prodMk_left
      (hT.preimage measurable_lineEndpoint)).aemeasurable)]
  simp only [subtypeIntervalKernel, Kernel.comap_apply, intervalKernel_apply]
  rw [lintegral_dirac x]
  apply lintegral_congr
  intro theta
  rw [Measure.map_apply (by fun_prop) hT]
  rfl

theorem finiteFacetProposal_univ_le_one
    (A : ι → State n) (b : ι → Real) (x : State n) :
    finiteFacetProposal A b x Set.univ ≤ 1 := by
  rw [finiteFacetProposal_apply, Measure.bind_apply MeasurableSet.univ
    ((Kernel.aemeasurable (directionEndpointKernel A b x)).congr
      (Filter.Eventually.of_forall fun theta => directionEndpointKernel_apply A b x theta))]
  calc
    (∫⁻ theta, Measure.map (fun t : Real => x + t • (theta : State n))
          (Arlib.uniformOn volume (Icc (lower A b x theta) (upper A b x theta))) Set.univ
        ∂unifSphere n) ≤ ∫⁻ _theta, 1 ∂unifSphere n := by
      apply lintegral_mono
      intro theta
      change Measure.map (fun t : Real => x + t • (theta : State n))
        (Arlib.uniformOn volume (Icc (lower A b x theta) (upper A b x theta))) Set.univ ≤ 1
      rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, preimage_univ,
        Arlib.uniformOn_def, Measure.smul_apply, smul_eq_mul,
        Measure.restrict_apply MeasurableSet.univ, univ_inter]
      exact ENNReal.inv_mul_le_one _
    _ = unifSphere n Set.univ := by simp
    _ ≤ 1 := unifSphere_univ_le_one n

/-- On a bounded polytope, the finite-facet proposal is exactly the existing denotational
hit-and-run proposal at every point of the body. -/
theorem finiteFacetProposal_eq_hitAndRunProposal
    (A : ι → State n) (b : ι → Real)
    (hK : Bornology.IsBounded (Arlib.Polytope.body A b))
    (x : State n) (hx : x ∈ Arlib.Polytope.body A b) [NeZero n] :
    finiteFacetProposal A b x = hitAndRunProposal (Arlib.Polytope.body A b) x := by
  ext T hT
  rw [finiteFacetProposal_apply, hitAndRunProposal_apply_uniformOn
    (Arlib.Polytope.measurableSet_body A b) x hT]
  rw [Measure.bind_apply hT
    ((Kernel.aemeasurable (directionEndpointKernel A b x)).congr
      (Filter.Eventually.of_forall fun theta => directionEndpointKernel_apply A b x theta))]
  apply lintegral_congr
  intro theta
  have htheta : (theta : State n) ≠ 0 := by
    intro hz
    have hnorm := theta.property
    simp [mem_sphere, dist_zero_right, hz] at hnorm
  rw [Measure.map_apply (by fun_prop) hT,
    chordSet_eq_Icc_of_isBounded hK hx htheta]
  rfl

/-! ## Completed Markov kernel -/

/-- Add the usual stay-put deficit to the finite-facet proposal. -/
noncomputable def finiteFacetHitAndRunAux (A : ι → State n) (b : ι → Real) :
    Kernel (State n) (State n) where
  toFun x := finiteFacetProposal A b x +
    (1 - finiteFacetProposal A b x Set.univ) • Measure.dirac x
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun T hT => ?_
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hT]
    exact (Kernel.measurable_coe (finiteFacetProposal A b) hT).add
      ((measurable_const.sub (Kernel.measurable_coe (finiteFacetProposal A b)
        MeasurableSet.univ)).mul ((measurable_one.indicator hT)))

theorem finiteFacetHitAndRunAux_apply (A : ι → State n) (b : ι → Real)
    (x : State n) :
    finiteFacetHitAndRunAux A b x = finiteFacetProposal A b x +
      (1 - finiteFacetProposal A b x Set.univ) • Measure.dirac x := rfl

instance (A : ι → State n) (b : ι → Real) :
    IsMarkovKernel (finiteFacetHitAndRunAux A b) := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [finiteFacetHitAndRunAux_apply, Measure.add_apply, Measure.smul_apply,
    smul_eq_mul, Measure.dirac_apply' _ MeasurableSet.univ]
  simp only [mem_univ, indicator_of_mem, Pi.one_apply, mul_one]
  exact add_tsub_cancel_of_le (finiteFacetProposal_univ_le_one A b x)

/-- Use the finite facet scan on the body.  Outside the body we retain the existing
totalized kernel; this branch is unreachable for a trajectory started in the body and it
makes the equality of kernels global rather than merely support-relative. -/
noncomputable def finiteFacetHitAndRun (A : ι → State n) (b : ι → Real) :
    Kernel (State n) (State n) :=
  Kernel.piecewise (Arlib.Polytope.measurableSet_body A b)
    (finiteFacetHitAndRunAux A b) (hitAndRun (Arlib.Polytope.body A b))

instance (A : ι → State n) (b : ι → Real) :
    IsMarkovKernel (finiteFacetHitAndRun A b) := by
  unfold finiteFacetHitAndRun
  infer_instance

/-- The finite-facet completed kernel is extensionally the repository's hit-and-run
kernel on every input. -/
theorem finiteFacetHitAndRun_eq_hitAndRun
    (A : ι → State n) (b : ι → Real)
    (hK : Bornology.IsBounded (Arlib.Polytope.body A b)) [NeZero n] :
    finiteFacetHitAndRun A b = hitAndRun (Arlib.Polytope.body A b) := by
  ext x T hT
  by_cases hx : x ∈ Arlib.Polytope.body A b
  · rw [finiteFacetHitAndRun, Kernel.piecewise_apply, if_pos hx,
      finiteFacetHitAndRunAux_apply,
      hitAndRun_apply_set (Arlib.Polytope.measurableSet_body A b) x hT,
      Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hT]
    rw [finiteFacetProposal_eq_hitAndRunProposal A b hK x hx]
  · rw [finiteFacetHitAndRun, Kernel.piecewise_apply, if_neg hx]

#print axioms finiteFacetHitAndRun_eq_hitAndRun

#print axioms intervalKernel_apply
#print axioms finiteFacetProposal_apply
#print axioms finiteFacetProposal_eq_hitAndRunProposal

end Arlib.MarkovChains.PolytopeHitAndRunExecution
