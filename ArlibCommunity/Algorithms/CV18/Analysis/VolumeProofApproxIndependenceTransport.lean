/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofApproxIndependencePerturbation

/-! # Transporting approximate independence through joint-law identities

The CV18 chronological proof establishes Lemma 7.17(c) when a phase is
created, then runs probability kernels for the remaining phases.  Those
kernels preserve the two already-created scalar observables.  The useful
interface is therefore equality of their joint pushforward laws, rather than
pointwise equality on the whole trace space.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory

/-- Approximate independence depends only on the joint pushforward law of its
two observables.  This formulation permits the source and target experiments
to have different sample spaces. -/
theorem ApproxIndepFun.of_map_pair_eq
    {Omega Omega' S T : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Omega']
    [MeasurableSpace S] [MeasurableSpace T]
    {epsilon : ℝ} {mu : Measure Omega} {nu : Measure Omega'}
    {X : Omega → S} {Y : Omega → T}
    {X' : Omega' → S} {Y' : Omega' → T}
    (hX : Measurable X) (hY : Measurable Y)
    (hX' : Measurable X') (hY' : Measurable Y')
    (hlaw : mu.map (fun omega => (X omega, Y omega)) =
      nu.map (fun omega => (X' omega, Y' omega)))
    (h : ApproxIndepFun epsilon X Y mu) :
    ApproxIndepFun epsilon X' Y' nu := by
  intro A hA B hB
  have hpair : Measurable fun omega : Omega => (X omega, Y omega) :=
    hX.prodMk hY
  have hpair' : Measurable fun omega : Omega' => (X' omega, Y' omega) :=
    hX'.prodMk hY'
  have hjoint :
      mu.real (X ⁻¹' A ∩ Y ⁻¹' B) =
        nu.real (X' ⁻¹' A ∩ Y' ⁻¹' B) := by
    have hAB : MeasurableSet (A ×ˢ B) := hA.prod hB
    have hm := congrArg (fun law : Measure (S × T) => law.real (A ×ˢ B)) hlaw
    simp only [measureReal_def] at hm
    rw [Measure.map_apply hpair hAB, Measure.map_apply hpair' hAB] at hm
    have hpre : (fun omega : Omega => (X omega, Y omega)) ⁻¹' (A ×ˢ B) =
        X ⁻¹' A ∩ Y ⁻¹' B := by
      ext omega
      simp
    have hpre' : (fun omega : Omega' => (X' omega, Y' omega)) ⁻¹' (A ×ˢ B) =
        X' ⁻¹' A ∩ Y' ⁻¹' B := by
      ext omega
      simp
    rw [hpre, hpre'] at hm
    simpa only [measureReal_def] using hm
  have hleft : mu.real (X ⁻¹' A) = nu.real (X' ⁻¹' A) := by
    have hAu : MeasurableSet (A ×ˢ (Set.univ : Set T)) :=
      hA.prod MeasurableSet.univ
    have hm := congrArg
      (fun law : Measure (S × T) => law.real (A ×ˢ Set.univ)) hlaw
    simp only [measureReal_def] at hm
    rw [Measure.map_apply hpair hAu, Measure.map_apply hpair' hAu] at hm
    have hpre : (fun omega : Omega => (X omega, Y omega)) ⁻¹'
        (A ×ˢ (Set.univ : Set T)) = X ⁻¹' A := by
      ext omega
      simp
    have hpre' : (fun omega : Omega' => (X' omega, Y' omega)) ⁻¹'
        (A ×ˢ (Set.univ : Set T)) = X' ⁻¹' A := by
      ext omega
      simp
    rw [hpre, hpre'] at hm
    simpa only [measureReal_def] using hm
  have hright : mu.real (Y ⁻¹' B) = nu.real (Y' ⁻¹' B) := by
    have huB : MeasurableSet ((Set.univ : Set S) ×ˢ B) :=
      MeasurableSet.univ.prod hB
    have hm := congrArg
      (fun law : Measure (S × T) => law.real (Set.univ ×ˢ B)) hlaw
    simp only [measureReal_def] at hm
    rw [Measure.map_apply hpair huB, Measure.map_apply hpair' huB] at hm
    have hpre : (fun omega : Omega => (X omega, Y omega)) ⁻¹'
        ((Set.univ : Set S) ×ˢ B) = Y ⁻¹' B := by
      ext omega
      simp
    have hpre' : (fun omega : Omega' => (X' omega, Y' omega)) ⁻¹'
        ((Set.univ : Set S) ×ˢ B) = Y' ⁻¹' B := by
      ext omega
      simp
    rw [hpre, hpre'] at hm
    simpa only [measureReal_def] using hm
  rw [← hjoint, ← hleft, ← hright]
  exact h A hA B hB

/-- Binding a future probability kernel does not change the joint law of two
observables when both observables are almost surely preserved by that kernel.
This is the reusable future-phase step for the loss-preserving CV18 trace. -/
theorem Measure.map_pair_bind_eq_of_ae_eq
    {Omega Omega' S T : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Omega']
    [MeasurableSpace S] [MeasurableSpace T]
    (mu : Measure Omega) (K : Omega → Measure Omega')
    (hK : Measurable K) (hKprob : ∀ omega, IsProbabilityMeasure (K omega))
    (X : Omega → S) (Y : Omega → T)
    (X' : Omega' → S) (Y' : Omega' → T)
    (hX : Measurable X) (hY : Measurable Y)
    (hX' : Measurable X') (hY' : Measurable Y')
    (hpreserve : ∀ᵐ omega ∂mu, ∀ᵐ next ∂K omega,
      X' next = X omega ∧ Y' next = Y omega) :
    (mu.bind K).map (fun next => (X' next, Y' next)) =
      mu.map (fun omega => (X omega, Y omega)) := by
  have hpair : Measurable fun omega : Omega => (X omega, Y omega) :=
    hX.prodMk hY
  have hpair' : Measurable fun next : Omega' => (X' next, Y' next) :=
    hX'.prodMk hY'
  calc
    (mu.bind K).map (fun next => (X' next, Y' next)) =
        mu.bind fun omega =>
          (K omega).map (fun next => (X' next, Y' next)) :=
      map_bind_eq_bind_map_of_measurable mu hK hpair'
    _ = mu.bind fun omega => Measure.dirac (X omega, Y omega) := by
      apply Measure.bind_congr_right
      filter_upwards [hpreserve] with omega homega
      calc
        (K omega).map (fun next => (X' next, Y' next)) =
            (K omega).map (fun _ => (X omega, Y omega)) := by
          apply Measure.map_congr
          filter_upwards [homega] with next hnext
          exact Prod.ext hnext.1 hnext.2
        _ = Measure.dirac (X omega, Y omega) := by
          rw [Measure.map_const, measure_univ, one_smul]
    _ = mu.map (fun omega => (X omega, Y omega)) :=
      Measure.bind_dirac_eq_map mu hpair

/-- Iterating kernels which preserve two observables almost surely preserves
their complete joint law. -/
theorem Measure.map_pair_iteratedKernelLaw_eq_of_ae_eq
    {Omega S T : Type*} [MeasurableSpace Omega]
    [MeasurableSpace S] [MeasurableSpace T]
    (K : ℕ → Omega → Measure Omega)
    (hK : ∀ phase, Measurable (K phase))
    (hKprob : ∀ phase omega, IsProbabilityMeasure (K phase omega))
    (X : Omega → S) (Y : Omega → T)
    (hX : Measurable X) (hY : Measurable Y)
    (hpreserve : ∀ phase omega, ∀ᵐ next ∂K phase omega,
      X next = X omega ∧ Y next = Y omega)
    (mu : Measure Omega) : ∀ steps,
    (iteratedKernelLaw K mu steps).map (fun omega => (X omega, Y omega)) =
      mu.map (fun omega => (X omega, Y omega)) := by
  intro steps
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [iteratedKernelLaw_succ]
      calc
        ((iteratedKernelLaw K mu steps).bind (K steps)).map
            (fun omega => (X omega, Y omega)) =
            (iteratedKernelLaw K mu steps).map
              (fun omega => (X omega, Y omega)) := by
          apply Measure.map_pair_bind_eq_of_ae_eq
            (iteratedKernelLaw K mu steps) (K steps)
              (hK steps) (hKprob steps) X Y X Y hX hY hX hY
          filter_upwards with omega
          exact hpreserve steps omega
        _ = mu.map (fun omega => (X omega, Y omega)) := ih

#print axioms ApproxIndepFun.of_map_pair_eq
#print axioms Measure.map_pair_bind_eq_of_ae_eq
#print axioms Measure.map_pair_iteratedKernelLaw_eq_of_ae_eq

end ArlibCommunity.Algorithms.CV18
