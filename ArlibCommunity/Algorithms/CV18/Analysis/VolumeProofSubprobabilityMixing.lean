/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyPhaseMixing

/-!
# Mixing conditioned branches without losing warmness

Rejection sampling splits a warm probability law into subprobability
branches.  Normalizing a branch of mass `p` appears to worsen its warmness by
`1 / p`.  The square-root Lovasz--Simonovits estimate cancels that loss after
the normalized estimate is scaled back by `p`.  This file records the linear
measure identities used by that argument.
-/

open MeasureTheory
open ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open Arlib Arlib.MarkovChains
open scoped ENNReal

/-- Markov iteration is linear in the initial finite mass. -/
theorem iterate_smul_measure
    {S : Type*} [MeasurableSpace S] (P : Kernel S S)
    (c : ENNReal) (mu : Measure S) : forall t : Nat,
    iterate P (c • mu) t = c • iterate P mu t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [iterate_succ, ih, iterate_succ]
      change (c • iterate P mu t).bind P = c • (iterate P mu t).bind P
      exact Measure.bind_smul c _ _

/-- Total variation scales linearly when both finite measures are multiplied
by the same coefficient. -/
theorem Arlib.TVLe.smul_measure
    {S : Type*} [MeasurableSpace S]
    {mu nu : Measure S} {epsilon c : ENNReal}
    (h : TVLe mu nu epsilon) : TVLe (c • mu) (c • nu) (c * epsilon) := by
  intro A hA
  have hleft := h.left hA
  have hright := h.right hA
  simp only [Measure.smul_apply, smul_eq_mul]
  constructor
  · calc
      c * mu A <= c * (nu A + epsilon) := by gcongr
      _ = c * nu A + c * epsilon := mul_add _ _ _
  · calc
      c * nu A <= c * (mu A + epsilon) := by gcongr
      _ = c * mu A + c * epsilon := mul_add _ _ _

/-- A subprobability branch dominated by `M * pi` becomes
`M / p`-warm after normalization, where `p` is its mass. -/
theorem isWarm_normalized_branch
    {S : Type*} [MeasurableSpace S]
    {mu pi : Measure S} {M p : ENNReal}
    (hwarm : IsWarm M mu pi) (hp : p ≠ 0) :
    IsWarm (p⁻¹ * M) (p⁻¹ • mu) pi := by
  intro A hA
  simp only [Measure.smul_apply, smul_eq_mul]
  calc
    p⁻¹ * mu A <= p⁻¹ * (M * pi A) :=
      by gcongr; exact hwarm A hA
    _ = (p⁻¹ * M) * pi A := by ring

/-- Scaling a normalized branch back by its mass recovers the branch. -/
theorem mass_smul_inv_mass_smul
    {S : Type*} [MeasurableSpace S]
    (mu : Measure S) {p : ENNReal} (hp : p ≠ 0) (hptop : p ≠ ⊤) :
    p • (p⁻¹ • mu) = mu := by
  rw [<- smul_assoc]
  simp [ENNReal.mul_inv_cancel hp hptop]

end ArlibCommunity.Algorithms.CV18
