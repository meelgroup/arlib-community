import TvDomainReduction.Model.Prior
import TvDomainReduction.Model.Run
import TvDomainReduction.Meta.ModelClosure
import TvDomainReduction.Interface.Encoding
import TvDomainReduction.Interface.Pseudocode
import TvDomainReduction.Interface.ProgramModel
import TvDomainReduction.Analysis.ReduceLawNotSparsifiesLe

/-!
Proof-side owner for claim (1) of Theorem 4.1, the accuracy claim.

The frontier it is to be proved from is imported above: the `Interface/` ladder
(`TvDomainReduction.answerLaw_eq` at the top of it) transports the program's
answer law to the pseudocode's, and arlib's `Reduction.embeds_exact` and
`Reduction.relErr_of_calibrated` supply the propagation invariant and the
`δ = ε/(3L)` calibration.

The proof follows main.tex:926–927.  On the event `Reduction.Sparsifies (ε/(3L))`
— every product region sparsified — `relErr_of_calibrated` puts the root
functional within `(1 ± ε)` of the exact one, and `exactRoot_half_E_eq_dTV`
identifies half of the exact one with `d_TV`, so `D̃ ∈ relErr ε d_TV`.  The
complementary event has mass at most `L · η/L = η` by the union bound
`reduceLaw_not_sparsifies_le`.
-/

set_option autoImplicit false

namespace TvDomainReduction.Analysis

open Arlib.Approximation
open Arlib.Computation
open Arlib.KnowledgeCompilation.Probabilistic

/-- Proof-side owner for `TvDomainReduction.pc_fpras_correct`; its statement is fixed by the proof charter.
PAPER: main.tex:926–927 -/
theorem pc_fpras_correct_proof (hprior : Prior)
    {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ) (jP : Fin gP) (jQ : Fin gQ)
    (hPnn : ∀ x : C.Assign, 0 ≤ C.valP x jP) (hPs : ∑ x : C.Assign, C.valP x jP = 1)
    (hQnn : ∀ x : C.Assign, 0 ≤ C.valQ x jQ) (hQs : ∑ x : C.Assign, C.valQ x jQ = 1)
    (ε η : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hL : 0 < CircuitPair.steps C)
    (prior : SparsifyPrior (perStepTol ε (CircuitPair.steps C))
      (perStepFail η (CircuitPair.steps C))) :
    1 - ENNReal.ofReal η
      ≤ (Run.answerLaw C prior jP jQ).toOuterMeasure
          (Arlib.relErr ε (dTV C jP jQ hPnn hPs hQnn hQs)) := by
  set E := Arlib.relErr ε (dTV C jP jQ hPnn hPs hQnn hQs)
  rw [TvDomainReduction.answerLaw_eq C prior (fun _ => prior.draw₀) jP jQ]
  -- On the event that every product region sparsified, `D̃` is within `(1 ± ε)`.
  have hgood : (fun R : CircuitPair.Reduction C => Dtilde R jP jQ) ⁻¹' Eᶜ
      ⊆ {R | ¬ R.Sparsifies (perStepTol ε (CircuitPair.steps C))} := by
    intro R hR hS
    apply hR
    have h := Reduction.relErr_of_calibrated R hL hε0.le hε1.le hS (aTV jP jQ)
    show Dtilde R jP jQ ∈ Arlib.relErr ε (dTV C jP jQ hPnn hPs hQnn hQs)
    rw [← exactRoot_half_E_eq_dTV C jP jQ hPnn hPs hQnn hQs]
    obtain ⟨h1, h2⟩ := h
    show Dtilde R jP jQ ∈ Set.Icc _ _
    unfold Dtilde
    constructor <;> nlinarith
  -- The union bound over the `L` steps.
  have hbad : (Pseudocode.answerLaw C prior jP jQ).toOuterMeasure Eᶜ ≤ ENNReal.ofReal η := by
    rw [Pseudocode.answerLaw, PMF.toOuterMeasure_map_apply]
    refine (MeasureTheory.measure_mono hgood).trans ?_
    refine (reduceLaw_not_sparsifies_le prior C.P C.Q).trans (le_of_eq ?_)
    have hL' : (0 : ℝ) < (CircuitPair.steps C : ℝ) := by exact_mod_cast hL
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1
    show (CircuitPair.steps C : ℝ) * (η / (CircuitPair.steps C : ℝ)) = η
    field_simp
  have hone : 1 ≤ (Pseudocode.answerLaw C prior jP jQ).toOuterMeasure E
      + (Pseudocode.answerLaw C prior jP jQ).toOuterMeasure Eᶜ := by
    rw [← (PMF.toOuterMeasure_apply_eq_one_iff _ Set.univ).2 (Set.subset_univ _),
      ← Set.union_compl_self E]
    exact MeasureTheory.measure_union_le _ _
  calc 1 - ENNReal.ofReal η
      ≤ 1 - (Pseudocode.answerLaw C prior jP jQ).toOuterMeasure Eᶜ := tsub_le_tsub_left hbad _
    _ ≤ _ := tsub_le_iff_right.2 hone

end TvDomainReduction.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · via `answerLaw_eq`, `relErr_of_calibrated`, `exactRoot_half_E_eq_dTV` and the union bound `reduceLaw_not_sparsifies_le`
-/
