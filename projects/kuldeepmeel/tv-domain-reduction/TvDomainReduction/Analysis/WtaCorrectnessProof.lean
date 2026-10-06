import TvDomainReduction.Model.Prior
import TvDomainReduction.Model.Run
import TvDomainReduction.Meta.ModelClosure
import TvDomainReduction.Analysis.CorrectnessProof
import TvDomainReduction.Analysis.SpaceProof
import TvDomainReduction.Analysis.TimeProof
import TvDomainReduction.Analysis.MixtureCorrectnessProof
import TvDomainReduction.Analysis.MixtureTimeProof
import TvDomainReduction.Interface.Encoding
import TvDomainReduction.Interface.Pseudocode
import TvDomainReduction.Interface.ProgramModel

/-!
Proof-side owner for the accuracy claim of `thm:wta_fpras` (main.tex:996–1034).

The run (`Run.runLawWTA`) is the circuit engine on the *unmodified* automata, read
at the root query `aWTA = (Z_P^{-1}, −Z_Q^{-1})` with `Z` the DP value
`circuitMass`; the paper's unary root gate of weight `Z_R^{-1}` (main.tex:1006) is
folded into that query.  So `pc_fpras_correct_proof` is not cited as a black box
(its hypothesis `∑ₓ f_R(x) = 1` is false for a generic automaton); its argument is
replayed at the query `aWTA`, exactly as `mixture_fpras_correct_proof` does at `wVec`:

* `sum_valP_eq_circuitMass` / `sum_valQ_eq_circuitMass`: the normalisation DP
  computes `Z_R = ∑ₓ f_R(x)` (main.tex:967), by bilinearity, with no sign hypothesis;
* `wta_half_E_eq_dTVwta`: `½ E(Ω, a_TV) = d_TV(P,Q)` (eq:wta-pointwise-difference,
  main.tex:986–991);
* `answerLawWTA_eq`: the run's answer law is the pseudocode's reduction law pushed
  forward along `DtildeWTA` (the DP and query charges change no value);
* then `Reduction.relErr_of_calibrated` on the event that every one of the
  `I = steps C` product regions sparsified, and the union bound
  `reduceLaw_not_sparsifies_le` (the history-dependent, conditional one) for the
  complement, of mass `≤ I · η/I = η`.

The paper's padding and gate expansion (main.tex:1006–1030) are not needed:
arlib's `Circuit.node` is the bilinear gate itself.
-/

set_option autoImplicit false

open TvDomainReduction
open Arlib.Approximation
open Arlib.Computation
open Arlib.KnowledgeCompilation.Probabilistic
open TvDomainReduction.Model.Operations

namespace TvDomainReduction.Analysis

/-- INTERNAL: the normalisation DP is correct on the `P`-block — `circuitMass P j`
equals the sum of gate `j` over all assignments, by bilinearity of each node.
TEXLINE: main.tex:967 -/
theorem sum_valP_eq_circuitMass : {V : Vtree} → {gP gQ : ℕ} → (P : Circuit V gP) →
    (Q : Circuit V gQ) → (j : Fin gP) →
    ∑ x : (CircuitPair.mk P Q).Assign, (CircuitPair.mk P Q).valP x j = circuitMass P j
  | _, _, _, .leaf _, .leaf _, _ => rfl
  | _, _, _, .node lP rP cP, .node lQ rQ cQ, j => by
      have h : ∀ x : (CircuitPair.node (CircuitPair.mk lP lQ) (CircuitPair.mk rP rQ) cP cQ).Assign,
          (CircuitPair.node (CircuitPair.mk lP lQ) (CircuitPair.mk rP rQ) cP cQ).valP x j
            = ∑ p, ∑ q, cP j p q * (CircuitPair.mk lP lQ).valP x.1 p
                * (CircuitPair.mk rP rQ).valP x.2 q :=
        fun x => CircuitPair.valP_node _ _ cP cQ x j
      have e : ∑ x : (CircuitPair.mk (.node lP rP cP) (.node lQ rQ cQ)).Assign,
          (CircuitPair.mk (.node lP rP cP) (.node lQ rQ cQ)).valP x j
          = ∑ x1 : (CircuitPair.mk lP lQ).Assign, ∑ x2 : (CircuitPair.mk rP rQ).Assign,
              ∑ p, ∑ q, cP j p q * (CircuitPair.mk lP lQ).valP x1 p
                * (CircuitPair.mk rP rQ).valP x2 q :=
        (Finset.sum_congr rfl fun x _ => h x).trans (Fintype.sum_prod_type _)
      rw [e]
      show _ = ∑ p, ∑ q, cP j p q * circuitMass lP p * circuitMass rP q
      simp only [← sum_valP_eq_circuitMass lP lQ, ← sum_valP_eq_circuitMass rP rQ,
        Finset.mul_sum, Finset.sum_mul]
      refine (Finset.sum_congr rfl fun x1 _ => Finset.sum_comm.trans
        (Finset.sum_congr rfl fun p _ => Finset.sum_comm)).trans ?_
      refine (Finset.sum_comm.trans (Finset.sum_congr rfl fun p _ => Finset.sum_comm)).trans ?_
      exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => Finset.sum_comm

/-- INTERNAL: the `Q`-block counterpart of `sum_valP_eq_circuitMass`.
TEXLINE: main.tex:967 -/
theorem sum_valQ_eq_circuitMass : {V : Vtree} → {gP gQ : ℕ} → (P : Circuit V gP) →
    (Q : Circuit V gQ) → (j : Fin gQ) →
    ∑ x : (CircuitPair.mk P Q).Assign, (CircuitPair.mk P Q).valQ x j = circuitMass Q j
  | _, _, _, .leaf _, .leaf _, _ => rfl
  | _, _, _, .node lP rP cP, .node lQ rQ cQ, j => by
      have h : ∀ x : (CircuitPair.node (CircuitPair.mk lP lQ) (CircuitPair.mk rP rQ) cP cQ).Assign,
          (CircuitPair.node (CircuitPair.mk lP lQ) (CircuitPair.mk rP rQ) cP cQ).valQ x j
            = ∑ p, ∑ q, cQ j p q * (CircuitPair.mk lP lQ).valQ x.1 p
                * (CircuitPair.mk rP rQ).valQ x.2 q :=
        fun x => CircuitPair.valQ_node _ _ cP cQ x j
      have e : ∑ x : (CircuitPair.mk (.node lP rP cP) (.node lQ rQ cQ)).Assign,
          (CircuitPair.mk (.node lP rP cP) (.node lQ rQ cQ)).valQ x j
          = ∑ x1 : (CircuitPair.mk lP lQ).Assign, ∑ x2 : (CircuitPair.mk rP rQ).Assign,
              ∑ p, ∑ q, cQ j p q * (CircuitPair.mk lP lQ).valQ x1 p
                * (CircuitPair.mk rP rQ).valQ x2 q :=
        (Finset.sum_congr rfl fun x _ => h x).trans (Fintype.sum_prod_type _)
      rw [e]
      show _ = ∑ p, ∑ q, cQ j p q * circuitMass lQ p * circuitMass rQ q
      simp only [← sum_valQ_eq_circuitMass lP lQ, ← sum_valQ_eq_circuitMass rP rQ,
        Finset.mul_sum, Finset.sum_mul]
      refine (Finset.sum_congr rfl fun x1 _ => Finset.sum_comm.trans
        (Finset.sum_congr rfl fun p _ => Finset.sum_comm)).trans ?_
      refine (Finset.sum_comm.trans (Finset.sum_congr rfl fun p _ => Finset.sum_comm)).trans ?_
      exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => Finset.sum_comm

/-- PAPER: main.tex:986–991 — eq:wta-pointwise-difference: `⟨a_TV, Φ_r(x)⟩ = P(x) − Q(x)`,
so half the exact root functional at `a_TV = (Z_P^{-1}, −Z_Q^{-1})` is `d_TV(P,Q)`. -/
theorem wta_half_E_eq_dTVwta {V : Vtree} (C : CircuitPair V 1 1)
    (hPnn : ∀ x : C.Assign, 0 ≤ C.valP x 0 / wtaZP C)
    (hPs : ∑ x : C.Assign, C.valP x 0 / wtaZP C = 1)
    (hQnn : ∀ x : C.Assign, 0 ≤ C.valQ x 0 / wtaZQ C)
    (hQs : ∑ x : C.Assign, C.valQ x 0 / wtaZQ C = 1) :
    (1 / 2) * C.toRegion.exactWPS.E (aWTA C) = dTVwta C hPnn hPs hQnn hQs := by
  have hZP : circuitMass C.P 0 = wtaZP C := (sum_valP_eq_circuitMass C.P C.Q 0).symm
  have hZQ : circuitMass C.Q 0 = wtaZQ C := (sum_valQ_eq_circuitMass C.P C.Q 0).symm
  rw [dTVwta, Arlib.Probability.FinDist.tvDist_apply, Region.exactWPS, WPS.E_exact]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  simp only [dot, Fintype.sum_sum_type, aWTA, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_one,
    hZP, hZQ, neg_mul, ← sub_eq_add_neg]
  simp [wtaDistP, wtaDistQ, CircuitPair.valP, CircuitPair.valQ, div_eq_inv_mul]

/-- INTERNAL: the WTA run leaves behind exactly the construction `build` does — the
normalisation DP and the query entries are charges only, carrying no value.
TEXLINE: main.tex:967 -/
theorem runWTA_val {V : Vtree} (C : CircuitPair V 1 1) {δ η' : ℝ}
    (prior : SparsifyPrior δ η') (t : Program.Tape prior) :
    (Program.runWTA C prior t).val = Interface.built prior C.P C.Q t := by
  simp [Program.runWTA, Program.runDense, Interface.built]
  rfl

/-- INTERNAL: the bridge for the WTA run's output law — the answer law is the
pseudocode's bottom-up reduction law pushed forward along `DtildeWTA`.
TEXLINE: main.tex:996-1034 -/
theorem answerLawWTA_eq {V : Vtree} (C : CircuitPair V 1 1) {δ η' : ℝ}
    (prior : SparsifyPrior δ η') :
    Run.answerLawWTA C prior = (Pseudocode.runLaw C prior).map (DtildeWTA C) := by
  rw [Pseudocode.runLaw, Run.answerLawWTA, Run.runLawWTA, PMF.map_comp,
    ← tapeLaw_map_built prior C.P C.Q]
  refine Eq.trans ?_ (PMF.map_comp (p := Run.tapeLaw prior C.P C.Q)
    (f := Interface.built prior C.P C.Q) (DtildeWTA C)).symm
  refine congrArg (fun f => PMF.map f (Run.tapeLaw prior C.P C.Q)) (funext fun t => ?_)
  simp only [Function.comp_apply, runWTA_val]
  rfl

end TvDomainReduction.Analysis

/-- Proof-side owner for `TvDomainReduction.wta_fpras_correct`; its statement is fixed by the proof charter.
PAPER: main.tex:1005-1032 -/
theorem TvDomainReduction.Analysis.wta_fpras_correct_proof (hprior : Prior) {V : Vtree} (C : CircuitPair V 1 1) (hPnn : ∀ x : C.Assign, 0 ≤ C.valP x 0 / wtaZP C) (hPs : ∑ x : C.Assign, C.valP x 0 / wtaZP C = 1) (hQnn : ∀ x : C.Assign, 0 ≤ C.valQ x 0 / wtaZQ C) (hQs : ∑ x : C.Assign, C.valQ x 0 / wtaZQ C = 1) (ε η : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hη0 : 0 < η) (hη1 : η < 1) (hL : 0 < CircuitPair.steps C) (prior : SparsifyPrior (perStepTol ε (CircuitPair.steps C)) (perStepFail η (CircuitPair.steps C))) : 1 - ENNReal.ofReal η ≤ (Run.answerLawWTA C prior).toOuterMeasure (Arlib.relErr ε (dTVwta C hPnn hPs hQnn hQs)) := by
  set E := Arlib.relErr ε (dTVwta C hPnn hPs hQnn hQs)
  rw [answerLawWTA_eq]
  -- On the event that every product region sparsified, `d̂` is within `(1 ± ε)`.
  have hgood : (DtildeWTA C) ⁻¹' Eᶜ
      ⊆ {R : CircuitPair.Reduction C | ¬ R.Sparsifies (perStepTol ε (CircuitPair.steps C))} := by
    intro R hR hS
    apply hR
    have h := Reduction.relErr_of_calibrated R hL hε0.le hε1.le hS (aWTA C)
    show DtildeWTA C R ∈ Arlib.relErr ε (dTVwta C hPnn hPs hQnn hQs)
    rw [← wta_half_E_eq_dTVwta C hPnn hPs hQnn hQs]
    obtain ⟨h1, h2⟩ := h
    show DtildeWTA C R ∈ Set.Icc _ _
    unfold DtildeWTA DtildeAt
    constructor <;> nlinarith
  -- The union bound over the `I` steps.
  have hbad : ((Pseudocode.runLaw C prior).map (DtildeWTA C)).toOuterMeasure Eᶜ
      ≤ ENNReal.ofReal η := by
    rw [PMF.toOuterMeasure_map_apply]
    refine (MeasureTheory.measure_mono hgood).trans ?_
    refine (reduceLaw_not_sparsifies_le prior C.P C.Q :).trans (le_of_eq ?_)
    have hL' : (0 : ℝ) < (CircuitPair.steps C : ℝ) := by exact_mod_cast hL
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1
    show (CircuitPair.steps C : ℝ) * (η / (CircuitPair.steps C : ℝ)) = η
    field_simp
  have hone : 1 ≤ ((Pseudocode.runLaw C prior).map (DtildeWTA C)).toOuterMeasure E
      + ((Pseudocode.runLaw C prior).map (DtildeWTA C)).toOuterMeasure Eᶜ := by
    rw [← (PMF.toOuterMeasure_apply_eq_one_iff _ Set.univ).2 (Set.subset_univ _),
      ← Set.union_compl_self E]
    exact MeasureTheory.measure_union_le _ _
  calc 1 - ENNReal.ofReal η
      ≤ 1 - ((Pseudocode.runLaw C prior).map (DtildeWTA C)).toOuterMeasure Eᶜ :=
        tsub_le_tsub_left hbad _
    _ ≤ _ := tsub_le_iff_right.2 hone

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · via `answerLawWTA_eq`, `wta_half_E_eq_dTVwta` (DP identity `sum_valP/Q_eq_circuitMass`), `relErr_of_calibrated` and the union bound `reduceLaw_not_sparsifies_le`
-/
