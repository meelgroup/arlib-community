import TvDomainReduction.Model.Prior
import TvDomainReduction.Model.Run
import TvDomainReduction.Meta.ModelClosure
import TvDomainReduction.Analysis.CorrectnessProof
import TvDomainReduction.Analysis.SpaceProof
import TvDomainReduction.Analysis.TimeProof
import TvDomainReduction.Interface.Encoding
import TvDomainReduction.Interface.Pseudocode
import TvDomainReduction.Interface.ProgramModel

/-!
Proof-side owner for claim (1) of `thm:main_fptas` (main.tex:788–795), the
accuracy claim for mixtures of product distributions.

The proof follows main.tex:842–848.  On the event `Reduction.Sparsifies (ε/(3n))`
— every one of the `n − 1` product regions of the caterpillar sparsified — the
monotonicity step `sparsifies_mono` lifts it to the calibrated tolerance
`ε/(3(n−1))`, `Reduction.relErr_of_calibrated` puts the root functional at `w`
within `(1 ± ε)` of the exact one, and `mixPair_half_E_eq_dTVmix` (`F_0 = d_TV`)
identifies half the exact one with `dTVmix`.  The complementary event has mass at
most `(n − 1) · η/n ≤ η` by the union bound `reduceLaw_not_sparsifies_le`.
`answerLawMix_eq` transports `Run.answerLawMix` to the pseudocode's law.
`lem:propagation` is not restated: it is one node of `Reduction.embeds_exact`.
-/

set_option autoImplicit false

namespace TvDomainReduction.Analysis

open Arlib.Approximation
open Arlib.Computation
open Arlib.KnowledgeCompilation.Probabilistic

/-- INTERNAL: the caterpillar over the first `t + 1` coordinates has `t` product
regions, so `(mixPair M).steps = M.n − 1` (one sparsification per internal region,
leaves kept exact).
TEXLINE: main.tex:888 -/
theorem catPair_steps (M : MixtureInstance) : ∀ t : ℕ, CircuitPair.steps (catPair M t) = t
  | 0 => rfl
  | t + 1 => by
      show (catPair M t).steps + 0 + 1 = t + 1
      rw [catPair_steps M t]

/-- INTERNAL: the compiled caterpillar computes the paper's accumulated feature on the
`P`-block, `R_{≤t} = R_{≤t-1} ⊙ r_t` — the obligation recorded as decision 5 of
`Model/Prelude.lean`.
TEXLINE: main.tex:720-722 -/
theorem catPair_valP (M : MixtureInstance) :
    ∀ (t : ℕ) (x : (catPair M t).Assign) (i : Fin M.k1),
      (catPair M t).valP x i = prefixFeatP M t x i
  | 0, _, _ => rfl
  | t + 1, x, i => by
      show tensorFeat (blockTensor (diagTensor (Fin M.k1)) (diagTensor (Fin M.k2)))
        ((catPair M t).Phi x.1)
        ((fun a => Sum.elim (fun j => M.pTab (t+1) j a) (fun j => M.qTab (t+1) j a)) x.2)
        (Sum.inl i) = prefixFeatP M t x.1 i * M.pTab (t + 1) i x.2
      rw [← catPair_valP M t x.1 i]
      simp only [tensorFeat, Fintype.sum_sum_type, blockTensor, zero_mul,
        Finset.sum_const_zero, add_zero, diagTensor, CircuitPair.valP, Sum.elim_inl]
      rw [Finset.sum_eq_single i (fun b _ hb => Finset.sum_eq_zero fun c _ => by simp [hb])
        (by simp), Finset.sum_eq_single i (fun c _ hc => by simp [hc]) (by simp)]
      simp

/-- INTERNAL: the `Q`-block counterpart of `catPair_valP`.
TEXLINE: main.tex:720-722 -/
theorem catPair_valQ (M : MixtureInstance) :
    ∀ (t : ℕ) (x : (catPair M t).Assign) (i : Fin M.k2),
      (catPair M t).valQ x i = prefixFeatQ M t x i
  | 0, _, _ => rfl
  | t + 1, x, i => by
      show tensorFeat (blockTensor (diagTensor (Fin M.k1)) (diagTensor (Fin M.k2)))
        ((catPair M t).Phi x.1)
        ((fun a => Sum.elim (fun j => M.pTab (t+1) j a) (fun j => M.qTab (t+1) j a)) x.2)
        (Sum.inr i) = prefixFeatQ M t x.1 i * M.qTab (t + 1) i x.2
      rw [← catPair_valQ M t x.1 i]
      simp only [tensorFeat, Fintype.sum_sum_type, blockTensor, zero_mul,
        Finset.sum_const_zero, zero_add, diagTensor, CircuitPair.valQ, Sum.elim_inr]
      rw [Finset.sum_eq_single i (fun b _ hb => Finset.sum_eq_zero fun c _ => by simp [hb])
        (by simp), Finset.sum_eq_single i (fun c _ hc => by simp [hc]) (by simp)]
      simp

/-- PAPER: main.tex:730-733 — `d_TV(P,Q) = ½ ∑ₓ |wᵀ R(x)|`, i.e. `F_0 = d_TV(P,Q)`
(main.tex:821): half the exact root functional at the query `w = (+α, −β)` is the
total variation distance between the two mixtures. -/
theorem mixPair_half_E_eq_dTVmix (M : MixtureInstance)
    (hPnn : ∀ x, 0 ≤ mixPmfP M x) (hPs : ∑ x, mixPmfP M x = 1)
    (hQnn : ∀ x, 0 ≤ mixPmfQ M x) (hQs : ∑ x, mixPmfQ M x = 1) :
    (1 / 2) * (mixPair M).toRegion.exactWPS.E (wVec M) = dTVmix M hPnn hPs hQnn hQs := by
  rw [dTVmix, Arlib.Probability.FinDist.tvDist_apply, Region.exactWPS, WPS.E_exact]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  simp only [dot, Fintype.sum_sum_type, wVec, Sum.elim_inl, Sum.elim_inr, neg_mul,
    Finset.sum_neg_distrib, ← sub_eq_add_neg]
  have hP : ∀ i, (mixPair M).toRegion.Phi x (Sum.inl i) = mixFeatP M x i :=
    fun i => catPair_valP M (M.n - 1) x i
  have hQ : ∀ i, (mixPair M).toRegion.Phi x (Sum.inr i) = mixFeatQ M x i :=
    fun i => catPair_valQ M (M.n - 1) x i
  simp only [hP, hQ]
  rfl

/-- INTERNAL: `Reduction.Sparsifies` is monotone in the tolerance — a `(1 ± δ)`
embedding at every product region is a `(1 ± δ')` one for `δ ≤ δ'`.  Needed because
the run uses `δ = ε/(3n)` over `n − 1` steps, below the calibrated `ε/(3(n−1))`.
TEXLINE: main.tex:842-848 -/
theorem sparsifies_mono {δ δ' : ℝ} (h : δ ≤ δ') {d : Type} [instd : Fintype d] {S : Region d}
    (R : Reduction S) (hR : R.Sparsifies δ) : R.Sparsifies δ' := by
  revert instd hR
  induction R with
  | leaf X Φ => intro _ _; trivial
  | @node dl dr instl instr dd l r M Rl Rr ι instι C ihl ihr =>
      intro instd hR
      obtain ⟨hl, hr, hC⟩ := hR
      exact ⟨@ihl instl hl, @ihr instr hr, Embeds.mono (by linarith) (by linarith) hC⟩

/-- INTERNAL: the bridge for Algorithm 1's output law — `runDense` returns the same
construction as `build`, so the answer law is the pseudocode's bottom-up reduction
law pushed forward along `DtildeMix`.
TEXLINE: main.tex:763-784 -/
theorem answerLawMix_eq (M : MixtureInstance) {δ η' : ℝ} (prior : SparsifyPrior δ η') :
    Run.answerLawMix M prior
      = (Pseudocode.runLaw (mixPair M) prior).map (DtildeMix M) := by
  rw [Pseudocode.runLaw, Run.answerLawMix, Run.runLawMix, PMF.map_comp,
    ← tapeLaw_map_built prior (mixPair M).P (mixPair M).Q]
  exact (PMF.map_comp (p := Run.tapeLaw prior (mixPair M).P (mixPair M).Q)
    (f := Interface.built prior (mixPair M).P (mixPair M).Q) (DtildeMix M)).symm

/-- Proof-side owner for `TvDomainReduction.mixture_fpras_correct`; its statement is fixed by the proof charter.
PAPER: main.tex:842-848 -/
theorem mixture_fpras_correct_proof (hprior : Prior) (M : MixtureInstance) (hM : M.IsStochastic) (hPnn : ∀ x, 0 ≤ mixPmfP M x) (hPs : ∑ x, mixPmfP M x = 1) (hQnn : ∀ x, 0 ≤ mixPmfQ M x) (hQs : ∑ x, mixPmfQ M x = 1) (ε η : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hη0 : 0 < η) (hη1 : η < 1) (hn : 2 ≤ M.n) (prior : SparsifyPrior (perStepTol ε M.n) (perStepFail η M.n)) : 1 - ENNReal.ofReal η ≤ (Run.answerLawMix M prior).toOuterMeasure (Arlib.relErr ε (dTVmix M hPnn hPs hQnn hQs)) := by
  set E := Arlib.relErr ε (dTVmix M hPnn hPs hQnn hQs)
  rw [answerLawMix_eq]
  have hsteps : (mixPair M).toRegion.steps = M.n - 1 := catPair_steps M (M.n - 1)
  have hL : 0 < (mixPair M).toRegion.steps := by rw [hsteps]; omega
  have hcast : (((M.n - 1 : ℕ) : ℝ)) = (M.n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hn2 : (2 : ℝ) ≤ (M.n : ℝ) := by exact_mod_cast hn
  -- `δ = ε/(3n)` is below the calibrated tolerance `ε/(3(n−1))` for the `n − 1` steps.
  have htol : perStepTol ε M.n ≤ ε / (3 * ((mixPair M).toRegion.steps : ℝ)) := by
    rw [hsteps, hcast, perStepTol]
    exact div_le_div_of_nonneg_left hε0.le (by linarith) (by linarith)
  have hgood : (DtildeMix M) ⁻¹' Eᶜ
      ⊆ {R : CircuitPair.Reduction (mixPair M) | ¬ R.Sparsifies (perStepTol ε M.n)} := by
    intro R hR hS
    apply hR
    have h := Reduction.relErr_of_calibrated R hL hε0.le hε1.le
      (sparsifies_mono htol R hS) (wVec M)
    show DtildeMix M R ∈ Arlib.relErr ε (dTVmix M hPnn hPs hQnn hQs)
    rw [← mixPair_half_E_eq_dTVmix M hPnn hPs hQnn hQs]
    obtain ⟨h1, h2⟩ := h
    show DtildeMix M R ∈ Set.Icc _ _
    unfold DtildeMix DtildeAt
    constructor <;> nlinarith
  have hbad : ((Pseudocode.runLaw (mixPair M) prior).map (DtildeMix M)).toOuterMeasure Eᶜ ≤ ENNReal.ofReal η := by
    rw [PMF.toOuterMeasure_map_apply]
    refine (MeasureTheory.measure_mono hgood).trans ?_
    refine (reduceLaw_not_sparsifies_le prior (mixPair M).P (mixPair M).Q :).trans ?_
    have hst : (pairRegion (mixPair M).P (mixPair M).Q).steps = M.n - 1 := hsteps
    rw [hst, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hcast, perStepFail]
    have hn0 : (0 : ℝ) < M.n := by linarith
    rw [mul_div_assoc', div_le_iff₀ hn0]
    nlinarith
  have hone : 1 ≤ ((Pseudocode.runLaw (mixPair M) prior).map (DtildeMix M)).toOuterMeasure E
      + ((Pseudocode.runLaw (mixPair M) prior).map (DtildeMix M)).toOuterMeasure Eᶜ := by
    rw [← (PMF.toOuterMeasure_apply_eq_one_iff _ Set.univ).2 (Set.subset_univ _),
      ← Set.union_compl_self E]
    exact MeasureTheory.measure_union_le _ _
  calc 1 - ENNReal.ofReal η
      ≤ 1 - ((Pseudocode.runLaw (mixPair M) prior).map (DtildeMix M)).toOuterMeasure Eᶜ :=
        tsub_le_tsub_left hbad _
    _ ≤ _ := tsub_le_iff_right.2 hone

end TvDomainReduction.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · via `answerLawMix_eq`, `sparsifies_mono`, `relErr_of_calibrated`, `mixPair_half_E_eq_dTVmix` and the union bound `reduceLaw_not_sparsifies_le`
-/
