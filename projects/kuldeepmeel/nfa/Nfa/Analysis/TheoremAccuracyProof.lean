import Nfa.Meta.ModelClosure
import Nfa.Model.Run
import Nfa.Model.Prior
import Arlib.Prelude
import Nfa.Interface.Encoding
import Nfa.Interface.Pseudocode
import Nfa.Interface.ProgramModel
import Nfa.Analysis.CoreRunFailLe
import Nfa.Analysis.MedianAmplify

/-!
# Accuracy of `countNFA` (theorem:main_result, first half)

The proof of analysis.tex:61-66.  The measured output is rewritten to the
pseudocode's `countOutput` (`output_eq_countOutput`).  On an empty slice the
algorithm returns `0 = |ℒ_n(𝒜)|`.  Otherwise it returns the median of
`μ = ⌈8 ln(1/δ)⌉` independent core-run estimates; each fails with probability at
most `1/4` (`coreRun_fail_le`, Lemma main_result_core), so the median fails with
probability at most `exp(−μ/8) ≤ δ` (`median_amplify`).
-/

namespace Nfa.Analysis

/-- On an empty slice (`q_F ∉ Q^n`) no word of length `n` is accepted.

INTERNAL: the pre.empty branch of `countNFA` returns `0`, which is `|ℒ_n(𝒜)|`
only through this fact.
TEXLINE: algorithm.tex:4 -/
theorem sliceCount_eq_zero_of_not_nonempty {Q : Type} [Fintype Q] [LinearOrder Q]
    (A : Nfa.PaperNFA Q) (n : ℕ) (h : ¬ Nfa.Pseudocode.nonemptySlice A n) :
    Nfa.sliceCount A n = 0 := by
  by_contra hne
  obtain ⟨w, hwlen, hwacc⟩ := Set.nonempty_of_ncard_ne_zero hne
  apply h
  obtain ⟨q, hq, hqw⟩ := hwacc
  have hqF : q = A.qF := hq
  subst hqF
  unfold Nfa.Pseudocode.nonemptySlice Nfa.Pseudocode.layerSet
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨w, hwlen, hqw⟩

end Nfa.Analysis

/-- Proof-side owner for `Nfa.countNFA_correct`; its statement is fixed by the proof charter.

PAPER: introduction.tex:88-95 (theorem:main_result, accuracy), proof analysis.tex:61-66. -/
theorem Nfa.Analysis.countNFA_correct_proof (hprior : Nfa.Prior) {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (n : ℕ) (ε δ : ℝ) (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) : 1 - δ ≤ ((Nfa.Run.output A σ n ε δ).toOuterMeasure (Arlib.relErr ε (Nfa.sliceCount A n : ℝ))).toReal := by
  rw [(Nfa.output_eq_countOutput A σ n ε δ).2]
  unfold Nfa.Pseudocode.countOutput Nfa.Pseudocode.countNFA
  classical
  set S : Set ℝ := Arlib.relErr ε (Nfa.sliceCount A n : ℝ) with hS
  by_cases hne : Nfa.Pseudocode.nonemptySlice A n
  · rw [if_pos hne]
    set P := Nfa.params A n ε δ with hP
    set D := (Nfa.Pseudocode.drawAll (fun _ => Nfa.Pseudocode.coreRun A σ P n) 0
      (List.range P.μ)).map fun ests => Arlib.Probability.medianOf fun j : Fin P.μ => ests j
    have hcore := coreRun_fail_le hprior A σ n ε δ hn hε0 hε1 hne
    have hamp := median_amplify (Nfa.Pseudocode.coreRun A σ P n) _ _ hcore P.μ
    -- `exp(−μ/8) ≤ δ` from `μ = ⌈8 ln(1/δ)⌉`
    have hμ : 8 * Real.log (1 / δ) ≤ (P.μ : ℝ) := Nat.le_ceil _
    have hexp : Real.exp (-(P.μ : ℝ) / 8) ≤ δ := by
      have h1 : -(P.μ : ℝ) / 8 ≤ Real.log δ := by
        rw [one_div, Real.log_inv] at hμ
        linarith
      calc Real.exp (-(P.μ : ℝ) / 8) ≤ Real.exp (Real.log δ) := Real.exp_le_exp.2 h1
        _ = δ := Real.exp_log hδ0
    have hmeas : MeasurableSet S := measurableSet_Icc
    have hcompl : D.toOuterMeasure Sᶜ ≤ ENNReal.ofReal δ :=
      hamp.trans (ENNReal.ofReal_le_ofReal hexp)
    have hsum : D.toOuterMeasure S = 1 - D.toOuterMeasure Sᶜ := by
      rw [← D.toMeasure_apply_eq_toOuterMeasure_apply hmeas,
        ← D.toMeasure_apply_eq_toOuterMeasure_apply hmeas.compl,
        MeasureTheory.prob_compl_eq_one_sub hmeas, ENNReal.sub_sub_cancel ENNReal.one_ne_top
          MeasureTheory.prob_le_one]
    rw [hsum]
    have hle : 1 - ENNReal.ofReal δ ≤ 1 - D.toOuterMeasure Sᶜ := tsub_le_tsub_left hcompl 1
    calc 1 - δ = (1 - ENNReal.ofReal δ).toReal := by
          rw [ENNReal.toReal_sub_of_le (ENNReal.ofReal_le_one.2 hδ1.le) ENNReal.one_ne_top,
            ENNReal.toReal_ofReal hδ0.le, ENNReal.toReal_one]
      _ ≤ (1 - D.toOuterMeasure Sᶜ).toReal :=
          ENNReal.toReal_mono (ENNReal.sub_ne_top ENNReal.one_ne_top) hle
  · rw [if_neg hne, PMF.toOuterMeasure_pure_apply]
    have h0 : (0 : ℝ) ∈ S := by
      rw [hS, sliceCount_eq_zero_of_not_nonempty A n hne]
      simp
    rw [if_pos h0, ENNReal.toReal_one]
    linarith

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved from children · assembled from `coreRun_fail_le` (open) and `median_amplify` (proved)
-/
