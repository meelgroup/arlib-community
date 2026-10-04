import Nfa.Analysis.SpiritLaw
import Nfa.Model.Prior
import Nfa.Analysis.SpiritBlockMoment
import Nfa.Analysis.StarBadLeSpirit
import Nfa.Analysis.MedianAmplify

/-!
# Lemma bound_proba_AND_event: loose blocks rarely coincide

`bound_proba_AND_event` is Lemma bound_proba_AND_event (analysis.tex:416-421, proof
sketch analysis.tex:422-456, full proof analysis.tex:538-719): in the spirited
algorithm `N^s`, at a state `q ∈ Q^i` (`i ≥ 1`) and for any set `F` of blocks, all the
blocks of `F` are *loose* — `Y_{q,b} ∉ (1 ± ε/2)|L(q)|` — with probability at most
`(4(n+1)/((1−ε)ε²β))^{|F|} ≤ 6^{-|F|}`.

The law of `(Y_{q,b})_b` in `N^s` is `spiritMeans` (the run of `N^s` up to `q`, then the
`hat S^r(q)` draws).  Loose is read as "outside the closed interval", which is the
smaller event than `|Y − L| ≥ (ε/2)L`, so the bound is implied by the paper's.

Paper route: Markov on `∏_{b ∈ F} (Y_{q,b} − |L(q)|)²` with threshold `(ε|L(q)|/2)^{2|F|}`;
the expectation is computed by the tower rule down the layers (lemmas
expectation_of_singleton, expectation_of_pair, expectation_of_C_A_terms,
analysis.tex:221-370), using the spirit's floor `p(q') ≥ (1−ε)/|L(q')|` for `q' ≺ q`
(the "dominated by" step), and is at most `((n+1)|L(q)|²/(β(1−ε)))^{|F|}` by the
derivation-path count `|D(w,i)|·|L(q^w_i)| = |L(q)|` (derivationpath.tex:197-206).
With `β ≥ 64n/(ε²(1−ε))` and `n ≥ 1` the ratio is `≤ (n+1)/(16n) ≤ 1/8 ≤ 1/6`.
-/

set_option autoImplicit false

namespace Nfa.Analysis

open Nfa.Pseudocode

/-- **Lemma bound_proba_AND_event** (analysis.tex:416-421): in `N^s` with the paper's
parameters, at the `k`-th listed state `q^i` of `corePairs A n`, every block of `F` is
loose with probability at most `6^{-|F|}`.

PAPER: analysis.tex:416-421 (statement), analysis.tex:422-456 and 538-719 (proof).
Stated at the paper's final bound `1/6^{|F|}`; loose is `Y ∉ [(1−ε/2)L, (1+ε/2)L]`. -/
theorem bound_proba_AND_event (hprior : Nfa.Prior) {Q : Type} [Fintype Q] [LinearOrder Q]
    (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (n : ℕ) (ε δ : ℝ)
    (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε < 1) (k i : ℕ) (q : Q)
    (hx : (corePairs A n)[k]? = some (i, q)) (F : Finset (Fin (Nfa.params A n ε δ).γ)) :
    (spiritMeans A σ (Nfa.params A n ε δ) ε n k i q).toOuterMeasure
      {Y | ∀ b ∈ F, Y b ∉
        Set.Icc ((1 - ε / 2) * (langCount A i q : ℝ)) ((1 + ε / 2) * (langCount A i q : ℝ))}
      ≤ (1 / 6) ^ F.card := by
  set L := (langCount A i q : ℝ)
  have hxmem : (i, q) ∈ corePairs A n := List.mem_of_getElem? hx
  have hL : 0 < L := by
    have := (StarBadLeSpiritAux.mem_corePairs A n i q).1 hxmem
    exact Nat.cast_pos.2 (StarBadLeSpiritAux.langCount_pos' A i q this.2.2)
  -- `β ε² (1−ε) ≥ 64 n`
  have hβ : 64 * (n : ℝ) ≤ ((Nfa.params A n ε δ).β : ℝ) * (ε ^ 2 * (1 - ε)) := by
    have h1 : 64 * (n : ℝ) / (ε ^ 2 * (1 - ε)) ≤ ((Nfa.params A n ε δ).β : ℝ) := Nat.le_ceil _
    have h2 : 0 < ε ^ 2 * (1 - ε) := by have : 0 < 1 - ε := by linarith
                                        positivity
    rwa [div_le_iff₀ h2] at h1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hβpos : 0 < ((Nfa.params A n ε δ).β : ℝ) := by
    have : 0 < ((Nfa.params A n ε δ).β : ℝ) * (ε ^ 2 * (1 - ε)) := by linarith
    exact pos_of_mul_pos_left this (by have : 0 < 1 - ε := by linarith
                                       positivity)
  set c : ℝ := (ε * L / 2) ^ 2
  have hc : 0 < c := by positivity
  set M : ℝ := (n + 1) * L ^ 2 / ((1 - ε) * ((Nfa.params A n ε δ).β : ℝ))
  have hM : 0 ≤ M := by have : 0 < 1 - ε := by linarith
                        positivity
  -- the ratio `M / c = 4(n+1)/((1−ε)ε²β) ≤ 1/6`
  have hratio : M / c ≤ 1 / 6 := by
    have h1ε : 0 < 1 - ε := by linarith
    rw [div_le_iff₀ hc, div_le_iff₀ (by positivity)]
    have hL2 : 0 < L ^ 2 := by positivity
    have : (n + 1 : ℝ) * 24 ≤ ((Nfa.params A n ε δ).β : ℝ) * (ε ^ 2 * (1 - ε)) := by linarith
    have key : (n + 1 : ℝ) * L ^ 2 * 24 ≤ ((Nfa.params A n ε δ).β : ℝ) * (ε ^ 2 * (1 - ε)) * L ^ 2 := by
      nlinarith
    simp only [c]
    nlinarith
  -- Markov on `∏_{b ∈ F} (Y_b − L)²` (eq. geq_component)
  have hmarkov := MedianAmplifyAux.mul_toOuterMeasure_le
    (spiritMeans A σ (Nfa.params A n ε δ) ε n k i q)
    {Y | ∀ b ∈ F, Y b ∉ Set.Icc ((1 - ε / 2) * L) ((1 + ε / 2) * L)}
    (ENNReal.ofReal (c ^ F.card))
    (fun Y => ENNReal.ofReal (∏ b ∈ F, (Y b - L) ^ 2)) (by
      intro Y hY
      apply ENNReal.ofReal_le_ofReal
      rw [← Finset.prod_const]
      refine Finset.prod_le_prod (fun _ _ => hc.le) fun b hb => ?_
      have hout := hY b hb
      simp only [Set.mem_Icc, not_and_or, not_le] at hout
      have habs : ε * L / 2 < |Y b - L| := by
        rcases hout with h | h
        · rw [abs_of_neg (by nlinarith)]; nlinarith
        · rw [abs_of_pos (by nlinarith)]; nlinarith
      rw [← sq_abs (Y b - L)]
      exact pow_le_pow_left₀ (by positivity) habs.le 2)
  have hmom := spirit_block_moment_le hprior A σ n ε δ hn hε0 hε1 k i q hx F
  have hcF : ENNReal.ofReal (c ^ F.card) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  calc (spiritMeans A σ (Nfa.params A n ε δ) ε n k i q).toOuterMeasure
        {Y | ∀ b ∈ F, Y b ∉ Set.Icc ((1 - ε / 2) * L) ((1 + ε / 2) * L)}
      ≤ ENNReal.ofReal (M ^ F.card) / ENNReal.ofReal (c ^ F.card) := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hcF) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
        exact hmarkov.trans hmom
    _ = ENNReal.ofReal ((M / c) ^ F.card) := by
        rw [← ENNReal.ofReal_div_of_pos (by positivity)]
        exact congrArg ENNReal.ofReal (div_pow M c _).symm
    _ ≤ ENNReal.ofReal ((1 / 6) ^ F.card) :=
        ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (div_nonneg hM hc.le) hratio _)
    _ = (1 / 6) ^ F.card := by
        rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num

end Nfa.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · the child `spirit_block_moment_le` is now proved (SpiritBlockMoment.lean)
* r1 · proved from child · Markov (eq. geq_component) + `β ≥ 64n/(ε²(1−ε))`; moment bound
  `spirit_block_moment_le` open
* r1 · open · stated for `proba_p_star` (via `spiritLooseProb_le`); handed off as the crux
-/
