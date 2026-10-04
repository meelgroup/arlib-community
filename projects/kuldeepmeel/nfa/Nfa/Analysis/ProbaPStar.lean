import Nfa.Analysis.CoreLawStar
import Nfa.Model.Prior
import Nfa.Analysis.SpiritLaw
import Nfa.Analysis.StarBadLeSpirit
import Nfa.Analysis.BoundProbaAndEvent
import Nfa.Analysis.IntersectionTail
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Lemma proba_p(q): every estimate is good in `countNFAcore*`

`proba_p_star` is Lemma proba_p(q) (analysis.tex:6-9, proof analysis.tex:115-154 and
373-468) with the window tightened from `(1 ± ε)|L(q)|⁻¹` to `goodWindow ε |L(q)|`
`= [1/((1+ε/2)|L(q)|), 1/((1−ε/2)|L(q)|)]`.  That is the window the paper's
argument controls: a median of means outside `(1 ± ε/2)|L(q)|` needs at least `γ/2`
loose blocks (analysis.tex:407-411), and when every median is inside, induction along
`≺` puts every `p(q) = min(ρ(q), hat ρ(q))` in the window (`ρ(q) = min_i p(q_i)` and
`|L(q_i)| ≤ |L(q)|`).  The paper's own window would not give `1/p(q_F) ∈ (1 ± ε)|ℒ|`.

Proof (the paper's, analysis.tex:115-154 and 373-463):
* `star_bad_le_spirit` (eq. from_N_to_Ns): the first bad listed state `q`; before it,
  `ρ(q) ≥ 1/((1+ε/2)|L(q)|)`, so `p(q)` leaves the window only if the median of the
  block means leaves `(1 ± ε/2)|L(q)|`; up to `q`, `N*` and the spirited `N^s` (floor
  `(1−ε)/|L(q)|`) have the same law, since the floor lies below the window.  This gives
  `Pr_{N*}[bad] ≤ Σ_k spiritLooseProb k`.
* `spiritLooseProb_le`: a loose median forces `⌈γ/2⌉` loose blocks
  (`Arlib.Probability.half_outside_of_median_not_mem`); Proposition
  chernoff_intersections (`intersection_tail_bound`) with Lemma bound_proba_AND_event
  (`bound_proba_AND_event`, `≤ 6^{-|F|}`) gives `2^γ 6^{-⌈γ/2⌉} ≤ 1/(16|Q^u|)`, using
  `5 ln(3/2) ≥ 2` for `γ = ⌈5 ln(16|Q^u|)⌉`.
* there are `|Q^u| − 1` listed states (`corePairs_length_lt`); the sum is `≤ 1/16`.
-/

namespace Nfa.Analysis.ProbaPStarAux

open Nfa.Pseudocode
open scoped ENNReal

/-- `5 ln(3/2) ≥ 2`, from `e² ≤ (3/2)^5`.

INTERNAL: the constant behind `γ = ⌈5 ln(16|Q^u|)⌉`.
TEXLINE: analysis.tex:459-463 -/
theorem five_log_ge : (2 : ℝ) ≤ 5 * Real.log (3 / 2) := by
  have h1 : Real.exp 2 ≤ (3 / 2 : ℝ) ^ 5 := by
    have he := Real.exp_one_lt_d9
    have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have h0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
    nlinarith
  have h2 : 2 ≤ Real.log ((3 / 2 : ℝ) ^ 5) := by
    rw [Real.le_log_iff_exp_le (by norm_num)]; exact h1
  rw [Real.log_pow] at h2
  push_cast at h2
  linarith

/-- `2^γ 6^{-⌈γ/2⌉} ≤ 1/x` once `γ ≥ 5 ln x`, `x ≥ 1`: the paper's `(4/6)^{γ/2} ≤ 1/(16|Q^u|)`.

INTERNAL: the numeric step after Proposition chernoff_intersections.
TEXLINE: analysis.tex:459-463 -/
theorem gamma_tail_real (x : ℝ) (hx : 1 ≤ x) (γ : ℕ) (hγ : 5 * Real.log x ≤ γ) :
    (2 : ℝ) ^ γ * (1 / 6) ^ ((γ + 1) / 2) ≤ 1 / x := by
  have hx0 : 0 < x := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  set k := (γ + 1) / 2
  have hk : γ ≤ 2 * k := by omega
  have ha : 0 ≤ (2 : ℝ) ^ γ * (1 / 6) ^ k := by positivity
  rw [← pow_le_pow_iff_left₀ ha (by positivity) (two_ne_zero)]
  have hsq : ((2 : ℝ) ^ γ * (1 / 6) ^ k) ^ 2 ≤ (2 / 3 : ℝ) ^ γ := by
    rw [mul_pow, ← pow_mul, ← pow_mul]
    calc (2 : ℝ) ^ (γ * 2) * (1 / 6) ^ (k * 2) ≤ (2 : ℝ) ^ (γ * 2) * (1 / 6) ^ γ := by
          gcongr (2 : ℝ) ^ (γ * 2) * ?_
          exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = (2 / 3 : ℝ) ^ γ := by
          rw [mul_comm γ 2, pow_mul, ← mul_pow]; norm_num
  refine hsq.trans ?_
  have hlog23 : Real.log (2 / 3) = - Real.log (3 / 2) := by
    rw [← Real.log_inv]; norm_num
  have h5 := five_log_ge
  have hpos : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hexp : (2 / 3 : ℝ) ^ γ = Real.exp (γ * Real.log (2 / 3)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hx2 : (1 / x) ^ 2 = Real.exp (-(2 * Real.log x)) := by
    rw [Real.exp_neg, show 2 * Real.log x = (2 : ℕ) * Real.log x by norm_num, Real.exp_nat_mul,
      Real.exp_log hx0]
    field_simp
  rw [hexp, hx2, Real.exp_le_exp, hlog23]
  nlinarith

variable {Q : Type} [Fintype Q] [LinearOrder Q]

/-- `Σ_{i ∈ range' 1 n} f i = Σ_{ℓ < n} f (ℓ + 1)`.

INTERNAL: index bookkeeping for `corePairs`.
TEXLINE: algorithm.tex:97 -/
theorem range'_one_sum (f : ℕ → ℕ) (n : ℕ) :
    ((List.range' 1 n).map f).sum = ∑ ℓ ∈ Finset.range n, f (ℓ + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range'_1_concat, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
      simp [add_comm]

/-- The listed states are the unrolled states other than `q_I^0`: `|corePairs| + 1 ≤ |Q^u|`.

INTERNAL: the number of terms in eq. from_N_to_Ns.
TEXLINE: analysis.tex:150-154 -/
theorem corePairs_length_lt (A : PaperNFA Q) (n : ℕ) :
    (corePairs A n).length + 1 ≤ A.unrolledCard n := by
  classical
  have hcard : ∀ ℓ, (A.layer ℓ).ncard = (layerSet A ℓ).card := by
    intro ℓ
    rw [← Set.ncard_coe_finset]
    congr 1
    ext q
    simp [layerSet]
  have hlen : (corePairs A n).length = ∑ ℓ ∈ Finset.range n, (layerSet A (ℓ + 1)).card := by
    unfold corePairs
    rw [List.length_flatMap]
    simp only [List.length_map, layerList, Finset.length_sort]
    exact range'_one_sum (fun i => (layerSet A i).card) n
  have h0 : 1 ≤ (layerSet A 0).card := by
    refine Finset.card_pos.2 ⟨A.qI, ?_⟩
    unfold layerSet
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨[], rfl, by simp [NFA.eval_nil, PaperNFA.toNFA]⟩
  unfold PaperNFA.unrolledCard
  simp_rw [hcard]
  rw [Finset.sum_range_succ', hlen]
  omega

/-- The `ε/2`-median at a listed state of `N^s` is loose with probability at most
`1/(16|Q^u|)`.

INTERNAL: eq. bound_rho_hat at the `ε/2` window, from lemma:bound_proba_AND_event and
prop:chernoff_intersections.
TEXLINE: analysis.tex:404-463 -/
theorem spiritLooseProb_le (hprior : Nfa.Prior) (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A)
    (n : ℕ) (ε δ : ℝ) (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε < 1) (k : ℕ) :
    spiritLooseProb A σ (Nfa.params A n ε δ) ε n k
      ≤ ((16 * A.unrolledCard n : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  set P := Nfa.params A n ε δ
  have hlen := corePairs_length_lt A n
  have hx16 : (1 : ℝ) ≤ ((16 * A.unrolledCard n : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ 16 * A.unrolledCard n)
  have hγ : 5 * Real.log ((16 * A.unrolledCard n : ℕ) : ℝ) ≤ (P.γ : ℝ) := by
    have : P.γ = ⌈5 * Real.log (16 * (A.unrolledCard n : ℝ))⌉₊ := rfl
    rw [this]
    push_cast
    exact Nat.le_ceil _
  have htail : (2 : ℝ≥0∞) ^ P.γ * (1 / 6) ^ ((P.γ + 1) / 2)
      ≤ ((16 * A.unrolledCard n : ℕ) : ℝ≥0∞)⁻¹ := by
    have h := gamma_tail_real _ hx16 P.γ hγ
    have hL : (2 : ℝ≥0∞) ^ P.γ * (1 / 6) ^ ((P.γ + 1) / 2) =
        ENNReal.ofReal ((2 : ℝ) ^ P.γ * (1 / 6) ^ ((P.γ + 1) / 2)) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    have hR : ((16 * A.unrolledCard n : ℕ) : ℝ≥0∞)⁻¹ =
        ENNReal.ofReal (1 / ((16 * A.unrolledCard n : ℕ) : ℝ)) := by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by linarith), ENNReal.ofReal_natCast]
    rw [hL, hR]
    exact ENNReal.ofReal_le_ofReal h
  unfold spiritLooseProb
  rcases hx : (corePairs A n)[k]? with _ | ⟨i, q⟩
  · exact zero_le
  · simp only
    set L := (langCount A i q : ℝ)
    set E : Fin P.γ → Set (Fin P.γ → ℝ) :=
      fun b => {Y | Y b ∉ Set.Icc ((1 - ε / 2) * L) ((1 + ε / 2) * L)}
    refine (MeasureTheory.measure_mono ?_).trans ((intersection_tail_bound _ E _ fun F =>
      bound_proba_AND_event hprior A σ n ε δ hn hε0 hε1 k i q hx F).trans htail)
    intro Y hY
    have := Arlib.Probability.half_outside_of_median_not_mem
      (Arlib.Probability.isMedian_medianOf Y) hY
    simp only [Set.mem_ofPred_eq, E]
    convert this

end Nfa.Analysis.ProbaPStarAux

namespace Nfa.Analysis

open Nfa.Pseudocode
open ProbaPStarAux
open scoped ENNReal

/-- **Lemma proba_p(q)** (analysis.tex:6-9): in `countNFAcore*` with the paper's
parameters, some unrolled state `q^ℓ` ends with `p(q^ℓ)` outside
`[1/((1+ε/2)|L(q^ℓ)|), 1/((1−ε/2)|L(q^ℓ)|)]` with probability at most `1/16`.

PAPER: analysis.tex:6-9 (statement), analysis.tex:115-154 and 373-468 (proof).  The
window is the `ε/2` one the proof controls (analysis.tex:407-411), not the
`(1 ± ε)|L(q)|⁻¹` of the statement; see the module docstring. -/
theorem proba_p_star (hprior : Nfa.Prior) {Q : Type} [Fintype Q] [LinearOrder Q]
    (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (n : ℕ) (ε δ : ℝ)
    (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε < 1) :
    (coreLawStar A σ (Nfa.params A n ε δ) n).toOuterMeasure
      {st | ∃ ℓ ≤ n, ∃ q ∈ layerSet A ℓ, st.p ℓ q ∉ goodWindow ε (langCount A ℓ q : ℝ)}
      ≤ 1 / 16 := by
  set P := Nfa.params A n ε δ
  set Qu := A.unrolledCard n
  have hlen := corePairs_length_lt A n
  have hQu : (Qu : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : Qu ≠ 0)
  calc (coreLawStar A σ P n).toOuterMeasure
        {st | ∃ ℓ ≤ n, ∃ q ∈ layerSet A ℓ, st.p ℓ q ∉ goodWindow ε (langCount A ℓ q : ℝ)}
      ≤ ∑ k ∈ Finset.range (corePairs A n).length, spiritLooseProb A σ P ε n k :=
        star_bad_le_spirit A σ P n ε hε0 hε1
    _ ≤ ∑ k ∈ Finset.range (corePairs A n).length, ((16 * Qu : ℕ) : ℝ≥0∞)⁻¹ :=
        Finset.sum_le_sum fun k _ => spiritLooseProb_le hprior A σ n ε δ hn hε0 hε1 k
    _ = ((corePairs A n).length : ℝ≥0∞) * ((16 * Qu : ℕ) : ℝ≥0∞)⁻¹ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (Qu : ℝ≥0∞) * ((16 * Qu : ℕ) : ℝ≥0∞)⁻¹ := by
        gcongr; exact_mod_cast (by omega : (corePairs A n).length ≤ Qu)
    _ = 1 / 16 := by
        push_cast
        rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), mul_left_comm,
          ENNReal.mul_inv_cancel hQu (ENNReal.natCast_ne_top _), mul_one, one_div]

end Nfa.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved from children · `star_bad_le_spirit`, `bound_proba_AND_event` (both proved),
  `intersection_tail_bound`, the `γ` arithmetic and the count of listed states
* r1 · open · stated for `coreRun_fail_le`; not attempted beyond the route above
-/
