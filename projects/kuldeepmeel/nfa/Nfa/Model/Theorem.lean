import Nfa.Meta.ModelClosure
import Nfa.Model.Run
import Nfa.Model.Prior
import Arlib.Prelude
import Nfa.Analysis.TheoremAccuracyProof
import Nfa.Analysis.TheoremTimeProof
import Nfa.Analysis.TheoremProof

/-!
# Theorem theorem:main_result (introduction.tex:88-95; proof analysis.tex:61-69)

For every single-initial, single-final NFA `𝒜` over `{0,1}` with a total order on
its states, every `n ≥ 1`, `ε ∈ (0,1)`, `δ ∈ (0,1)` and every admissible selector,
`countNFA(𝒜, n, ε, δ)`

* (accuracy) returns `est` with `Pr[est ∈ (1 ± ε)|ℒ_n(𝒜)|] ≥ 1 − δ`, the probability
  being over the algorithm's own coins (`Nfa.Run.output`); and
* (running time) on **every** execution performs at most
  `C · n² · MM(m) · log(16(n+1)m) · ε⁻² · (1−ε)⁻¹ · ⌈8 ln(1/δ)⌉` charged operations,
  `m = |Q|`, for one absolute constant `C` and every witness-product cost `MM` with
  `m² ≤ MM(m) ≤ m³`.

Departures from the paper's wording, each deliberate:

* **Ranges.** The paper states `ε > 0`, `δ > 0`.  The algorithm needs `ε < 1`
  (`β = ⌈64n/(ε²(1−ε))⌉`) and `δ < 1` (`μ = ⌈8 ln(1/δ)⌉ ≥ 1`, else the final median
  is of nothing); the theorem assumes `0 < ε < 1` and `0 < δ < 1`.
* **Time-bound form.** The paper's `O(n²·MM(m)·log(nm)·ε⁻²·log(1/δ))` is not a
  uniform bound as written: `log(nm) = 0` at `n = m = 1`, `log(1/δ) → 0` as `δ → 1`
  while `μ ≥ 1` runs still execute, and `β` carries `(1−ε)⁻¹`.  The bound below
  uses `log(16(n+1)m)`, `(1−ε)⁻¹` and `⌈8 ln(1/δ)⌉₊`; it coincides with the paper's
  up to the constant for `ε ≤ 1/2`, `δ ≤ 1/2`, `nm ≥ 2`.  `C` is quantified once,
  before everything else, which is what "absolute constant" means.
* **`MM`.** Any `MM` with `m² ≤ MM(m) ≤ m³`.  The instances `MM(m) = O(m^{2.575})`
  (Czumaj–Kowaluk–Lingas, minimum witnesses) and `Õ(m^ω)` (any witness) are cited
  by the paper and not formalised.  Blocks of `computeCache` are charged at `MM(|Q|)`
  (padded to `|Q| × |Q|`), so no monotonicity of `MM` is assumed.
* **Selector.** The paper's algorithm resolves the union by the `≺`-least candidate
  (eq. union); Remark selector allows any deterministic choice, and the theorem
  quantifies over every admissible `Selector`.
* **Empty slice.** No hypothesis `ℒ_n(𝒜) ≠ ∅`: the program detects it and returns `0`.
* **Not claimed.** The reduction from general NFAs (introduction.tex:229-230),
  Remark tightness, and the appendix caching scheme.
-/

namespace Nfa

open Nfa.Model

/-- **Accuracy** (theorem:main_result, first half): with probability at least
`1 − δ` over the coins of `countNFA`, the returned estimate lies in the closed
window `[(1−ε)|ℒ_n(𝒜)|, (1+ε)|ℒ_n(𝒜)|]`. -/
theorem countNFA_correct (hprior : Prior) {Q : Type} [Fintype Q] [LinearOrder Q]
    (A : PaperNFA Q) (σ : Selector A) (n : ℕ) (ε δ : ℝ)
    (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ ((Run.output A σ n ε δ).toOuterMeasure
      (Arlib.relErr ε (sliceCount A n : ℝ))).toReal := by
    exact Nfa.Analysis.countNFA_correct_proof hprior (Q := Q) A σ n ε δ hn hε0 hε1 hδ0 hδ1

/-- **Running time** (theorem:main_result, second half): there is one constant `C`
such that every execution of `countNFA` — every computation in the support of
`Run.run` — costs at most `C · n² · MM(m) · log(16(n+1)m) · ε⁻² · (1−ε)⁻¹ ·
⌈8 ln(1/δ)⌉₊` steps in the currency `Operations.rate MM m`, `m = |Q|`. -/
theorem countNFA_time (hprior : Prior) :
    ∃ C : ℝ, ∀ (Q : Type) [Fintype Q] [LinearOrder Q] (A : PaperNFA Q) (σ : Selector A)
      (n : ℕ) (ε δ : ℝ) (MM : ℕ → ℕ),
      1 ≤ n → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      (∀ m, m ^ 2 ≤ MM m) → (∀ m, MM m ≤ m ^ 3) →
      ∀ c ∈ (Run.run A σ n ε δ).support,
        (Arlib.Computation.Charged.steps (Operations.rate MM (Fintype.card Q)) c : ℝ) ≤
          C * (n : ℝ) ^ 2 * (MM (Fintype.card Q) : ℝ) *
            Real.log (16 * ((n : ℝ) + 1) * (Fintype.card Q : ℝ)) *
            (ε ^ 2)⁻¹ * (1 - ε)⁻¹ * (⌈8 * Real.log (1 / δ)⌉₊ : ℝ) := by
    exact Nfa.Analysis.countNFA_time_proof hprior

/-- **Theorem theorem:main_result**: `countNFA` is accurate with probability at least
`1 − δ`, and every execution runs within the repaired time bound, for one absolute
constant `C`. -/
theorem countNFA_main_result (hprior : Prior) :
    ∃ C : ℝ, ∀ (Q : Type) [Fintype Q] [LinearOrder Q] (A : PaperNFA Q) (σ : Selector A)
      (n : ℕ) (ε δ : ℝ) (MM : ℕ → ℕ),
      1 ≤ n → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      (∀ m, m ^ 2 ≤ MM m) → (∀ m, MM m ≤ m ^ 3) →
      1 - δ ≤ ((Run.output A σ n ε δ).toOuterMeasure
          (Arlib.relErr ε (sliceCount A n : ℝ))).toReal ∧
      ∀ c ∈ (Run.run A σ n ε δ).support,
        (Arlib.Computation.Charged.steps (Operations.rate MM (Fintype.card Q)) c : ℝ) ≤
          C * (n : ℝ) ^ 2 * (MM (Fintype.card Q) : ℝ) *
            Real.log (16 * ((n : ℝ) + 1) * (Fintype.card Q : ℝ)) *
            (ε ^ 2)⁻¹ * (1 - ε)⁻¹ * (⌈8 * Real.log (1 / δ)⌉₊ : ℝ) := by
  exact Nfa.Analysis.countNFA_main_result_of_halves (countNFA_correct hprior)
    (countNFA_time hprior)

end Nfa

#modelClosureOfType Nfa.countNFA_main_result
#print axioms Nfa.countNFA_main_result

#surplusIn Nfa.Model from Nfa.countNFA_main_result

/-!
HANDOFF NOTES
Review observations only; these notes do not change theorem status.
Proof trust: 3 trusted-code-base item(s), starting with The cost model in Model/Operations.lean is trusted as the meaning of 'running time'. It prices witnessProduct at MM(|Q|) with witnesses supplied by σ, linear-time median, unit-cost rational coins and unit-cost word/set operations.
Randomness semantics: The headline's distribution is a pushforward of an externally drawn tape along a deterministic program (`PMF.map` of `countNFA … (Tape.ofFun f)` over `tapeLaw`). It is not the algorithm denoted in PMF with its coins as primitive samplers. As a result, the output law does not arise from the control flow of `countNFA`. Whether the statement is about the paper's independent Bernoulli coins depends on an off-statement modelling argument.
-/
