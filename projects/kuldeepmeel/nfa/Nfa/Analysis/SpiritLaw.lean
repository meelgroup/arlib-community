import Nfa.Analysis.CoreLawStar

/-!
# The spirited algorithm `N^s`

analysis.tex:73-112 introduces `N^s`: `countNFAcore*` helped by a spirit that knows
every `|L(q)|` and raises each estimate to the floor `(1−ε)/|L(q)|`,
`p(q) = max(bar p(q), (1−ε)/|L(q)|)` with `bar p(q) = min(ρ(q), hat ρ(q))`.
Nothing else changes: `ρ`, the block means, `hat ρ` and both `reduce` thresholds are
computed exactly as in `N*` (`estimateAndSample`).

* `spiritFloor A ε i q` — the floor `(1−ε)/|L(q^i)|`.
* `spiritStep` — `estimateAndSample` with the floor applied to `p(q)`.
* `runSpirit` — `spiritStep` on each listed state in turn (the analogue of `runStar`).
* `spiritPrefix A σ P ε n k` — the state of `N^s` after the first `k` listed states of
  `corePairs A n`, i.e. just before the `k`-th one is estimated.
* `spiritMeans A σ P ε n k i q` — the law, in `N^s`, of the block means
  `Y_{q,0}, …, Y_{q,γ-1}` formed when `q^i` (the `k`-th listed state) is estimated.
* `spiritLooseProb A σ P ε n k` — `Pr_{N^s}[median(Y_q) ∉ (1 ± ε/2)|L(q)|]` at the `k`-th
  listed state (`0` past the end of the list): the per-state term of eq. from_N_to_Ns
  in the `ε/2` form that `goodWindow` needs.
-/

set_option autoImplicit false

open scoped ENNReal

namespace Nfa.Analysis

open Nfa.Pseudocode

variable {Q : Type} [Fintype Q] [LinearOrder Q]

/-- The spirit's floor `(1−ε)/|L(q^i)|`.

PAPER: analysis.tex:76-80 (`p(q) = max(bar p(q), (1−ε)/|L(q)|)`). -/
noncomputable def spiritFloor (A : PaperNFA Q) (ε : ℝ) (i : ℕ) (q : Q) : ℝ :=
  (1 - ε) / (langCount A i q : ℝ)

/-- **`estimateAndSample(q)` in `N^s`**: as `estimateAndSample`, except that the stored
estimate is `max(bar p(q), (1−ε)/|L(q)|)`, and the final `reduce` uses it.

PAPER: analysis.tex:88-111 (the listing of `estimateAndSample` in `N^s`). -/
noncomputable def spiritStep (A : PaperNFA Q) (σ : Selector A) (P : Params) (ε : ℝ)
    (i : ℕ) (st : CoreState Q) (q : Q) : PMF (CoreState Q) :=
  let ρ := rho A st i q
  (hatSamples A σ P st i q ρ).bind fun hatS =>
    let p := max (takeMin ρ (blockMedian P ρ hatS)) (spiritFloor A ε i q)
    (finalReduce P hatS ρ p).map fun S' =>
      { st with
        p := Function.update st.p i (Function.update (st.p i) q p)
        S := Function.update st.S i (Function.update (st.S i) q S') }

/-- `spiritStep` on each listed state in turn.

PAPER: analysis.tex:73-76 (`N^s` follows `N*`). -/
noncomputable def runSpirit (A : PaperNFA Q) (σ : Selector A) (P : Params) (ε : ℝ) :
    CoreState Q → List (ℕ × Q) → PMF (CoreState Q)
  | st, [] => PMF.pure st
  | st, x :: xs => (spiritStep A σ P ε x.1 st x.2).bind fun st' => runSpirit A σ P ε st' xs

/-- The state of `N^s` just before the `k`-th listed state of `corePairs A n` is
estimated.

INTERNAL: the `q`-prefix executions of analysis.tex:126-128, as a law.
TEXLINE: analysis.tex:126-128 -/
noncomputable def spiritPrefix (A : PaperNFA Q) (σ : Selector A) (P : Params) (ε : ℝ)
    (n k : ℕ) : PMF (CoreState Q) :=
  runSpirit A σ P ε (initState A P) ((corePairs A n).take k)

/-- The law, in `N^s`, of the block means `(Y_{q,b})_{b < γ}` formed when `q^i`, the
`k`-th listed state, is estimated.

INTERNAL: the random vector whose median is `1/hat ρ(q)` (eq. rho_hat_to_median).
TEXLINE: analysis.tex:394-404 -/
noncomputable def spiritMeans (A : PaperNFA Q) (σ : Selector A) (P : Params) (ε : ℝ)
    (n k i : ℕ) (q : Q) : PMF (Fin P.γ → ℝ) :=
  (spiritPrefix A σ P ε n k).bind fun t =>
    (hatSamples A σ P t i q (rho A t i q)).map fun hatS b => blockMean P (rho A t i q) hatS b

/-- `Pr_{N^s}[median(Y_{q,0}, …, Y_{q,γ-1}) ∉ (1 ± ε/2)|L(q)|]` at the `k`-th listed state
`q^i` of `corePairs A n`; `0` past the end of the list.

INTERNAL: the per-state term of eq. from_N_to_Ns, at the `ε/2` window.
TEXLINE: analysis.tex:146-151, 404-411 -/
noncomputable def spiritLooseProb (A : PaperNFA Q) (σ : Selector A) (P : Params) (ε : ℝ)
    (n k : ℕ) : ℝ≥0∞ :=
  match (corePairs A n)[k]? with
  | none => 0
  | some (i, q) =>
      (spiritMeans A σ P ε n k i q).toOuterMeasure
        {Y | Arlib.Probability.medianOf Y ∉
          Set.Icc ((1 - ε / 2) * (langCount A i q : ℝ)) ((1 + ε / 2) * (langCount A i q : ℝ))}

end Nfa.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · defined · `spiritFloor`, `spiritStep`, `runSpirit`, `spiritPrefix`, `spiritMeans`,
  `spiritLooseProb`
-/
