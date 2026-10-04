import Nfa.Interface.Pseudocode
import Nfa.Model.Prior
import Arlib.Prelude
import Mathlib.Data.Set.Finite.List
import Nfa.Analysis.CoreLawLeStar
import Nfa.Analysis.ProbaPStar
import Nfa.Analysis.ProbaSStar

/-!
# One core run fails with probability at most `1/4`

`coreRun_fail_le` is Lemma main_result_core (analysis.tex:16-39), the accuracy half,
in the form the median amplification of the main theorem consumes: on a nonempty
slice, the estimate `est_j = 1/p(q_F^n)` of one run of `countNFAcore` (with the
paper's parameters, interrupt included) lies outside `(1 ± ε)|ℒ_n(𝒜)|` with
probability at most `1/4`.

The paper states the guarantee on `p(q_F)` with the window `(1 ± ε)|ℒ|⁻¹`, from
which `1/p(q_F) ∈ (1 ± ε)|ℒ|` does *not* follow (the upper end `|ℒ|/(1−ε)` exceeds
`(1+ε)|ℒ|`).  The statement here is what analysis.tex:61-66 actually needs.  It is
still what the paper's argument proves: the loose-block event of
analysis.tex:407-411 is already at `ε/2`, so on the good event every median of
means lies in `(1 ± ε/2)|L(q)|`, every `p(q)` lies in
`[1/((1+ε/2)|L(q)|), 1/((1−ε/2)|L(q)|)]` (induction over `≺`, using
`|L(q_i)| ≤ |L(q)|` as in prop:hat_rho_is_enough), and so
`1/p(q_F) ∈ [(1−ε/2)|ℒ|, (1+ε/2)|ℒ|] ⊆ (1 ± ε)|ℒ|`.  The `θ`-overflow bound of
Lemma proba_S(q) still holds with that window, since `1/(1−ε/2) ≤ 1+ε` for `ε ≤ 1`.

Proof (analysis.tex:23-39): by the coupling `coreLaw_le_star`,
`Pr_N[est ∉ window] ≤ Pr_{N*}[Σ|S| ≥ θ] + Pr_{N*}[est ∉ window]`; the first term is
at most `1/8` (`proba_S_star`), and the second at most `1/16` (`proba_p_star`), since
`p(q_F^n) ∈ goodWindow ε |L(q_F^n)|` puts `1/p(q_F^n)` in `(1 ± ε)|ℒ_n(𝒜)|`
(`inv_mem_relErr`, `langCount_qF`).  `1/8 + 1/16 ≤ 1/4`.
-/

namespace Nfa.Analysis

open Nfa.Pseudocode

/-- `|L(q_F^n)| = |ℒ_n(𝒜)|`.

INTERNAL: the slice count is the language count of the final state at layer `n`.
TEXLINE: analysis.tex:24 -/
theorem langCount_qF {Q : Type} (A : PaperNFA Q) (n : ℕ) :
    langCount A n A.qF = Nfa.sliceCount A n := by
  unfold langCount Nfa.sliceCount
  congr 1
  ext w
  simp only [Set.mem_ofPred_eq, NFA.accepts, PaperNFA.toNFA]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, A.qF, rfl, h2⟩
  · rintro ⟨h1, q, hq, h2⟩
    have : q = A.qF := hq
    subst this
    exact ⟨h1, h2⟩

/-- A state of `Q^ℓ` has a nonempty language: `|L(q^ℓ)| ≥ 1`.

INTERNAL: `Q^ℓ` is forward-reachable, so some word of length `ℓ` reaches `q`.
TEXLINE: analysis.tex:86 -/
theorem langCount_pos {Q : Type} [Fintype Q] [LinearOrder Q] (A : PaperNFA Q) (ℓ : ℕ) (q : Q)
    (hq : q ∈ layerSet A ℓ) : 0 < langCount A ℓ q := by
  unfold layerSet at hq
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
  obtain ⟨w, hw, hqw⟩ := hq
  unfold langCount
  rw [Set.ncard_pos ((List.finite_length_eq Bool ℓ).subset fun x hx => hx.1)]
  exact ⟨w, hw, hqw⟩

/-- `p ∈ [1/((1+ε/2)L), 1/((1−ε/2)L)]` puts `1/p` in `(1 ± ε)L`.

INTERNAL: the window repair: the paper's `(1 ± ε)L⁻¹` would not.
TEXLINE: analysis.tex:61-66 -/
theorem inv_mem_relErr {ε L p : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hL : 0 < L)
    (hp : p ∈ goodWindow ε L) : 1 / p ∈ Arlib.relErr ε L := by
  obtain ⟨hlo, hhi⟩ := hp
  have ha : 0 < 1 / ((1 + ε / 2) * L) := by positivity
  have hb : 0 < (1 - ε / 2) * L := mul_pos (by linarith) hL
  have hp0 : 0 < p := ha.trans_le hlo
  constructor
  · have := one_div_le_one_div_of_le hp0 hhi
    rw [one_div_one_div] at this
    nlinarith
  · have := one_div_le_one_div_of_le ha hlo
    rw [one_div_one_div] at this
    nlinarith

/-- **Lemma main_result_core, accuracy half** (analysis.tex:16-39): on a nonempty
slice, one run of `countNFAcore` with the paper's parameters returns
`est = 1/p(q_F^n) ∉ (1 ± ε)|ℒ_n(𝒜)|` with probability at most `1/4`.

PAPER: analysis.tex:16-21 (statement), analysis.tex:23-39 (proof).  Stated on
`est` rather than on `p(q_F)`: the paper's window on `p(q_F)` does not transfer to
`est` (see the module docstring); its own `ε/2` loose-block event does. -/
theorem coreRun_fail_le (hprior : Nfa.Prior) {Q : Type} [Fintype Q] [LinearOrder Q]
    (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (n : ℕ) (ε δ : ℝ)
    (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hne : Nfa.Pseudocode.nonemptySlice A n) :
    (Nfa.Pseudocode.coreRun A σ (Nfa.params A n ε δ) n).toOuterMeasure
      (Arlib.relErr ε (Nfa.sliceCount A n : ℝ))ᶜ ≤ 1 / 4 := by
  set P := Nfa.params A n ε δ
  unfold Nfa.Pseudocode.coreRun
  rw [PMF.toOuterMeasure_map_apply]
  have hqF : A.qF ∈ layerSet A n := hne
  have hL : 0 < (langCount A n A.qF : ℝ) := by exact_mod_cast langCount_pos A n A.qF hqF
  have hsub : coreEstimate A n ⁻¹' (Arlib.relErr ε (Nfa.sliceCount A n : ℝ))ᶜ ⊆
      {st | ∃ ℓ ≤ n, ∃ q ∈ layerSet A ℓ, st.p ℓ q ∉ goodWindow ε (langCount A ℓ q : ℝ)} := by
    intro st hst
    refine ⟨n, le_rfl, A.qF, hqF, fun hp => hst ?_⟩
    simp only [coreEstimate]
    rw [← langCount_qF]
    exact inv_mem_relErr hε0 hε1 hL hp
  calc (coreLaw A σ P n).toOuterMeasure
        (coreEstimate A n ⁻¹' (Arlib.relErr ε (Nfa.sliceCount A n : ℝ))ᶜ)
      ≤ (coreLawStar A σ P n).toOuterMeasure {st | P.θ ≤ storedTotal A n P st} +
          (coreLawStar A σ P n).toOuterMeasure
            (coreEstimate A n ⁻¹' (Arlib.relErr ε (Nfa.sliceCount A n : ℝ))ᶜ) :=
        coreLaw_le_star A σ P n _
    _ ≤ 1 / 8 + 1 / 16 := add_le_add (proba_S_star hprior A σ n ε δ hn hε0 hε1)
        ((MeasureTheory.measure_mono hsub).trans (proba_p_star hprior A σ n ε δ hn hε0 hε1))
    _ ≤ 1 / 8 + 1 / 8 := add_le_add le_rfl (ENNReal.div_le_div_left (by norm_num) _)
    _ = 1 / 4 := by
        rw [ENNReal.div_add_div_same, show (1 : ENNReal) + 1 = 2 by norm_num,
          ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
        norm_num

end Nfa.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved from children · `coreLaw_le_star` (proved), `proba_S_star`, `proba_p_star` (open)
* r1 · open · stated for `countNFA_correct_proof`; live handoff request rejected (mechanical admission)
-/
