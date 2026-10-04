import Nfa.Meta.ModelClosure
import Nfa.Model.Run
import Nfa.Model.Prior
import Arlib.Prelude
import Nfa.Interface.Encoding
import Nfa.Interface.Pseudocode
import Nfa.Interface.ProgramModel
import Nfa.Analysis.UnrollCost
import Nfa.Analysis.CoreRunCost
import Nfa.Analysis.TimeArith

/-!
# The running-time half of theorem:main_result

Every execution of `countNFA` — whatever its tape — takes at most
`C · n² · MM(m) · log(16(n+1)m) · ε⁻² · (1−ε)⁻¹ · ⌈8 ln(1/δ)⌉` steps in the currency
`rate MM m` (analysis.tex:40-55, 67-68).  The bound is deterministic: the support of
`Run.run` is the image of `execution`, and `countNFA_cost` bounds `m` times the
steps of `countNFA` on *every* tape by `countBound` — `unroll` and the emptiness
test, then `μ` core runs (`coreRun_cost`) and the final median of `μ` values.
`countBound_le_target` does the arithmetic at the paper's parameters.  No
probabilistic fact, and nothing from `Prior`, is used.
-/

set_option autoImplicit false

namespace Nfa.Analysis

open Arlib.Computation (Charged)
open Nfa.Model.Operations

/-- INTERNAL: a fold whose iterations take, times `c`, at most `k a` steps takes,
times `c`, at most `Σ k`.
TEXLINE: analysis.tex:67-68 -/
theorem steps_foldl_mul_le {κ κₛ : Type} [Fintype κ] {β ι : Type} (C : Arlib.Computation.Rate κ)
    (f : β → ι → Charged κ κₛ β) (c : ℕ) (k : ι → ℕ) (l : List ι)
    (h : ∀ b a, a ∈ l → c * Charged.steps C (f b a) ≤ k a) (b : β) :
    c * Charged.steps C (Charged.foldl f l b) ≤ (l.map k).sum := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
      rw [steps_foldl_cons, Nat.mul_add, List.map_cons, List.sum_cons]
      exact Nat.add_le_add (h b a (by simp))
        (ih (fun b a ha => h b a (List.mem_cons_of_mem _ ha)) _)

/-- INTERNAL: **`m` times the steps of `countNFA` is at most `countBound`**, on every
tape and for every parameter block.
TEXLINE: analysis.tex:67-68 -/
theorem countNFA_cost {Q : Type} [Fintype Q] [LinearOrder Q] (MM : ℕ → ℕ)
    (A : PaperNFA Q) (σ : Selector A) (n : ℕ) (P : Params) (tape : Tape Q) :
    Fintype.card Q *
        Charged.steps (rate MM (Fintype.card Q)) (Nfa.Program.countNFA A σ n P tape) ≤
      countBound (Fintype.card Q) n (max 1 (MM (Fintype.card Q))) P := by
  set m := Fintype.card Q
  obtain ⟨hu, hsize, hL⟩ := unroll_cost MM A n
  set layers := (Nfa.Program.unroll A n).val
  have hacc : Charged.steps (rate MM m) (Nfa.Program.acceptsAtLength A layers n) ≤ m := by
    refine (steps_foldl_le_sum (rate MM m) _ (fun _ => 1) _ ?_ false).trans ?_
    · intro b a _; simp [sameState]
    · simpa using (layers_getD_length_le layers m hL n).2
  unfold Nfa.Program.countNFA
  simp only [Charged.steps_bind]
  have hrest : m * Charged.steps (rate MM m) (if (Nfa.Program.acceptsAtLength A layers n).val then do
        let ests ← Charged.foldl (fun (ests : List Scalar) (j : ℕ) => do
            let e ← Nfa.Program.coreRun A σ P tape n layers j
            pure (ests ++ [e])) (List.range P.μ) []
        Scalar.median ests
      else Scalar.lit 0) ≤ P.μ * (coreBound m n (max 1 (MM m)) P + m) + m := by
    split
    · simp only [Charged.steps_bind]
      have hfold := steps_foldl_mul_le (rate MM m) (fun (ests : List Scalar) (j : ℕ) => do
            let e ← Nfa.Program.coreRun A σ P tape n layers j
            pure (ests ++ [e])) m (fun _ => coreBound m n (max 1 (MM m)) P) (List.range P.μ)
          (by
            intro b a _
            simpa using coreRun_cost MM A σ P tape n layers a hsize hL) []
      have hlen := (foldl_inv_le (rate MM m) (fun (ests : List Scalar) (j : ℕ) => do
            let e ← Nfa.Program.coreRun A σ P tape n layers j
            pure (ests ++ [e])) (fun _ => True) List.length
          (fun a => Charged.steps (rate MM m) (Nfa.Program.coreRun A σ P tape n layers a))
          (fun _ => 1)
          (List.range P.μ) (by intro b a _ _; exact ⟨trivial, by simp, by simp⟩) [] trivial).2.2
      have hmed : ∀ xs : List Scalar,
          Charged.steps (rate MM m) (Scalar.median xs) ≤ xs.length := by
        intro xs
        unfold Scalar.median
        simp only [Charged.steps_bind, Charged.steps_pure, add_zero]
        refine (steps_foldl_le_sum (rate MM m) _ (fun _ => 1) xs ?_ ()).trans (by simp)
        intro b a _; simp
      simp only [List.map_const', List.length_range, smul_eq_mul, List.sum_replicate,
        List.length_nil, zero_add] at hfold hlen
      have := hmed (Charged.foldl (fun (ests : List Scalar) (j : ℕ) => do
            let e ← Nfa.Program.coreRun A σ P tape n layers j
            pure (ests ++ [e])) (List.range P.μ) []).val
      nlinarith
    · simp [Scalar.lit]
  unfold countBound
  nlinarith

end Nfa.Analysis

/-- Proof-side owner for `Nfa.countNFA_time`; its statement is fixed by the proof charter.
PAPER: introduction.tex:88-95 (running-time half of theorem:main_result); proof
analysis.tex:40-55, 67-68. -/
theorem Nfa.Analysis.countNFA_time_proof (hprior : Nfa.Prior) : ∃ C : ℝ, ∀ (Q : Type) [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (n : ℕ) (ε δ : ℝ) (MM : ℕ → ℕ), 1 ≤ n → 0 < ε → ε < 1 → 0 < δ → δ < 1 → (∀ m, m ^ 2 ≤ MM m) → (∀ m, MM m ≤ m ^ 3) → ∀ c ∈ (Nfa.Run.run A σ n ε δ).support, (Arlib.Computation.Charged.steps (Nfa.Model.Operations.rate MM (Fintype.card Q)) c : ℝ) ≤ C * (n : ℝ) ^ 2 * (MM (Fintype.card Q) : ℝ) * Real.log (16 * ((n : ℝ) + 1) * (Fintype.card Q : ℝ)) * (ε ^ 2)⁻¹ * (1 - ε)⁻¹ * (⌈8 * Real.log (1 / δ)⌉₊ : ℝ) := by
  obtain ⟨C, hC⟩ := Nfa.Analysis.countBound_le_target
  refine ⟨C, ?_⟩
  intro Q _ _ A σ n ε δ MM hn hε0 hε1 hδ0 hδ1 hlo hhi c hc
  rw [Nfa.Interface.run_eq, PMF.mem_support_map_iff] at hc
  obtain ⟨f, -, rfl⟩ := hc
  have hm : (0 : ℝ) < Fintype.card Q := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨A.qI⟩
  have hcost := Nfa.Analysis.countNFA_cost MM A σ n (params A n ε δ)
    (Nfa.Model.Operations.Tape.ofFun f)
  have hb := hC Q A n ε δ MM hn hε0 hε1 hδ0 hδ1 hlo hhi
  have hcost' : (Fintype.card Q : ℝ) *
      (Arlib.Computation.Charged.steps (Nfa.Model.Operations.rate MM (Fintype.card Q))
        (Nfa.Interface.execution A σ n ε δ f) : ℝ) ≤
      (countBound (Fintype.card Q) n (max 1 (MM (Fintype.card Q))) (params A n ε δ) : ℝ) := by
    exact_mod_cast hcost
  exact le_of_mul_le_mul_left (hcost'.trans hb) hm

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `countNFA_time_proof` from `countNFA_cost` (unroll + μ core runs + median) and `countBound_le_target`; deterministic over every tape, no `Prior` field used
-/
