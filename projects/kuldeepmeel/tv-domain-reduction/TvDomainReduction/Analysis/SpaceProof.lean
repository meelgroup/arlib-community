import TvDomainReduction.Model.Prior
import TvDomainReduction.Model.Run
import TvDomainReduction.Meta.ModelClosure
import TvDomainReduction.Interface.Encoding
import TvDomainReduction.Interface.Pseudocode
import TvDomainReduction.Interface.ProgramModel

/-!
Proof-side owner for claim (2) of Theorem 4.1, the retained-size claim.

Two conjuncts: the observed maximum `maxInternalCard` of every reachable
outcome of `Run.runLaw` is at most the static budget `pairRetainedBudget`, and
that budget obeys the paper's formula, which comes from `SparsifyPrior.size_le`
instantiated at `d_S ≤ 2W` and `δ = ε/(3L)`.

Both are proved here, with no `sorry`.  The first is
`maxInternalCard_built_le`: by the simultaneous leaf/node recursion of
`Program.build` and `retainedBudget`, every product region keeps exactly
`prior.size (gP + gQ)` rows.  The second is `retainedBudget_le_sizeBound`:
at every product region `gP + gQ ≤ 2W`, and `d ↦ d log(2d)` is monotone on `ℕ`
(`mul_log_two_mul_mono`), so `size_le` at `d = 2W` dominates every region; the
substitutions `δ⁻² = 9L²/ε²` and `log(1/η') = log(L/η)` then give the factor
`18 = 2 · 9` exactly.
-/

set_option autoImplicit false

namespace TvDomainReduction.Analysis

open Arlib.Approximation
open Arlib.Computation
open Arlib.KnowledgeCompilation.Probabilistic
open TvDomainReduction.Interface

/-- INTERNAL: the observed retained maximum of one bottom-up construction never
exceeds the static budget; at a product region the stored index type is
`RetainedIdx prior gP gQ = Fin (prior.size (gP + gQ))`, exactly the budget's
local term.
TEXLINE: main.tex:896, main.tex:905 -/
theorem maxInternalCard_built_le {δ η' : ℝ} (prior : SparsifyPrior δ η') :
    {V : Vtree} → {gP gQ : ℕ} → (P : Circuit V gP) → (Q : Circuit V gQ) →
      (t : Program.Tape prior) →
      maxInternalCard (built prior P Q t) ≤ retainedBudget prior P Q
  | _, _, _, .leaf _, .leaf _, _ => Nat.zero_le _
  | _, _, _, .node lP rP _, .node lQ rQ _, _ =>
      max_le_max (le_of_eq (by simp))
        (max_le_max (maxInternalCard_built_le prior lP lQ _)
          (maxInternalCard_built_le prior rP rQ _))

/-- INTERNAL: `d ↦ d · log(2d)` is monotone on the naturals (the `d = 0` case
uses `log 0 = 0`).  `SparsifyPrior.size` itself is not assumed monotone; this is
what lets `size_le` at the widest region dominate every region.
TEXLINE: main.tex:896 -/
theorem mul_log_two_mul_mono {a b : ℕ} (hab : a ≤ b) :
    (a : ℝ) * Real.log (2 * a) ≤ (b : ℝ) * Real.log (2 * b) := by
  have hb : 0 ≤ (b : ℝ) * Real.log (2 * b) := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · have : (1 : ℝ) ≤ b := by exact_mod_cast hb
      exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simpa using hb
  · have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
    exact mul_le_mul hab' (Real.log_le_log (by linarith) (by linarith))
      (Real.log_nonneg (by linarith)) (by linarith)

/-- INTERNAL: if every region of both circuits has at most `n` gates, the static
budget is at most `size_le`'s right-hand side at `d = 2n`, since every product
region has `d_S = gP + gQ ≤ 2n` feature coordinates.
TEXLINE: main.tex:896, main.tex:929 -/
theorem retainedBudget_le_sizeBound {δ η' : ℝ} (prior : SparsifyPrior δ η')
    (hη : 0 ≤ Real.log (1 / η')) :
    {V : Vtree} → {gP gQ : ℕ} → (P : Circuit V gP) → (Q : Circuit V gQ) → (n : ℕ) →
      gateWidth P ≤ n → gateWidth Q ≤ n →
      (retainedBudget prior P Q : ℝ)
        ≤ prior.sizeConst * (((2 * n : ℕ) : ℝ) * Real.log (2 * ((2 * n : ℕ) : ℝ)) / δ ^ 2)
            * Real.log (1 / η')
  | _, _, _, .leaf _, .leaf _, n, _, _ => by
      have := mul_log_two_mul_mono (Nat.zero_le (2 * n))
      simp only [retainedBudget_leaf, Nat.cast_zero, mul_zero, zero_mul] at this ⊢
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (div_nonneg this (sq_nonneg _))) hη
  | _, _, _, @Circuit.node _ _ _ _ g lP rP _, @Circuit.node _ _ _ _ h lQ rQ _, n, hP, hQ => by
      simp only [gateWidth_node, max_le_iff] at hP hQ
      rw [retainedBudget_node, Nat.cast_max, Nat.cast_max]
      refine max_le ?_ (max_le ?_ ?_)
      · refine (prior.size_le _).trans ?_
        have hle : g + h ≤ 2 * n := by omega
        gcongr ?_ * (?_ / _) * _
        exact mul_log_two_mul_mono hle
      · exact retainedBudget_le_sizeBound prior hη lP lQ n hP.2.1 hQ.2.1
      · exact retainedBudget_le_sizeBound prior hη rP rQ n hP.2.2 hQ.2.2

/-- Proof-side owner for `TvDomainReduction.pc_fpras_space`; its statement is fixed by the proof charter. -/
theorem pc_fpras_space_proof (hprior : Prior)
    {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ)
    (ε η : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hL : 0 < CircuitPair.steps C)
    (prior : SparsifyPrior (perStepTol ε (CircuitPair.steps C))
      (perStepFail η (CircuitPair.steps C))) :
    (∀ p ∈ (Run.runLaw C prior).support,
        maxInternalCard (Charged.val p) ≤ pairRetainedBudget C prior)
      ∧ (pairRetainedBudget C prior : ℝ)
          ≤ prior.sizeConst * 18 * (pairWidth C : ℝ) * (CircuitPair.steps C : ℝ) ^ 2
              * Real.log (4 * pairWidth C)
              * Real.log (CircuitPair.steps C / η) / ε ^ 2 := by
  refine ⟨?_, ?_⟩
  · intro p hp
    rw [runLaw_eq_map, PMF.mem_support_map_iff] at hp
    obtain ⟨t, -, rfl⟩ := hp
    exact maxInternalCard_built_le prior C.P C.Q t
  · have hL1 : (1 : ℝ) ≤ CircuitPair.steps C := by exact_mod_cast hL
    have hLη : Real.log (1 / perStepFail η (CircuitPair.steps C))
        = Real.log (CircuitPair.steps C / η) := by
      rw [perStepFail_eq, one_div_div]
    have hlog : 0 ≤ Real.log (1 / perStepFail η (CircuitPair.steps C)) := by
      rw [hLη]
      exact Real.log_nonneg ((one_le_div hη0).2 (by linarith))
    refine (retainedBudget_le_sizeBound prior hlog C.P C.Q (pairWidth C)
      (le_max_left _ _) (le_max_right _ _)).trans (le_of_eq ?_)
    rw [hLη]
    generalize prior.sizeConst = c
    rw [perStepTol_eq]
    push_cast
    have hW : (2 : ℝ) * (2 * (pairWidth C : ℝ)) = 4 * pairWidth C := by ring
    rw [hW]
    have hL0 : (CircuitPair.steps C : ℝ) ≠ 0 := by linarith
    field_simp
    ring

end TvDomainReduction.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `pc_fpras_space_proof` closed via local `maxInternalCard_built_le`, `retainedBudget_le_sizeBound`
-/
