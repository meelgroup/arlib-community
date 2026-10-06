import TvDomainReduction.Model.Prior
import TvDomainReduction.Model.Run
import TvDomainReduction.Meta.ModelClosure
import TvDomainReduction.Interface.Encoding
import TvDomainReduction.Interface.Pseudocode
import TvDomainReduction.Interface.ProgramModel

/-!
Proof-side owner for claim (3) of Theorem 4.1, the arithmetic-running-time
claim.

Per-outcome over the support of `Run.runLaw`: the tally `Charged.steps rate` of
the charged program `Program.run` is bounded by the propagation's own term plus
`L` calls of the cited solver, whose price is `SparsifyPrior.callCost_le`.

The proof is a structural recursion over the shared v-tree (`build_steps_le`),
mirroring `Program.build`: a leaf costs its `(gP + gQ) · m` table reads; a product
region costs `N · (1 + 3 · wires)` for the inherited weights and the fused
features plus one Lewis-weight call, where `N ≤ (q + M)²` by `build_card_idx_le`.
The root evaluation of `Program.run` adds `4n + 1` with `n ≤ q + M`.  Summing gives
`(q+M)² (L + 3|C|) + 4(q+M) + 1 ≤ 7 (1 + (q+M)² (|C| + L))` for the traversal, and
the constant is `c = 7`.  The hypotheses on `ε`, `η` and `hprior` are not used: the
bound holds for every tape, not only on the support.
-/

set_option autoImplicit false

namespace TvDomainReduction.Analysis

open Arlib.Approximation
open Arlib.Computation
open Arlib.KnowledgeCompilation.Probabilistic
open TvDomainReduction.Model.Operations

/-- INTERNAL: one `opMany` block of `n` operations costs `n` steps at the unit rate.
Stated with the value as a variable so that it applies by unification to the
program's charged lines, whose values are only definitionally of the declared type. -/
theorem steps_opMany_rate {α : Type _} (o : ArithOp) (n : ℕ) (a : α) :
    Charged.steps rate (Charged.opMany o n a : Comp α) = n := by
  simp [rate]

/-- INTERNAL: every coreset `Program.build` produces has at most `q + M` rows: `m ≤ q`
at a leaf, and exactly `prior.size (gP + gQ) ≤ M` (zero-padded) at a product region.
TEXLINE: main.tex:929 -/
theorem build_card_idx_le {δ η' : ℝ} (prior : SparsifyPrior δ η') :
    ∀ {V : Vtree} {gP gQ : ℕ} (P : Circuit V gP) (Q : Circuit V gQ) (t : Program.Tape prior),
      Fintype.card (Program.build prior P Q t).val.Idx ≤ leafDomMax V + retainedBudget prior P Q
  | _, _, _, @Circuit.leaf m gP θP, @Circuit.leaf _ gQ θQ, t => by
      rw [Fintype.card_eq_nat_card]
      change Nat.card (Fin m) ≤ m + 0
      simp
  | _, _, _, @Circuit.node _ _ gPl gPr gP lP rP cP,
             @Circuit.node _ _ gQl gQr gQ lQ rQ cQ, t => by
      rw [Fintype.card_eq_nat_card]
      change Nat.card (Fin (prior.size (Fintype.card (Coord gP gQ)))) ≤ _
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Coord, Fintype.card_sum,
        retainedBudget, leafDomMax]
      omega

/-- INTERNAL: one Lewis-weight call on at most `B²` candidate rows and at most `2W`
columns costs at most the worst-case price `costConst · polylog(2WB²) · (2WB² + (2W)^ω)`,
from `SparsifyPrior.callCost_le` and `polylog_mono`.
TEXLINE: main.tex:929 -/
theorem callCost_le_worst {δ η' : ℝ} (prior : SparsifyPrior δ η') (N d B W : ℕ)
    (hN : N ≤ B ^ 2) (hd : d ≤ 2 * W) :
    (prior.callCost N d : ℝ)
      ≤ prior.costConst * prior.polylog (2 * W * B ^ 2)
          * (2 * (W : ℝ) * (B : ℝ) ^ 2 + (2 * W : ℝ) ^ prior.mmExp) := by
  have hNd : N * d ≤ 2 * W * B ^ 2 := by
    calc N * d ≤ B ^ 2 * (2 * W) := Nat.mul_le_mul hN hd
      _ = 2 * W * B ^ 2 := by ring
  have hω : (0 : ℝ) ≤ prior.mmExp := by linarith [prior.mmExp_le.1]
  have hpl : (prior.polylog (N * d) : ℝ) ≤ prior.polylog (2 * W * B ^ 2) := by
    exact_mod_cast prior.polylog_mono hNd
  have hNd' : (N : ℝ) * d ≤ 2 * (W : ℝ) * (B : ℝ) ^ 2 := by exact_mod_cast hNd
  have hd' : (d : ℝ) ≤ 2 * (W : ℝ) := by exact_mod_cast hd
  have hrp : (d : ℝ) ^ prior.mmExp ≤ (2 * W : ℝ) ^ prior.mmExp :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hd' hω
  have hnn : (0 : ℝ) ≤ (N : ℝ) * d + (d : ℝ) ^ prior.mmExp :=
    add_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine (prior.callCost_le N d).trans ?_
  calc (prior.costConst : ℝ) * prior.polylog (N * d) * ((N : ℝ) * d + (d : ℝ) ^ prior.mmExp)
      ≤ (prior.costConst : ℝ) * prior.polylog (2 * W * B ^ 2)
          * ((N : ℝ) * d + (d : ℝ) ^ prior.mmExp) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpl (Nat.cast_nonneg _)) hnn
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hNd' hrp) (by positivity)

/-- INTERNAL: the per-region recursion of the time claim.  For any `B ≥ q + M` and
`W` bounding both circuits' widths, the tally of `Program.build` is at most
`B² · (L + 3|C|)` for the traversal (weights, multiply-accumulates, leaf reads) plus
`L` worst-case Lewis-weight calls.
TEXLINE: main.tex:929 -/
theorem build_steps_le {δ η' : ℝ} (prior : SparsifyPrior δ η') (B W : ℕ) :
    ∀ {V : Vtree} {gP gQ : ℕ} (P : Circuit V gP) (Q : Circuit V gQ) (t : Program.Tape prior),
      leafDomMax V + retainedBudget prior P Q ≤ B → gateWidth P ≤ W → gateWidth Q ≤ W →
      (Charged.steps rate (Program.build prior P Q t) : ℝ)
        ≤ (B : ℝ) ^ 2 * ((pairRegion P Q).steps + 3 * ((circuitSize P : ℝ) + circuitSize Q))
          + ((pairRegion P Q).steps : ℝ) * (prior.costConst * prior.polylog (2 * W * B ^ 2)
              * (2 * (W : ℝ) * (B : ℝ) ^ 2 + (2 * W : ℝ) ^ prior.mmExp))
  | _, _, _, @Circuit.leaf m gP θP, @Circuit.leaf _ gQ θQ, t, hB, _, _ => by
      have hstep : Charged.steps rate (Program.build prior (Circuit.leaf θP) (Circuit.leaf θQ) t)
          = (gP + gQ) * m := steps_opMany_rate _ _ _
      simp only [leafDomMax, retainedBudget, add_zero] at hB
      have h1 : (gP + gQ) * m ≤ (gP + gQ) * B ^ 2 := by
        apply Nat.mul_le_mul_left
        calc m ≤ m * m := Nat.le_mul_self m
          _ ≤ B * B := Nat.mul_le_mul hB hB
          _ = B ^ 2 := (sq B).symm
      have h1' : ((gP + gQ : ℕ) * m : ℝ) ≤ ((gP + gQ : ℕ) : ℝ) * (B : ℝ) ^ 2 := by
        exact_mod_cast h1
      have hpr : (pairRegion (Circuit.leaf θP) (Circuit.leaf θQ)).steps = 0 := rfl
      rw [hstep, hpr]
      simp only [circuitSize]
      push_cast at h1' ⊢
      have : (0:ℝ) ≤ (B:ℝ)^2 * ((gP:ℝ) * m + gQ * m) := by positivity
      nlinarith
  | _, _, _, @Circuit.node Vl Vr gPl gPr gP lP rP cP,
             @Circuit.node _ _ gQl gQr gQ lQ rQ cQ, t, hB, hWP, hWQ => by
      have hstep : Charged.steps rate (Program.build prior (Circuit.node lP rP cP) (Circuit.node lQ rQ cQ) t) =
          Charged.steps rate (Program.build prior lP lQ (fun p => t (false :: p)))
          + Charged.steps rate (Program.build prior rP rQ (fun p => t (true :: p)))
          + (Fintype.card (Program.build prior lP lQ (fun p => t (false :: p))).val.Idx
              * Fintype.card (Program.build prior rP rQ (fun p => t (true :: p))).val.Idx)
            * (1 + 3 * (gP * gPl * gPr + gQ * gQl * gQr))
          + prior.callCost (Fintype.card (Program.build prior lP lQ (fun p => t (false :: p))).val.Idx
              * Fintype.card (Program.build prior rP rQ (fun p => t (true :: p))).val.Idx) (gP + gQ) := by
        simp only [Program.build, Charged.steps_bind, muls, adds, lewisOps, steps_opMany_rate]
        refine Eq.trans (congrArg (fun x => _ + (_ + (_ + (_ + x)))) (steps_opMany_rate _ _ _)) ?_
        ring
      have hpr : (pairRegion (Circuit.node lP rP cP) (Circuit.node lQ rQ cQ)).steps
          = (pairRegion lP lQ).steps + (pairRegion rP rQ).steps + 1 := rfl
      simp only [leafDomMax, retainedBudget] at hB
      simp only [gateWidth] at hWP hWQ
      have hBl : leafDomMax Vl + retainedBudget prior lP lQ ≤ B := by omega
      have hBr : leafDomMax Vr + retainedBudget prior rP rQ ≤ B := by omega
      have IHl := build_steps_le prior B W lP lQ (fun p => t (false :: p)) hBl (by omega) (by omega)
      have IHr := build_steps_le prior B W rP rQ (fun p => t (true :: p)) hBr (by omega) (by omega)
      have hclB := (build_card_idx_le prior lP lQ (fun p => t (false :: p))).trans hBl
      have hcrB := (build_card_idx_le prior rP rQ (fun p => t (true :: p))).trans hBr
      rw [hstep, hpr]
      generalize Fintype.card (Program.build prior lP lQ (fun p => t (false :: p))).val.Idx = cl
        at hclB ⊢
      generalize Fintype.card (Program.build prior rP rQ (fun p => t (true :: p))).val.Idx = cr
        at hcrB ⊢
      generalize Charged.steps rate (Program.build prior lP lQ (fun p => t (false :: p))) = sl
        at IHl ⊢
      generalize Charged.steps rate (Program.build prior rP rQ (fun p => t (true :: p))) = sr
        at IHr ⊢
      have hN : cl * cr ≤ B ^ 2 := by rw [sq]; exact Nat.mul_le_mul hclB hcrB
      have hcall := callCost_le_worst prior (cl * cr) (gP + gQ) B W hN (by omega)
      have hN' : ((cl * cr : ℕ) : ℝ) * (1 + 3 * ((gP * gPl * gPr + gQ * gQl * gQr : ℕ) : ℝ))
          ≤ (B : ℝ) ^ 2 * (1 + 3 * ((gP * gPl * gPr + gQ * gQl * gQr : ℕ) : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast hN
      simp only [circuitSize]
      push_cast at IHl IHr hN' hcall ⊢
      have h3 : (0 : ℝ) ≤ (B : ℝ) ^ 2 * ((gP : ℝ) + gQ) := by positivity
      linarith

/-- Proof-side owner for `TvDomainReduction.pc_fpras_time`; its statement is fixed by the proof charter. -/
theorem pc_fpras_time_proof (hprior : Prior)
    {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ)
    (ε η : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hL : 0 < CircuitPair.steps C)
    (prior : SparsifyPrior (perStepTol ε (CircuitPair.steps C))
      (perStepFail η (CircuitPair.steps C))) :
    ∃ c : ℕ, ∀ p ∈ (Run.runLaw C prior).support,
      (Charged.steps rate p : ℝ)
        ≤ c * (1 + ((leafDomMax V : ℝ) + pairRetainedBudget C prior) ^ 2
                    * (pairSize C + CircuitPair.steps C))
          + (CircuitPair.steps C : ℝ) * prior.costConst
              * prior.polylog
                  (2 * pairWidth C * (leafDomMax V + pairRetainedBudget C prior) ^ 2)
              * (2 * (pairWidth C : ℝ)
                    * ((leafDomMax V : ℝ) + pairRetainedBudget C prior) ^ 2
                  + (2 * pairWidth C : ℝ) ^ prior.mmExp) := by
  refine ⟨7, fun p hp => ?_⟩
  rw [Run.runLaw, PMF.mem_support_map_iff] at hp
  obtain ⟨t, -, rfl⟩ := hp
  have hrun : Charged.steps rate (Program.run C prior t)
      = Charged.steps rate (Program.build prior C.P C.Q t)
        + 4 * Fintype.card (Program.build prior C.P C.Q t).val.Idx + 1 := by
    simp only [Program.run, Charged.steps_bind, subs, abses, muls, adds, divs, steps_opMany_rate]
    refine Eq.trans (congrArg (fun x => _ + (_ + (_ + (_ + (_ + x))))) (steps_opMany_rate _ _ _)) ?_
    ring
  have hB : leafDomMax V + retainedBudget prior C.P C.Q
      ≤ leafDomMax V + pairRetainedBudget C prior := le_refl _
  have hbuild := build_steps_le prior (leafDomMax V + pairRetainedBudget C prior) (pairWidth C)
    C.P C.Q t hB (le_max_left _ _) (le_max_right _ _)
  have hcard := build_card_idx_le prior C.P C.Q t
  have hpr : (pairRegion C.P C.Q).steps = CircuitPair.steps C := rfl
  rw [hpr] at hbuild
  rw [hrun]
  generalize Fintype.card (Program.build prior C.P C.Q t).val.Idx = n at hcard ⊢
  generalize Charged.steps rate (Program.build prior C.P C.Q t) = s at hbuild ⊢
  have hn : n ≤ (leafDomMax V + pairRetainedBudget C prior) ^ 2 := by
    rw [sq]
    exact (Nat.le_mul_self n).trans (Nat.mul_le_mul hcard hcard)
  have hn' : (n : ℝ) ≤ ((leafDomMax V : ℝ) + pairRetainedBudget C prior) ^ 2 := by
    exact_mod_cast hn
  have hL' : (1 : ℝ) ≤ CircuitPair.steps C := by exact_mod_cast hL
  simp only [pairSize] at hbuild ⊢
  push_cast at hbuild ⊢
  have hSL : ((leafDomMax V : ℝ) + pairRetainedBudget C prior) ^ 2
      ≤ ((leafDomMax V : ℝ) + pairRetainedBudget C prior) ^ 2
        * ((circuitSize C.P : ℝ) + circuitSize C.Q + CircuitPair.steps C) :=
    le_mul_of_one_le_right (sq_nonneg _) (by
      have : (0 : ℝ) ≤ (circuitSize C.P : ℝ) + circuitSize C.Q := by positivity
      linarith)
  have h0 : (0 : ℝ) ≤ ((leafDomMax V : ℝ) + pairRetainedBudget C prior) ^ 2
      * ((circuitSize C.P : ℝ) + circuitSize C.Q) := by positivity
  have h1 : (0 : ℝ) ≤ ((leafDomMax V : ℝ) + pairRetainedBudget C prior) ^ 2
      * (CircuitPair.steps C : ℝ) := by positivity
  linarith

end TvDomainReduction.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `pc_fpras_time_proof` with `c = 7`, via `build_steps_le` / `build_card_idx_le` / `callCost_le_worst`
-/
