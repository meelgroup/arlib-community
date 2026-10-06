import TvDomainReduction.Model.Prior
import TvDomainReduction.Model.Run
import TvDomainReduction.Meta.ModelClosure
import TvDomainReduction.Analysis.TimeProof
import TvDomainReduction.Interface.Encoding
import TvDomainReduction.Interface.Pseudocode
import TvDomainReduction.Interface.ProgramModel

/-!
INTERNAL support file for `wta_fpras_time_proof`.

`Analysis.TimeProof.build_steps_le` prices the solver call at every product
region against `2 · pairWidth C`, the paper's own `d_S ≤ 2W` bound (main.tex:871).
`thm:wta_fpras` is stated against a *different* quantity, `pairJointDim`
(main.tex:969, "the joint node-interface dimension"), which bounds `d_S = gP_S +
gQ_S` at every region *directly*, by the very recursion that defines it — no
factor of `2`, and no detour through `pairWidth`.  Reusing `build_steps_le`
literally would hand back a bound in `prior.polylog (2 · pairWidth C · B²)`,
which is *not* provably `≤ prior.polylog (pairJointDim C · B²)` (polylog is only
known to be monotone, and `pairJointDim ≤ 2 · pairWidth` points the wrong way).

So this file restates `callCost_le_worst` and `build_steps_le` against a generic
dimension bound `D` instead of `2 · pairWidth`, and separately prices the leaf
reads directly (`≤ vtreeNodes V · D · q`, no `B²` factor at all — a leaf's
`(gP+gQ) · m` reads are paid once, never multiplied by the retained-row count),
rather than folding them into `pairSize` and multiplying the whole thing by `B²`
as `build_steps_le` does.  That second change is required, not cosmetic: folding
leaf reads into `B² · pairSize` overcounts a leaf's true cost by a factor of
`B²`, and `B` is unbounded in terms of `pairJointDim` alone (it also grows with
`q`), so the overcounted bound is not provably within `wta_fpras_time`'s stated
shape.
-/

set_option autoImplicit false

namespace TvDomainReduction.Analysis

open Arlib.Approximation
open Arlib.Computation
open Arlib.KnowledgeCompilation.Probabilistic
open TvDomainReduction.Model.Operations
open TvDomainReduction.Interface

/-- INTERNAL: `jointDim`'s leaf equation, named for `simp`. -/
theorem jointDim_leaf {m gP gQ : ℕ} (θP : Fin gP → Fin m → ℝ) (θQ : Fin gQ → Fin m → ℝ) :
    jointDim (Circuit.leaf θP) (Circuit.leaf θQ) = gP + gQ := rfl

/-- INTERNAL: `jointDim`'s node equation, named for `simp`. -/
theorem jointDim_node {Vl Vr : Vtree} {gPl gPr gP gQl gQr gQ : ℕ}
    (lP : Circuit Vl gPl) (rP : Circuit Vr gPr) (lQ : Circuit Vl gQl) (rQ : Circuit Vr gQr)
    (cP : Fin gP → Fin gPl → Fin gPr → ℝ) (cQ : Fin gQ → Fin gQl → Fin gQr → ℝ) :
    jointDim (Circuit.node lP rP cP) (Circuit.node lQ rQ cQ)
      = max (gP + gQ) (max (jointDim lP lQ) (jointDim rP rQ)) := rfl

/-- INTERNAL: `vtreeNodes`'s leaf equation, named for `simp`. -/
theorem vtreeNodes_leaf (m : ℕ) : vtreeNodes (.leaf m) = 1 := rfl

/-- INTERNAL: `vtreeNodes`'s node equation, named for `simp`. -/
theorem vtreeNodes_node (l r : Vtree) :
    vtreeNodes (.node l r) = vtreeNodes l + vtreeNodes r + 1 := rfl

/-- INTERNAL: a circuit's own gate count never exceeds its `gateWidth`, directly
from the two defining equations. -/
theorem self_le_gateWidth : ∀ {V : Vtree} {g : ℕ} (P : Circuit V g), g ≤ gateWidth P
  | _, _, .leaf _ => le_refl _
  | _, _, .node _ _ _ => by simp only [gateWidth_node]; omega

/-- INTERNAL: every v-tree has at least one node. -/
theorem vtreeNodes_pos : ∀ (V : Vtree), 1 ≤ vtreeNodes V
  | .leaf _ => le_refl _
  | .node l r => by
      have := vtreeNodes_pos l
      simp only [vtreeNodes_node]; omega

/-- INTERNAL: on a pair of automata `C : CircuitPair V 1 1`, the joint
node-interface dimension is at least `2`, since the root alone already
contributes `gP + gQ = 1 + 1` to the defining maximum (`main.tex:1002`'s own
remark, "for `CircuitPair V 1 1`, `d ≥ 2`"). -/
theorem pairJointDim_ge_two {V : Vtree} (C : CircuitPair V 1 1) : 2 ≤ pairJointDim C := by
  rcases C with ⟨P, Q⟩
  cases P with
  | leaf θP =>
      cases Q with
      | leaf θQ => simp [pairJointDim, jointDim_leaf]
  | node lP rP cP =>
      cases Q with
      | node lQ rQ cQ =>
          simp only [pairJointDim, jointDim_node]
          omega

/-- INTERNAL: a single circuit's `gateWidth` is dominated by the pair's `jointDim`,
pointwise at every region (`gP_S ≤ gP_S + gQ_S ≤ jointDim`), hence in the max.
TEXLINE: main.tex:1002 -/
theorem gateWidth_le_jointDim_left :
    ∀ {V : Vtree} {gP gQ : ℕ} (P : Circuit V gP) (Q : Circuit V gQ),
      gateWidth P ≤ jointDim P Q
  | _, _, _, .leaf _, .leaf _ => by
      simp only [gateWidth_leaf, jointDim_leaf]; omega
  | _, _, _, .node lP rP cP, .node lQ rQ cQ => by
      simp only [gateWidth_node, jointDim_node]
      have hl := gateWidth_le_jointDim_left lP lQ
      have hr := gateWidth_le_jointDim_left rP rQ
      omega

/-- INTERNAL: symmetric statement for the second circuit. -/
theorem gateWidth_le_jointDim_right :
    ∀ {V : Vtree} {gP gQ : ℕ} (P : Circuit V gP) (Q : Circuit V gQ),
      gateWidth Q ≤ jointDim P Q
  | _, _, _, .leaf _, .leaf _ => by
      simp only [gateWidth_leaf, jointDim_leaf]; omega
  | _, _, _, .node lP rP cP, .node lQ rQ cQ => by
      simp only [gateWidth_node, jointDim_node]
      have hl := gateWidth_le_jointDim_right lP lQ
      have hr := gateWidth_le_jointDim_right rP rQ
      omega

/-- INTERNAL: `pairWidth ≤ pairJointDim` (main.tex:1002's own remark, "differs
from the settled `pairWidth` (`pairWidth ≤ d ≤ 2 · pairWidth`)"), the half this
development needs. -/
theorem pairWidth_le_pairJointDim {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ) :
    pairWidth C ≤ pairJointDim C := by
  simp only [pairWidth_eq, pairJointDim]
  exact max_le (gateWidth_le_jointDim_left C.P C.Q) (gateWidth_le_jointDim_right C.P C.Q)

/-- INTERNAL: the number of product regions never exceeds the number of v-tree
nodes (`CircuitPair.steps ≤ vtreeNodes`); `vtreeNodes`'s own docstring records the
exact relation `vtreeNodes = 2 · steps + 1`, of which only the inequality is
needed here. -/
theorem circuitPair_steps_le_vtreeNodes :
    ∀ {V : Vtree} {gP gQ : ℕ} (P : Circuit V gP) (Q : Circuit V gQ),
      (pairRegion P Q).steps ≤ vtreeNodes V
  | _, _, _, .leaf θP, .leaf θQ => by
      have hpr : (pairRegion (Circuit.leaf θP) (Circuit.leaf θQ)).steps = 0 := rfl
      simp only [vtreeNodes_leaf, hpr]
      omega
  | _, _, _, .node lP rP cP, .node lQ rQ cQ => by
      have hpr : (pairRegion (Circuit.node lP rP cP) (Circuit.node lQ rQ cQ)).steps
          = (pairRegion lP lQ).steps + (pairRegion rP rQ).steps + 1 := rfl
      rw [hpr, vtreeNodes_node]
      have hl := circuitPair_steps_le_vtreeNodes lP lQ
      have hr := circuitPair_steps_le_vtreeNodes rP rQ
      omega

/-- INTERNAL: `callCost_le_worst`, restated against a direct dimension bound `D`
instead of `2 · pairWidth`.  Same proof, with `D` in place of `2 * W`
throughout. -/
theorem callCost_le_joint {δ η' : ℝ} (prior : SparsifyPrior δ η') (N d B D : ℕ)
    (hN : N ≤ B ^ 2) (hd : d ≤ D) :
    (prior.callCost N d : ℝ)
      ≤ prior.costConst * prior.polylog (D * B ^ 2)
          * ((D : ℝ) * (B : ℝ) ^ 2 + (D : ℝ) ^ prior.mmExp) := by
  have hNd : N * d ≤ D * B ^ 2 := by
    calc N * d ≤ B ^ 2 * D := Nat.mul_le_mul hN hd
      _ = D * B ^ 2 := by ring
  have hω : (0 : ℝ) ≤ prior.mmExp := by linarith [prior.mmExp_le.1]
  have hpl : (prior.polylog (N * d) : ℝ) ≤ prior.polylog (D * B ^ 2) := by
    exact_mod_cast prior.polylog_mono hNd
  have hNd' : (N : ℝ) * d ≤ (D : ℝ) * (B : ℝ) ^ 2 := by exact_mod_cast hNd
  have hd' : (d : ℝ) ≤ (D : ℝ) := by exact_mod_cast hd
  have hrp : (d : ℝ) ^ prior.mmExp ≤ (D : ℝ) ^ prior.mmExp :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hd' hω
  have hnn : (0 : ℝ) ≤ (N : ℝ) * d + (d : ℝ) ^ prior.mmExp :=
    add_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine (prior.callCost_le N d).trans ?_
  calc (prior.costConst : ℝ) * prior.polylog (N * d) * ((N : ℝ) * d + (d : ℝ) ^ prior.mmExp)
      ≤ (prior.costConst : ℝ) * prior.polylog (D * B ^ 2)
          * ((N : ℝ) * d + (d : ℝ) ^ prior.mmExp) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpl (Nat.cast_nonneg _)) hnn
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hNd' hrp) (by positivity)

/-- INTERNAL: the per-region recursion of the time claim, restated against a
direct dimension bound `D` on `jointDim` and pricing leaf reads directly instead
of folding them into `B² · pairSize` (see the module docstring for why).  A leaf
contributes `vtreeNodes · D · q`, never scaled by `B`; a product region
contributes `B² · (1 + 6D³)` for the inherited weights and fused features plus
one worst-case Lewis-weight call.
TEXLINE: main.tex:929, main.tex:1002 -/
theorem build_steps_le_joint {δ η' : ℝ} (prior : SparsifyPrior δ η') (B D q : ℕ) :
    ∀ {V : Vtree} {gP gQ : ℕ} (P : Circuit V gP) (Q : Circuit V gQ) (t : Program.Tape prior),
      leafDomMax V + retainedBudget prior P Q ≤ B → jointDim P Q ≤ D → leafDomMax V ≤ q →
      (Charged.steps rate (Program.build prior P Q t) : ℝ)
        ≤ (vtreeNodes V : ℝ) * ((D : ℝ) * q)
          + ((pairRegion P Q).steps : ℝ) * ((B : ℝ) ^ 2 * (1 + 6 * (D : ℝ) ^ 3)
              + prior.costConst * prior.polylog (D * B ^ 2)
                  * ((D : ℝ) * (B : ℝ) ^ 2 + (D : ℝ) ^ prior.mmExp))
  | _, _, _, @Circuit.leaf m gP θP, @Circuit.leaf _ gQ θQ, t, _, hD, hq => by
      have hstep : Charged.steps rate (Program.build prior (Circuit.leaf θP) (Circuit.leaf θQ) t)
          = (gP + gQ) * m := steps_opMany_rate _ _ _
      simp only [jointDim_leaf] at hD
      simp only [leafDomMax_leaf] at hq
      have hpr : (pairRegion (Circuit.leaf θP) (Circuit.leaf θQ)).steps = 0 := rfl
      have h1 : (gP + gQ) * m ≤ D * q := Nat.mul_le_mul hD hq
      rw [hstep, vtreeNodes_leaf, hpr]
      push_cast
      simp only [one_mul, zero_mul, add_zero]
      exact_mod_cast h1
  | _, _, _, @Circuit.node Vl Vr gPl gPr gP lP rP cP,
             @Circuit.node _ _ gQl gQr gQ lQ rQ cQ, t, hB, hD, hq => by
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
      simp only [jointDim_node] at hD
      simp only [leafDomMax_node] at hq
      have hBl : leafDomMax Vl + retainedBudget prior lP lQ ≤ B := by omega
      have hBr : leafDomMax Vr + retainedBudget prior rP rQ ≤ B := by omega
      have hDg : gP + gQ ≤ D := by omega
      have hDl : jointDim lP lQ ≤ D := by omega
      have hDr : jointDim rP rQ ≤ D := by omega
      have hql : leafDomMax Vl ≤ q := by omega
      have hqr : leafDomMax Vr ≤ q := by omega
      have IHl := build_steps_le_joint prior B D q lP lQ (fun p => t (false :: p)) hBl hDl hql
      have IHr := build_steps_le_joint prior B D q rP rQ (fun p => t (true :: p)) hBr hDr hqr
      have hclB := (build_card_idx_le prior lP lQ (fun p => t (false :: p))).trans hBl
      have hcrB := (build_card_idx_le prior rP rQ (fun p => t (true :: p))).trans hBr
      have hgPl : gPl ≤ D := (self_le_gateWidth lP).trans ((gateWidth_le_jointDim_left lP lQ).trans hDl)
      have hgPr : gPr ≤ D := (self_le_gateWidth rP).trans ((gateWidth_le_jointDim_left rP rQ).trans hDr)
      have hgQl : gQl ≤ D := (self_le_gateWidth lQ).trans ((gateWidth_le_jointDim_right lP lQ).trans hDl)
      have hgQr : gQr ≤ D := (self_le_gateWidth rQ).trans ((gateWidth_le_jointDim_right rP rQ).trans hDr)
      have hgP : gP ≤ D := by omega
      have hgQ : gQ ≤ D := by omega
      have hwires : gP * gPl * gPr + gQ * gQl * gQr ≤ 2 * D ^ 3 := by
        have h1 : gP * gPl * gPr ≤ D * D * D := Nat.mul_le_mul (Nat.mul_le_mul hgP hgPl) hgPr
        have h2 : gQ * gQl * gQr ≤ D * D * D := Nat.mul_le_mul (Nat.mul_le_mul hgQ hgQl) hgQr
        have : D * D * D = D ^ 3 := by ring
        omega
      rw [hstep, hpr, vtreeNodes_node]
      generalize Fintype.card (Program.build prior lP lQ (fun p => t (false :: p))).val.Idx = cl
        at hclB ⊢
      generalize Fintype.card (Program.build prior rP rQ (fun p => t (true :: p))).val.Idx = cr
        at hcrB ⊢
      generalize Charged.steps rate (Program.build prior lP lQ (fun p => t (false :: p))) = sl
        at IHl ⊢
      generalize Charged.steps rate (Program.build prior rP rQ (fun p => t (true :: p))) = sr
        at IHr ⊢
      have hN : cl * cr ≤ B ^ 2 := by rw [sq]; exact Nat.mul_le_mul hclB hcrB
      have hcall := callCost_le_joint prior (cl * cr) (gP + gQ) B D hN hDg
      have hN' : ((cl * cr : ℕ) : ℝ) * (1 + 3 * ((gP * gPl * gPr + gQ * gQl * gQr : ℕ) : ℝ))
          ≤ (B : ℝ) ^ 2 * (1 + 6 * (D : ℝ) ^ 3) := by
        have hwires' : ((gP * gPl * gPr + gQ * gQl * gQr : ℕ) : ℝ) ≤ 2 * (D : ℝ) ^ 3 := by
          exact_mod_cast hwires
        have hN'' : ((cl * cr : ℕ) : ℝ) ≤ (B : ℝ) ^ 2 := by exact_mod_cast hN
        have h3 : (0:ℝ) ≤ 1 + 3 * ((gP * gPl * gPr + gQ * gQl * gQr : ℕ) : ℝ) := by positivity
        calc ((cl * cr : ℕ) : ℝ) * (1 + 3 * ((gP * gPl * gPr + gQ * gQl * gQr : ℕ) : ℝ))
            ≤ (B : ℝ) ^ 2 * (1 + 3 * ((gP * gPl * gPr + gQ * gQl * gQr : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_right hN'' h3
          _ ≤ (B : ℝ) ^ 2 * (1 + 6 * (D : ℝ) ^ 3) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              linarith
      push_cast at IHl IHr hN' hcall ⊢
      generalize hZ : (B:ℝ) ^ 2 * (1 + 6 * (D:ℝ) ^ 3)
          + (prior.costConst:ℝ) * (prior.polylog (D * B ^ 2) : ℝ)
              * ((D:ℝ) * (B:ℝ) ^ 2 + (D:ℝ) ^ prior.mmExp) = Z at IHl IHr hcall ⊢
      generalize hLl : ((pairRegion lP lQ).steps : ℝ) = Ll at IHl ⊢
      generalize hLr : ((pairRegion rP rQ).steps : ℝ) = Lr at IHr ⊢
      generalize hDq : (D : ℝ) * (q : ℝ) = Dq at IHl IHr ⊢
      have hdist : (Ll + Lr + 1) * Z = Ll * Z + Lr * Z + Z := by ring
      have hdist2 : ((vtreeNodes Vl : ℝ) + vtreeNodes Vr + 1) * Dq
          = (vtreeNodes Vl : ℝ) * Dq + (vtreeNodes Vr : ℝ) * Dq + Dq := by ring
      have hcomb : (cl:ℝ) * cr * (1 + 3 * ((gP:ℝ) * gPl * gPr + (gQ:ℝ) * gQl * gQr))
          + (prior.callCost (cl * cr) (gP + gQ) : ℝ) ≤ Z := by rw [← hZ]; linarith [hN', hcall]
      have hDq0 : (0:ℝ) ≤ Dq := by rw [← hDq]; positivity
      rw [hdist, hdist2]
      linarith [IHl, IHr, hcomb, hDq0]

end TvDomainReduction.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · all declarations, no `sorry`; used by `Analysis.WtaTimeProof.wta_fpras_time_proof`.
-/
