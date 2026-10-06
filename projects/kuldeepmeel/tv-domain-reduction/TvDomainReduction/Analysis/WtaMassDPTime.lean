import TvDomainReduction.Model.Prior
import TvDomainReduction.Model.Program
import TvDomainReduction.Meta.ModelClosure
import TvDomainReduction.Interface.Encoding
import TvDomainReduction.Analysis.TimeProof

/-!
INTERNAL support file for `wta_fpras_time_proof`.

Prices `Program.massDP` (main.tex:967, the normalisation DP), which `Run.runLawWTA`
runs once per automaton before `Program.runDense`.  The recursion mirrors
`massDP`'s own two cases exactly: a leaf with `g` coordinates over `Fin m` costs
`g · (m − 1)` additions, and an internal node costs `3 · g · gl · gr` (two
multiplications and one addition per tensor entry), on top of its two children.
No candidate-set bookkeeping enters here at all — `massDP` consumes no
randomness and forms no coreset — so the bound is purely in terms of the
circuit's own `gateWidth` and the tree's `leafDomMax`, summed once per v-tree
node (`vtreeNodes`).
-/

set_option autoImplicit false

universe u

namespace TvDomainReduction.Analysis

open Arlib.Approximation
open Arlib.Computation
open Arlib.KnowledgeCompilation.Probabilistic
open TvDomainReduction.Model.Operations
open TvDomainReduction.Interface

/-- INTERNAL: `vtreeNodes`'s leaf equation, named for `simp` (mirrors
`Analysis.WtaJointBound.vtreeNodes_leaf`; restated here so this file does not
need that one's imports). -/
theorem massDP_vtreeNodes_leaf (m : ℕ) : vtreeNodes (.leaf m) = 1 := rfl

/-- INTERNAL: `vtreeNodes`'s node equation, named for `simp`. -/
theorem massDP_vtreeNodes_node (l r : Vtree) :
    vtreeNodes (.node l r) = vtreeNodes l + vtreeNodes r + 1 := rfl

/-- INTERNAL: a circuit's own gate count never exceeds its `gateWidth`, directly
from the two defining equations. -/
theorem massDP_self_le_gateWidth : ∀ {V : Vtree} {g : ℕ} (P : Circuit V g), g ≤ gateWidth P
  | _, _, .leaf _ => le_refl _
  | _, _, .node _ _ _ => by
      simp only [gateWidth_node]; exact le_max_left _ _

/-- INTERNAL: `Program.massDP`'s tally never depends on the value threaded
through it — every charge is a static count determined by the circuit alone —
so the two children's tallies may be computed against any input value, in
particular the original `a` rather than the first child's output. -/
theorem massDP_steps_eq {α : Type u} :
    ∀ {V : Vtree} {g : ℕ} (P : Circuit V g) (a b : α),
      Charged.steps rate (Program.massDP P a) = Charged.steps rate (Program.massDP P b)
  | _, _, .leaf _, a, b => by
      simp only [Program.massDP, adds, steps_opMany_rate]
  | _, _, .node l r c, a, b => by
      simp only [Program.massDP, Charged.steps_bind, muls, adds, steps_opMany_rate]
      rw [massDP_steps_eq l a b, massDP_steps_eq r (Program.massDP l a).val (Program.massDP l b).val]

/-- INTERNAL: the normalisation DP's tally, structurally: `vtreeNodes V · (D · q
+ 3D³)` bounds `Charged.steps rate (Program.massDP P a)` whenever `D` bounds the
circuit's `gateWidth` and `q` bounds the tree's `leafDomMax`.  A leaf contributes
`g · (m−1) ≤ D · q` directly (no candidate-set factor: the DP touches every
leaf-table entry exactly once); an internal node contributes `3 · g · gl · gr ≤
3D³` on top of its two children.
TEXLINE: main.tex:967 -/
theorem massDP_steps_le {α : Type u} (D q : ℕ) :
    ∀ {V : Vtree} {g : ℕ} (P : Circuit V g) (a : α),
      gateWidth P ≤ D → leafDomMax V ≤ q →
      (Charged.steps rate (Program.massDP P a) : ℝ)
        ≤ (vtreeNodes V : ℝ) * ((D : ℝ) * q + 3 * (D : ℝ) ^ 3)
  | _, _, @Circuit.leaf m g θ, a, hD, hq => by
      have hstep : Charged.steps rate (Program.massDP (Circuit.leaf θ) a) = g * (m - 1) := by
        simp only [Program.massDP, adds, steps_opMany_rate]
      simp only [gateWidth_leaf] at hD
      simp only [leafDomMax_leaf] at hq
      rw [hstep, massDP_vtreeNodes_leaf]
      have h1 : g * (m - 1) ≤ g * m := Nat.mul_le_mul_left g (Nat.sub_le m 1)
      have h2 : g * m ≤ D * q := Nat.mul_le_mul hD hq
      have h3 : g * (m - 1) ≤ D * q := h1.trans h2
      have h3' : ((g * (m - 1) : ℕ) : ℝ) ≤ (D : ℝ) * q := by exact_mod_cast h3
      have hD30 : (0:ℝ) ≤ 3 * (D:ℝ) ^ 3 := by positivity
      rw [Nat.cast_one, one_mul]
      linarith
  | _, _, @Circuit.node Vl Vr gl gr g l r c, a, hD, hq => by
      have hstep : Charged.steps rate (Program.massDP (Circuit.node l r c) a) =
          Charged.steps rate (Program.massDP l a) + Charged.steps rate (Program.massDP r a)
          + (2 * g * gl * gr) + (g * gl * gr) := by
        simp only [Program.massDP, Charged.steps_bind, muls, adds, steps_opMany_rate]
        rw [massDP_steps_eq r (Program.massDP l a).val a]
        ring
      simp only [gateWidth_node] at hD
      simp only [leafDomMax_node] at hq
      have hDl : gateWidth l ≤ D := (le_max_left _ _).trans ((le_max_right _ _).trans hD)
      have hDr : gateWidth r ≤ D := (le_max_right _ _).trans ((le_max_right _ _).trans hD)
      have hg : g ≤ D := (le_max_left _ _).trans hD
      have hql : leafDomMax Vl ≤ q := (le_max_left _ _).trans hq
      have hqr : leafDomMax Vr ≤ q := (le_max_right _ _).trans hq
      have IHl := massDP_steps_le D q l a hDl hql
      have IHr := massDP_steps_le D q r a hDr hqr
      have hwires : g * gl * gr ≤ D ^ 3 := by
        have h1 : gl ≤ D := (massDP_self_le_gateWidth l).trans hDl
        have h2 : gr ≤ D := (massDP_self_le_gateWidth r).trans hDr
        have h3 : g * gl * gr ≤ D * D * D := Nat.mul_le_mul (Nat.mul_le_mul hg h1) h2
        have heq : D * D * D = D ^ 3 := by ring
        omega
      have hwires' : (g:ℝ) * gl * gr ≤ (D:ℝ) ^ 3 := by exact_mod_cast hwires
      have hDq0 : (0:ℝ) ≤ (D:ℝ) * q := by positivity
      have hgl3 : 2 * (g:ℝ) * gl * gr + (g:ℝ) * gl * gr
          ≤ (D:ℝ) * q + 3 * (D:ℝ) ^ 3 := by nlinarith [hwires']
      rw [hstep, massDP_vtreeNodes_node]
      push_cast
      generalize hZ : (D:ℝ) * q + 3 * (D:ℝ) ^ 3 = Z at IHl IHr hgl3 ⊢
      have hdist : ((vtreeNodes Vl : ℝ) + vtreeNodes Vr + 1) * Z
          = (vtreeNodes Vl : ℝ) * Z + (vtreeNodes Vr : ℝ) * Z + Z := by ring
      rw [hdist]
      linarith [IHl, IHr, hgl3]

end TvDomainReduction.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · all declarations, no `sorry`; used by `Analysis.WtaTimeProof.wta_fpras_time_proof`.
-/
