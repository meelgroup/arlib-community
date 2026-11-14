/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofLocalCapPrefix

/-!
# Compositional finite-query prefixes

Equality after applying `withQueryCap` forgets how much budget remains at a
successful leaf, and is therefore not by itself preserved by monadic bind.
`QueryPrefixEq` records the program tree through a fixed number of query
nodes while treating random draws as cost-free.  It is preserved by bind and
implies equality after the corresponding global cutoff.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory

/-- Two oracle programs have the same observable tree through `fuel` query
nodes. At fuel zero all query nodes are indistinguishable because the outer
cutoff aborts before issuing either query. -/
inductive MembershipOracleProgram.QueryPrefixEq {n : ℕ} {Result : Type} :
    ℕ → MembershipOracleProgram n Result →
      MembershipOracleProgram n Result → Prop where
  | pure (fuel : ℕ) (result : Result) :
      QueryPrefixEq fuel (.pure result) (.pure result)
  | queryZero (point₁ point₂ : AmbientSpace n)
      (next₁ next₂ : Bool → MembershipOracleProgram n Result) :
      QueryPrefixEq 0 (.query point₁ next₁) (.query point₂ next₂)
  | querySucc (fuel : ℕ) (point : AmbientSpace n)
      (next₁ next₂ : Bool → MembershipOracleProgram n Result)
      (hnext : ∀ answer, QueryPrefixEq fuel (next₁ answer) (next₂ answer)) :
      QueryPrefixEq (fuel + 1) (.query point next₁) (.query point next₂)
  | randomNat (fuel : ℕ) (law : PMF ℕ)
      (next₁ next₂ : ℕ → MembershipOracleProgram n Result)
      (hnext : ∀ seed, QueryPrefixEq fuel (next₁ seed) (next₂ seed)) :
      QueryPrefixEq fuel (.randomNat law next₁) (.randomNat law next₂)
  | randomPoint (fuel : ℕ) (law : Measure (AmbientSpace n))
      (hprob₁ hprob₂ : IsProbabilityMeasure law)
      (next₁ next₂ : AmbientSpace n → MembershipOracleProgram n Result)
      (hnext : ∀ point, QueryPrefixEq fuel (next₁ point) (next₂ point)) :
      QueryPrefixEq fuel (.randomPoint law hprob₁ next₁)
        (.randomPoint law hprob₂ next₂)
  | randomReal (fuel : ℕ) (law : Measure ℝ)
      (hprob₁ hprob₂ : IsProbabilityMeasure law)
      (next₁ next₂ : ℝ → MembershipOracleProgram n Result)
      (hnext : ∀ value, QueryPrefixEq fuel (next₁ value) (next₂ value)) :
      QueryPrefixEq fuel (.randomReal law hprob₁ next₁)
        (.randomReal law hprob₂ next₂)

namespace MembershipOracleProgram.QueryPrefixEq

theorem refl {n : ℕ} {Result : Type} :
  ∀ (fuel : ℕ) (program : MembershipOracleProgram n Result),
      QueryPrefixEq fuel program program := by
  intro fuel program
  induction program generalizing fuel with
  | pure result => exact .pure fuel result
  | query point next ih =>
      cases fuel with
      | zero => exact .queryZero point point next next
      | succ fuel =>
          exact .querySucc fuel point next next fun answer => ih answer fuel
  | randomNat law next ih =>
      exact .randomNat fuel law next next fun seed => ih seed fuel
  | randomPoint law hprob next ih =>
      exact .randomPoint fuel law hprob hprob next next fun point => ih point fuel
  | randomReal law hprob next ih =>
      exact .randomReal fuel law hprob hprob next next fun value => ih value fuel

theorem mono {n : ℕ} {Result : Type} {large small : ℕ}
    {left right : MembershipOracleProgram n Result}
    (h : QueryPrefixEq large left right) (hle : small ≤ large) :
    QueryPrefixEq small left right := by
  induction h generalizing small with
  | pure fuel result => exact .pure small result
  | queryZero point₁ point₂ next₁ next₂ =>
      have : small = 0 := by omega
      subst small
      exact .queryZero point₁ point₂ next₁ next₂
  | querySucc fuel point next₁ next₂ hnext ih =>
      cases small with
      | zero => exact .queryZero point point next₁ next₂
      | succ small =>
          exact .querySucc small point next₁ next₂ fun answer =>
            ih answer (by omega)
  | randomNat fuel law next₁ next₂ hnext ih =>
      exact .randomNat small law next₁ next₂ fun seed => ih seed hle
  | randomPoint fuel law hprob₁ hprob₂ next₁ next₂ hnext ih =>
      exact .randomPoint small law hprob₁ hprob₂ next₁ next₂
        fun point => ih point hle
  | randomReal fuel law hprob₁ hprob₂ next₁ next₂ hnext ih =>
      exact .randomReal small law hprob₁ hprob₂ next₁ next₂
        fun value => ih value hle

/-- Prefix equivalence is preserved by a dependent continuation when the
continuations agree at every possible residual budget. -/
theorem bind_of_residual {n : ℕ} {A B : Type} {fuel : ℕ}
    {left right : MembershipOracleProgram n A}
    {nextLeft nextRight : A → MembershipOracleProgram n B}
    (h : QueryPrefixEq fuel left right)
    (hnext : ∀ residual, residual ≤ fuel → ∀ result,
      QueryPrefixEq residual (nextLeft result) (nextRight result)) :
    QueryPrefixEq fuel (left.bind nextLeft) (right.bind nextRight) := by
  induction h with
  | pure fuel result =>
      simpa only [MembershipOracleProgram.bind] using hnext fuel le_rfl result
  | queryZero point₁ point₂ branch₁ branch₂ =>
      simp only [MembershipOracleProgram.bind]
      exact .queryZero point₁ point₂ _ _
  | querySucc fuel point branch₁ branch₂ hbranch ih =>
      simp only [MembershipOracleProgram.bind]
      exact .querySucc fuel point _ _ fun answer =>
        ih answer fun residual hres result =>
          hnext residual (by omega) result
  | randomNat fuel law branch₁ branch₂ hbranch ih =>
      simp only [MembershipOracleProgram.bind]
      exact .randomNat fuel law _ _ fun seed => ih seed hnext
  | randomPoint fuel law hprob₁ hprob₂ branch₁ branch₂ hbranch ih =>
      simp only [MembershipOracleProgram.bind]
      exact .randomPoint fuel law hprob₁ hprob₂ _ _ fun point =>
        ih point hnext
  | randomReal fuel law hprob₁ hprob₂ branch₁ branch₂ hbranch ih =>
      simp only [MembershipOracleProgram.bind]
      exact .randomReal fuel law hprob₁ hprob₂ _ _ fun value =>
        ih value hnext

theorem bind {n : ℕ} {A B : Type} {fuel : ℕ}
    {left right : MembershipOracleProgram n A}
    {nextLeft nextRight : A → MembershipOracleProgram n B}
    (h : QueryPrefixEq fuel left right)
    (hnext : ∀ result,
      QueryPrefixEq fuel (nextLeft result) (nextRight result)) :
    QueryPrefixEq fuel (left.bind nextLeft) (right.bind nextRight) :=
  h.bind_of_residual fun residual hres result => (hnext result).mono hres

/-- Prefix-equivalent programs have definitionally equal globally capped
syntax. -/
theorem withQueryCap_eq {n : ℕ} {Result : Type} {fuel : ℕ}
    {left right : MembershipOracleProgram n Result}
    (h : QueryPrefixEq fuel left right) :
    left.withQueryCap fuel = right.withQueryCap fuel := by
  induction h with
  | pure => rfl
  | queryZero => rfl
  | querySucc fuel point next₁ next₂ hnext ih =>
      simp only [MembershipOracleProgram.withQueryCap]
      congr 1
      funext answer
      exact ih answer
  | randomNat fuel law next₁ next₂ hnext ih =>
      simp only [MembershipOracleProgram.withQueryCap]
      congr 1
      funext seed
      exact ih seed
  | randomPoint fuel law hprob₁ hprob₂ next₁ next₂ hnext ih =>
      simp only [MembershipOracleProgram.withQueryCap]
      congr 1
      funext point
      exact ih point
  | randomReal fuel law hprob₁ hprob₂ next₁ next₂ hnext ih =>
      simp only [MembershipOracleProgram.withQueryCap]
      congr 1
      funext value
      exact ih value

end MembershipOracleProgram.QueryPrefixEq

end ArlibCommunity.Algorithms.CV18
