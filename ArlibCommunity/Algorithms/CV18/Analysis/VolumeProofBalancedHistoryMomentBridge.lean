/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedFullHistory
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedPhaseInstantiation
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofPhaseMomentAssembly

/-!
# Ordered balanced-history variables for the CV18 moment argument

The dependent-product recurrence must use the chronological Markov order.
This file gives the explicit equivalence from schedule positions to the
fixed/accelerated/terminal ideal phase type and the measurable history
coordinates in that order.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

noncomputable def figureOneChronologicalPhaseOfFin (q : VolumeParams) :
    Fin (figureOneDependentPhaseCount q) → FigureOneIdealPhase q := fun i =>
  if hi : i.1 < terminalPhaseSteps q then
    let k : Fin (terminalPhaseSteps q) := ⟨i.1, hi⟩
    if hk : scheduleValue q k ≤ 1 then
      .fixed ⟨k, hk⟩
    else
      .accelerated ⟨k, hk⟩
  else
    .terminal

noncomputable def figureOneChronologicalFinOfPhase (q : VolumeParams) :
    FigureOneIdealPhase q → Fin (figureOneDependentPhaseCount q)
  | .fixed k => ⟨k.1.1, by
      rw [figureOneDependentPhaseCount]
      omega⟩
  | .accelerated k => ⟨k.1.1, by
      rw [figureOneDependentPhaseCount]
      omega⟩
  | .terminal => ⟨terminalPhaseSteps q, by
      rw [figureOneDependentPhaseCount]
      omega⟩

theorem figureOneChronologicalPhaseOfFin_leftInverse (q : VolumeParams) :
    Function.LeftInverse (figureOneChronologicalFinOfPhase q)
      (figureOneChronologicalPhaseOfFin q) := by
  intro i
  by_cases hi : i.1 < terminalPhaseSteps q
  · simp only [figureOneChronologicalPhaseOfFin, hi, ↓reduceDIte]
    split_ifs <;> simp only [figureOneChronologicalFinOfPhase]
  · simp only [figureOneChronologicalPhaseOfFin, hi, ↓reduceDIte,
      figureOneChronologicalFinOfPhase]
    apply Fin.ext
    change terminalPhaseSteps q = i.1
    have hilimit := i.2
    change i.1 < terminalPhaseSteps q + 1 at hilimit
    omega

theorem figureOneChronologicalPhaseOfFin_rightInverse (q : VolumeParams) :
    Function.RightInverse (figureOneChronologicalFinOfPhase q)
      (figureOneChronologicalPhaseOfFin q) := by
  intro phase
  cases phase with
  | fixed k =>
      simp [figureOneChronologicalPhaseOfFin,
        figureOneChronologicalFinOfPhase, k.1.2, k.2]
  | accelerated k =>
      simp [figureOneChronologicalPhaseOfFin,
        figureOneChronologicalFinOfPhase, k.1.2, k.2]
  | terminal =>
      simp [figureOneChronologicalPhaseOfFin,
        figureOneChronologicalFinOfPhase]

/-- Explicit chronological ordering: scheduled transition `k` occupies
position `k`, and the terminal Gaussian-to-uniform phase is last. -/
noncomputable def figureOneChronologicalPhaseOrder (q : VolumeParams) :
    Fin (figureOneDependentPhaseCount q) ≃ FigureOneIdealPhase q where
  toFun := figureOneChronologicalPhaseOfFin q
  invFun := figureOneChronologicalFinOfPhase q
  left_inv := figureOneChronologicalPhaseOfFin_leftInverse q
  right_inv := figureOneChronologicalPhaseOfFin_rightInverse q

@[simp] theorem figureOneChronologicalPhaseOrder_apply_transition
    (q : VolumeParams) (k : Fin (terminalPhaseSteps q)) :
    figureOneChronologicalPhaseOrder q
        ⟨k, by rw [figureOneDependentPhaseCount]; omega⟩ =
      if hk : scheduleValue q k ≤ 1 then
        FigureOneIdealPhase.fixed ⟨k, hk⟩
      else FigureOneIdealPhase.accelerated ⟨k, hk⟩ := by
  simp [figureOneChronologicalPhaseOrder,
    figureOneChronologicalPhaseOfFin, k.isLt]

@[simp] theorem figureOneChronologicalPhaseOrder_apply_terminal
    (q : VolumeParams) :
    figureOneChronologicalPhaseOrder q
        ⟨terminalPhaseSteps q, by
          rw [figureOneDependentPhaseCount]
          omega⟩ = FigureOneIdealPhase.terminal := by
  simp [figureOneChronologicalPhaseOrder,
    figureOneChronologicalPhaseOfFin]

/-- Chronological phase selected by a one-based dependent-product index. -/
noncomputable def figureOneChronologicalPhaseAt (q : VolumeParams) (j : ℕ) :
    FigureOneIdealPhase q :=
  figureOneChronologicalPhaseOrder q
    ⟨(j - 1) % figureOneDependentPhaseCount q,
      Nat.mod_lt _ (figureOneDependentPhaseCount_pos q)⟩

/-- The ideal first moment in chronological (one-based) phase order. -/
noncomputable def figureOneChronologicalRawMean
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ) : ℝ :=
  figureOneIdealPhaseMean q I (figureOneChronologicalPhaseAt q j)

/-- The ideal relative second-moment factor in chronological phase order. -/
noncomputable def figureOneChronologicalMomentFactor
    (q : VolumeParams) (j : ℕ) : ℝ :=
  figureOneIdealPhaseFactor q (figureOneChronologicalPhaseAt q j)

theorem figureOneChronologicalRawMean_pos
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ) :
    0 < figureOneChronologicalRawMean q I j :=
  figureOneIdealPhaseMean_pos q I _

theorem figureOneChronologicalMomentFactor_one_le
    (q : VolumeParams) (j : ℕ) :
    1 ≤ figureOneChronologicalMomentFactor q j :=
  figureOneIdealPhaseFactor_one_le q _

theorem figureOneChronologicalRawMean_product
    (q : VolumeParams) (I : VolumeInput q.n) :
    dependentPhaseMeanProduct (figureOneChronologicalRawMean q I)
        (figureOneDependentPhaseCount q) =
      ∏ phase, figureOneIdealPhaseMean q I phase := by
  rw [dependentPhaseMeanProduct]
  calc
    (∏ j ∈ Finset.range (figureOneDependentPhaseCount q),
        figureOneChronologicalRawMean q I (j + 1)) =
        ∏ j ∈ Finset.range (figureOneDependentPhaseCount q),
          figureOneIdealPhaseMean q I
            (figureOneChronologicalPhaseAt q (j + 1)) := by
      apply Finset.prod_congr rfl
      intro j hj
      rfl
    _ = ∏ i : Fin (figureOneDependentPhaseCount q),
          figureOneIdealPhaseMean q I (figureOneChronologicalPhaseOrder q i) := by
      rw [← Fin.prod_univ_eq_prod_range
        (fun j => figureOneIdealPhaseMean q I
          (figureOneChronologicalPhaseAt q (j + 1)))]
      apply Fintype.prod_congr
      intro i
      simp only [figureOneChronologicalPhaseAt, Nat.add_sub_cancel,
        Nat.mod_eq_of_lt i.isLt]
    _ = ∏ phase, figureOneIdealPhaseMean q I phase :=
      (figureOneChronologicalPhaseOrder q).prod_comp
        (figureOneIdealPhaseMean q I)

theorem figureOneChronologicalMomentFactor_product
    (q : VolumeParams) :
    dependentPhaseMeanProduct (figureOneChronologicalMomentFactor q)
        (figureOneDependentPhaseCount q) =
      ∏ phase, figureOneIdealPhaseFactor q phase := by
  rw [dependentPhaseMeanProduct]
  calc
    (∏ j ∈ Finset.range (figureOneDependentPhaseCount q),
        figureOneChronologicalMomentFactor q (j + 1)) =
        ∏ j ∈ Finset.range (figureOneDependentPhaseCount q),
          figureOneIdealPhaseFactor q
            (figureOneChronologicalPhaseAt q (j + 1)) := by
      apply Finset.prod_congr rfl
      intro j hj
      rfl
    _ = ∏ i : Fin (figureOneDependentPhaseCount q),
          figureOneIdealPhaseFactor q (figureOneChronologicalPhaseOrder q i) := by
      rw [← Fin.prod_univ_eq_prod_range
        (fun j => figureOneIdealPhaseFactor q
          (figureOneChronologicalPhaseAt q (j + 1)))]
      apply Fintype.prod_congr
      intro i
      simp only [figureOneChronologicalPhaseAt, Nat.add_sub_cancel,
        Nat.mod_eq_of_lt i.isLt]
    _ = ∏ phase, figureOneIdealPhaseFactor q phase :=
      (figureOneChronologicalPhaseOrder q).prod_comp
        (figureOneIdealPhaseFactor q)

/-- Schedule coordinate represented by an ideal phase. -/
noncomputable def figureOneIdealPhaseHistoryIndex (q : VolumeParams) :
    FigureOneIdealPhase q → ℕ
  | .fixed k => k.1.1
  | .accelerated k => k.1.1
  | .terminal => terminalPhaseSteps q

theorem figureOneIdealPhaseHistoryIndex_chronologicalOrder
    (q : VolumeParams) (i : Fin (figureOneDependentPhaseCount q)) :
    figureOneIdealPhaseHistoryIndex q
        (figureOneChronologicalPhaseOrder q i) = i.1 := by
  by_cases hi : i.1 < terminalPhaseSteps q
  · simp only [figureOneChronologicalPhaseOrder, Equiv.coe_fn_mk,
      figureOneChronologicalPhaseOfFin, hi, ↓reduceDIte]
    split_ifs <;> rfl
  · have hilimit := i.2
    change i.1 < terminalPhaseSteps q + 1 at hilimit
    have hieq : i.1 = terminalPhaseSteps q := by omega
    simp [figureOneChronologicalPhaseOrder,
      figureOneChronologicalPhaseOfFin, figureOneIdealPhaseHistoryIndex, hi,
      hieq]

/-- Raw coordinate of a completed balanced history.  Failure is represented
by zero, consistently with the optional executable output. -/
noncomputable def balancedCoolingHistoryPhaseCoordinate
    (q : VolumeParams) (phase : FigureOneIdealPhase q) :
    Option (BalancedCoolingHistory q.n) → ℝ
  | none => 0
  | some history => history.1 (figureOneIdealPhaseHistoryIndex q phase)

theorem measurable_balancedCoolingHistoryPhaseCoordinate
    (q : VolumeParams) (phase : FigureOneIdealPhase q) :
    Measurable (balancedCoolingHistoryPhaseCoordinate q phase) := by
  have hsome : Measurable fun history : BalancedCoolingHistory q.n =>
      history.1 (figureOneIdealPhaseHistoryIndex q phase) :=
    (measurable_pi_apply (figureOneIdealPhaseHistoryIndex q phase)).comp
      measurable_fst
  convert Measurable.optionElim (0 : ℝ) hsome using 1
  funext history
  cases history <;> rfl

/-- The phase variables in the chronological order required by Lemma 7.17. -/
noncomputable def balancedCoolingChronologicalPhaseVariable
    (q : VolumeParams) :
    ℕ → Option (BalancedCoolingHistory q.n) → ℝ := fun j =>
  balancedCoolingHistoryPhaseCoordinate q
    (figureOneChronologicalPhaseAt q j)

theorem measurable_balancedCoolingChronologicalPhaseVariable
    (q : VolumeParams) (j : ℕ) :
    Measurable (balancedCoolingChronologicalPhaseVariable q j) :=
  measurable_balancedCoolingHistoryPhaseCoordinate q _

theorem balancedCoolingChronologicalPhaseVariable_apply_succ
    (q : VolumeParams) (j : ℕ) (hj : j < figureOneDependentPhaseCount q)
    (history : Option (BalancedCoolingHistory q.n)) :
    balancedCoolingChronologicalPhaseVariable q (j + 1) history =
      match history with
      | none => 0
      | some value => value.1 j := by
  cases history with
  | none => rfl
  | some value =>
      simp only [balancedCoolingChronologicalPhaseVariable,
        balancedCoolingHistoryPhaseCoordinate,
        figureOneChronologicalPhaseAt, Nat.add_sub_cancel,
        Nat.mod_eq_of_lt hj]
      rw [figureOneIdealPhaseHistoryIndex_chronologicalOrder]

/-- Bounded nonnegative version of the executable history coordinate.  This
is the variable required by the `MemLp`-based truncation layer.  On histories
whose stored phase averages lie in the paper's range `[0, exp (1/2)]`, it is
definitionally the raw stored average. -/
noncomputable def balancedCoolingChronologicalPhaseVariableClamped
    (q : VolumeParams) :
    ℕ → Option (BalancedCoolingHistory q.n) → ℝ := fun j history =>
  min (max 0 (balancedCoolingChronologicalPhaseVariable q j history))
    (Real.exp (1 / 2 : ℝ))

theorem measurable_balancedCoolingChronologicalPhaseVariableClamped
    (q : VolumeParams) (j : ℕ) :
    Measurable (balancedCoolingChronologicalPhaseVariableClamped q j) := by
  exact ((measurable_const.max
    (measurable_balancedCoolingChronologicalPhaseVariable q j)).min
      measurable_const)

theorem balancedCoolingChronologicalPhaseVariableClamped_nonneg
    (q : VolumeParams) (j : ℕ)
    (history : Option (BalancedCoolingHistory q.n)) :
    0 ≤ balancedCoolingChronologicalPhaseVariableClamped q j history := by
  exact le_min (le_max_left _ _) (Real.exp_pos _).le

theorem balancedCoolingChronologicalPhaseVariableClamped_le
    (q : VolumeParams) (j : ℕ)
    (history : Option (BalancedCoolingHistory q.n)) :
    balancedCoolingChronologicalPhaseVariableClamped q j history ≤
      Real.exp (1 / 2 : ℝ) :=
  min_le_right _ _

theorem memLp_balancedCoolingChronologicalPhaseVariableClamped
    (q : VolumeParams) (mu : Measure (Option (BalancedCoolingHistory q.n)))
    [IsFiniteMeasure mu] (j : ℕ) :
    MemLp (balancedCoolingChronologicalPhaseVariableClamped q j) 2 mu := by
  apply MemLp.of_bound
    (measurable_balancedCoolingChronologicalPhaseVariableClamped q j).aestronglyMeasurable
    (Real.exp (1 / 2 : ℝ))
  filter_upwards with history
  rw [Real.norm_eq_abs, abs_of_nonneg
    (balancedCoolingChronologicalPhaseVariableClamped_nonneg q j history)]
  exact balancedCoolingChronologicalPhaseVariableClamped_le q j history

theorem balancedCoolingChronologicalPhaseVariableClamped_eq
    (q : VolumeParams) (j : ℕ)
    (history : Option (BalancedCoolingHistory q.n))
    (h0 : 0 ≤ balancedCoolingChronologicalPhaseVariable q j history)
    (hupper : balancedCoolingChronologicalPhaseVariable q j history ≤
      Real.exp (1 / 2 : ℝ)) :
    balancedCoolingChronologicalPhaseVariableClamped q j history =
      balancedCoolingChronologicalPhaseVariable q j history := by
  unfold balancedCoolingChronologicalPhaseVariableClamped
  rw [max_eq_right h0, min_eq_left hupper]

/-- Reindex a phase-by-phase first-moment identification into the chronological
one-based family used by the dependent-product recurrence. -/
theorem integral_balancedCoolingChronologicalPhaseVariable_eq
    (q : VolumeParams) (I : VolumeInput q.n)
    (mu : Measure (Option (BalancedCoolingHistory q.n)))
    (hmean : ∀ phase,
      (∫ history, balancedCoolingHistoryPhaseCoordinate q phase history ∂mu) =
        figureOneIdealPhaseMean q I phase)
    (j : ℕ) :
    (∫ history, balancedCoolingChronologicalPhaseVariable q j history ∂mu) =
      figureOneChronologicalRawMean q I j := by
  exact hmean (figureOneChronologicalPhaseAt q j)

/-- Reindex the ideal per-phase second-moment bounds into chronological order. -/
theorem integral_sq_balancedCoolingChronologicalPhaseVariable_le
    (q : VolumeParams) (I : VolumeInput q.n)
    (mu : Measure (Option (BalancedCoolingHistory q.n)))
    (hsecond : ∀ phase,
      (∫ history,
        balancedCoolingHistoryPhaseCoordinate q phase history ^ 2 ∂mu) ≤
          figureOneIdealPhaseFactor q phase *
            figureOneIdealPhaseMean q I phase ^ 2)
    (j : ℕ) :
    (∫ history,
      balancedCoolingChronologicalPhaseVariable q j history ^ 2 ∂mu) ≤
        figureOneChronologicalMomentFactor q j *
          figureOneChronologicalRawMean q I j ^ 2 := by
  exact hsecond (figureOneChronologicalPhaseAt q j)

/-- If the executable history law is supported on the paper's weight range,
the bounded `MemLp` variables have exactly the same first moments as the raw
history coordinates. -/
theorem integral_balancedCoolingChronologicalPhaseVariableClamped_eq
    (q : VolumeParams) (I : VolumeInput q.n)
    (mu : Measure (Option (BalancedCoolingHistory q.n)))
    (hrange : ∀ j,
      ∀ᵐ history ∂mu,
        0 ≤ balancedCoolingChronologicalPhaseVariable q j history ∧
          balancedCoolingChronologicalPhaseVariable q j history ≤
            Real.exp (1 / 2 : ℝ))
    (hmean : ∀ phase,
      (∫ history, balancedCoolingHistoryPhaseCoordinate q phase history ∂mu) =
        figureOneIdealPhaseMean q I phase)
    (j : ℕ) :
    (∫ history,
      balancedCoolingChronologicalPhaseVariableClamped q j history ∂mu) =
        figureOneChronologicalRawMean q I j := by
  rw [integral_congr_ae]
  · exact integral_balancedCoolingChronologicalPhaseVariable_eq q I mu hmean j
  · filter_upwards [hrange j] with history hhistory
    exact balancedCoolingChronologicalPhaseVariableClamped_eq q j history
      hhistory.1 hhistory.2

/-- The analogous transfer for second moments. -/
theorem integral_sq_balancedCoolingChronologicalPhaseVariableClamped_le
    (q : VolumeParams) (I : VolumeInput q.n)
    (mu : Measure (Option (BalancedCoolingHistory q.n)))
    (hrange : ∀ j,
      ∀ᵐ history ∂mu,
        0 ≤ balancedCoolingChronologicalPhaseVariable q j history ∧
          balancedCoolingChronologicalPhaseVariable q j history ≤
            Real.exp (1 / 2 : ℝ))
    (hsecond : ∀ phase,
      (∫ history,
        balancedCoolingHistoryPhaseCoordinate q phase history ^ 2 ∂mu) ≤
          figureOneIdealPhaseFactor q phase *
            figureOneIdealPhaseMean q I phase ^ 2)
    (j : ℕ) :
    (∫ history,
      balancedCoolingChronologicalPhaseVariableClamped q j history ^ 2 ∂mu) ≤
        figureOneChronologicalMomentFactor q j *
          figureOneChronologicalRawMean q I j ^ 2 := by
  calc
    (∫ history,
        balancedCoolingChronologicalPhaseVariableClamped q j history ^ 2 ∂mu) =
        ∫ history,
          balancedCoolingChronologicalPhaseVariable q j history ^ 2 ∂mu := by
      apply integral_congr_ae
      filter_upwards [hrange j] with history hhistory
      rw [balancedCoolingChronologicalPhaseVariableClamped_eq q j history
        hhistory.1 hhistory.2]
    _ ≤ figureOneChronologicalMomentFactor q j *
          figureOneChronologicalRawMean q I j ^ 2 :=
      integral_sq_balancedCoolingChronologicalPhaseVariable_le
        q I mu hsecond j

/-- Retained target point exposed by a history, with the origin on failure. -/
noncomputable def balancedCoolingHistoryRetainedState (q : VolumeParams) :
    Option (BalancedCoolingHistory q.n) → AmbientSpace q.n
  | none => 0
  | some history => history.2.2.2

theorem measurable_balancedCoolingHistoryRetainedState (q : VolumeParams) :
    Measurable (balancedCoolingHistoryRetainedState q) := by
  have hsome : Measurable fun history : BalancedCoolingHistory q.n =>
      history.2.2.2 := measurable_snd.comp (measurable_snd.comp measurable_snd)
  convert Measurable.optionElim (0 : AmbientSpace q.n) hsome using 1
  funext history
  cases history <;> rfl

/-- Accumulated product exposed by a history, with zero on failure. -/
noncomputable def balancedCoolingHistoryProduct (q : VolumeParams) :
    Option (BalancedCoolingHistory q.n) → ℝ
  | none => 0
  | some history => history.2.2.1

theorem measurable_balancedCoolingHistoryProduct (q : VolumeParams) :
    Measurable (balancedCoolingHistoryProduct q) := by
  have hsome : Measurable fun history : BalancedCoolingHistory q.n =>
      history.2.2.1 := measurable_fst.comp (measurable_snd.comp measurable_snd)
  convert Measurable.optionElim (0 : ℝ) hsome using 1
  funext history
  cases history <;> rfl

/-- The retained-state marginal of the complete post-initial Figure-One
history.  This is the precise marginal that must be shown warm at the next
phase before applying the concrete Lemma 7.17(c) specialization. -/
noncomputable def balancedFigureOneFullHistoryRetainedLaw
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (point : AmbientSpace q.n) :
    Measure (AmbientSpace q.n) :=
  (balancedFigureOneFullHistoryLaw parameters q I point).map
    (balancedCoolingHistoryRetainedState q)

theorem balancedFigureOneFullHistoryRetainedLaw_isProbabilityMeasure
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (point : AmbientSpace q.n) :
    IsProbabilityMeasure
      (balancedFigureOneFullHistoryRetainedLaw parameters q I point) := by
  let _ : IsProbabilityMeasure
      (balancedFigureOneFullHistoryLaw parameters q I point) :=
    (balancedFigureOneFullHistoryLaw_measurable_and_probability
      parameters q I).2 point
  exact Measure.isProbabilityMeasure_map
    (measurable_balancedCoolingHistoryRetainedState q).aemeasurable

theorem memLp_balancedFigureOneFullHistory_chronologicalPhaseVariableClamped
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (point : AmbientSpace q.n) (j : ℕ) :
    MemLp (balancedCoolingChronologicalPhaseVariableClamped q j) 2
      (balancedFigureOneFullHistoryLaw parameters q I point) := by
  let _ : IsProbabilityMeasure
      (balancedFigureOneFullHistoryLaw parameters q I point) :=
    (balancedFigureOneFullHistoryLaw_measurable_and_probability
      parameters q I).2 point
  exact memLp_balancedCoolingChronologicalPhaseVariableClamped q _ j

/-- Structural invariant needed to identify the stored accumulated product
with the product of the chronological phase variables.  It is stated on the
optional history so failure is represented by zero on both sides. -/
def BalancedCoolingHistoryHasProduct (m : ℕ) :
    Option (BalancedCoolingHistory n) → Prop
  | none => True
  | some history =>
      history.2.1 = m ∧
        history.2.2.1 = ∏ j ∈ Finset.range m, history.1 j

theorem prod_range_cons_sequence (ratio : ℝ) (sequence : ℕ → ℝ) (m : ℕ) :
    (∏ j ∈ Finset.range (m + 1),
        if j = 0 then ratio else sequence (j - 1)) =
      ratio * ∏ j ∈ Finset.range m, sequence j := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        (∏ j ∈ Finset.range (m + 1 + 1),
            if j = 0 then ratio else sequence (j - 1)) =
            (∏ j ∈ Finset.range (m + 1),
              if j = 0 then ratio else sequence (j - 1)) * sequence m := by
              rw [Finset.prod_range_succ]
              simp
        _ = (ratio * ∏ j ∈ Finset.range m, sequence j) * sequence m := by
              rw [ih]
        _ = ratio * ∏ j ∈ Finset.range (m + 1), sequence j := by
              rw [Finset.prod_range_succ]
              ring

theorem prod_range_snoc_sequence (ratio : ℝ) (sequence : ℕ → ℝ) (m : ℕ) :
    (∏ j ∈ Finset.range (m + 1),
        if j = m then ratio else sequence j) =
      (∏ j ∈ Finset.range m, sequence j) * ratio := by
  rw [Finset.prod_range_succ]
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    rw [if_neg]
    exact ne_of_lt (Finset.mem_range.mp hj)
  · rw [if_pos rfl]

theorem BalancedCoolingHistoryHasProduct.cons
    {history : Option (BalancedCoolingHistory n)}
    (hproduct : BalancedCoolingHistoryHasProduct m history) (ratio : ℝ) :
    BalancedCoolingHistoryHasProduct (m + 1)
      (balancedCoolingHistoryCons ratio history) := by
  cases history with
  | none => trivial
  | some history =>
      simp only [BalancedCoolingHistoryHasProduct,
        balancedCoolingHistoryCons] at hproduct ⊢
      constructor
      · rw [hproduct.1]
      · rw [prod_range_cons_sequence, ← hproduct.2]

theorem BalancedCoolingHistoryHasProduct.snocTerminal
    {history : BalancedCoolingHistory n}
    (hproduct : BalancedCoolingHistoryHasProduct m (some history))
    (terminal : Option (ℝ × AmbientSpace n)) :
    BalancedCoolingHistoryHasProduct (m + 1)
      (balancedCoolingHistorySnocTerminal history terminal) := by
  cases terminal with
  | none => trivial
  | some terminal =>
      simp only [BalancedCoolingHistoryHasProduct,
        balancedCoolingHistorySnocTerminal] at hproduct ⊢
      constructor
      · omega
      · rw [hproduct.1, prod_range_snoc_sequence, ← hproduct.2]

theorem dependentPhaseSampleProduct_balancedCoolingChronological_eq
    (q : VolumeParams) (history : Option (BalancedCoolingHistory q.n))
    (hproduct : BalancedCoolingHistoryHasProduct
      (figureOneDependentPhaseCount q) history) :
    dependentPhaseSampleProduct
        (balancedCoolingChronologicalPhaseVariable q)
        (figureOneDependentPhaseCount q) history =
      balancedCoolingHistoryProduct q history := by
  cases history with
  | none =>
      simp only [dependentPhaseSampleProduct,
        balancedCoolingChronologicalPhaseVariable_apply_succ,
        balancedCoolingHistoryProduct]
      rw [Finset.prod_eq_zero (Finset.mem_range.mpr
        (figureOneDependentPhaseCount_pos q))]
      rfl
  | some history =>
      simp only [BalancedCoolingHistoryHasProduct] at hproduct
      rw [dependentPhaseSampleProduct]
      calc
        (∏ j ∈ Finset.range (figureOneDependentPhaseCount q),
            balancedCoolingChronologicalPhaseVariable q (j + 1)
              (some history)) =
            ∏ j ∈ Finset.range (figureOneDependentPhaseCount q),
              history.1 j := by
          apply Finset.prod_congr rfl
          intro j hj
          rw [balancedCoolingChronologicalPhaseVariable_apply_succ q j
            (Finset.mem_range.mp hj)]
        _ = balancedCoolingHistoryProduct q (some history) := by
          simpa only [balancedCoolingHistoryProduct] using hproduct.2.symm

theorem balancedFigureOneHistoryEstimate_eq_sampleProduct
    (q : VolumeParams) (history : Option (BalancedCoolingHistory q.n))
    (hproduct : BalancedCoolingHistoryHasProduct
      (figureOneDependentPhaseCount q) history) :
    balancedFigureOneHistoryEstimate q history =
      initialGaussianIntegral q *
        dependentPhaseSampleProduct
          (balancedCoolingChronologicalPhaseVariable q)
          (figureOneDependentPhaseCount q) history := by
  rw [dependentPhaseSampleProduct_balancedCoolingChronological_eq
    q history hproduct]
  cases history <;>
    simp [balancedFigureOneHistoryEstimate, balancedCoolingHistoryProduct]

#print axioms figureOneChronologicalPhaseOrder
#print axioms measurable_balancedCoolingChronologicalPhaseVariable
#print axioms measurable_balancedCoolingHistoryRetainedState
#print axioms dependentPhaseSampleProduct_balancedCoolingChronological_eq
#print axioms memLp_balancedFigureOneFullHistory_chronologicalPhaseVariableClamped

end ArlibCommunity.Algorithms.CV18
