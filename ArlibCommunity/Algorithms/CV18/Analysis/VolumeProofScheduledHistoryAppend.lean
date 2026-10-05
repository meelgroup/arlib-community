/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledExecutableFullHistory

/-! # Prefix algebra for scheduled chronological histories -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

/-- Concatenate a completed tail history after an already accumulated prefix. -/
noncomputable def balancedCoolingHistoryConcat
    (head tail : BalancedCoolingHistory n) : BalancedCoolingHistory n :=
  ((fun k => if k < head.2.1 then head.1 k
      else if k < head.2.1 + tail.2.1 then tail.1 (k - head.2.1)
      else head.1 k),
    head.2.1 + tail.2.1,
    head.2.2.1 * tail.2.2.1,
    tail.2.2.2)

theorem balancedCoolingHistoryConcat_initial
    (head : BalancedCoolingHistory n) :
    balancedCoolingHistoryConcat head
        ((fun _ => 0), 0, 1, head.2.2.2) = head := by
  rcases head with ⟨ratios, count, product, point⟩
  unfold balancedCoolingHistoryConcat
  simp only [Nat.add_zero, mul_one]
  congr 1
  funext k
  by_cases hk : k < count
  · simp [hk]
  · simp [hk]

theorem measurable_balancedCoolingHistoryConcat_left
    (head : BalancedCoolingHistory n) :
    Measurable (balancedCoolingHistoryConcat head) := by
  unfold balancedCoolingHistoryConcat
  apply Measurable.prodMk
  · refine measurable_pi_lambda _ fun k => ?_
    by_cases hk : k < head.2.1
    · simp only [hk, if_true]
      exact measurable_const
    · simp only [hk, if_false]
      apply Measurable.ite
      · exact measurableSet_lt measurable_const
          (measurable_const.add (measurable_fst.comp measurable_snd))
      · exact (measurable_pi_apply (k - head.2.1)).comp measurable_fst
      · exact measurable_const
  · fun_prop

noncomputable def balancedCoolingHistoryConcatOption
    (head : BalancedCoolingHistory n) :
    Option (BalancedCoolingHistory n) → Option (BalancedCoolingHistory n)
  | none => none
  | some tail => some (balancedCoolingHistoryConcat head tail)

theorem measurable_balancedCoolingHistoryConcatOption
    (head : BalancedCoolingHistory n) :
    Measurable (balancedCoolingHistoryConcatOption head) := by
  have hsome : Measurable fun tail : BalancedCoolingHistory n =>
      some (balancedCoolingHistoryConcat head tail) :=
    measurable_some.comp (measurable_balancedCoolingHistoryConcat_left head)
  convert Measurable.optionElim (none : Option (BalancedCoolingHistory n)) hsome using 1
  funext tail
  cases tail <;> rfl

theorem balancedCoolingHistoryConcatOption_initial
    (head : BalancedCoolingHistory n) :
    balancedCoolingHistoryConcatOption head
        (some ((fun _ => 0), 0, 1, head.2.2.2)) = some head := by
  simp only [balancedCoolingHistoryConcatOption]
  rw [balancedCoolingHistoryConcat_initial]

theorem balancedCoolingHistoryConcat_snoc_cons
    (head tail : BalancedCoolingHistory n) (ratio : ℝ)
    (nextPoint : AmbientSpace n) :
    balancedCoolingHistoryConcat head
        ((fun k => if k = 0 then ratio else tail.1 (k - 1)),
          tail.2.1 + 1, ratio * tail.2.2.1, tail.2.2.2) =
      balancedCoolingHistoryConcat
        ((fun k => if k = head.2.1 then ratio else head.1 k),
          head.2.1 + 1, head.2.2.1 * ratio, nextPoint) tail := by
  rcases head with ⟨prefixRatios, prefixCount, prefixProduct, prefixPoint⟩
  rcases tail with ⟨tailRatios, tailCount, tailProduct, tailPoint⟩
  unfold balancedCoolingHistoryConcat
  simp only
  congr 1
  · funext k
    by_cases hk : k < prefixCount
    · have hlt : k < prefixCount + (tailCount + 1) := by omega
      have hlt' : k < prefixCount + 1 := by omega
      have hne : k ≠ prefixCount := by omega
      simp [hk, hlt, hlt', hne]
    · have hkp : prefixCount ≤ k := Nat.le_of_not_gt hk
      by_cases heq : k = prefixCount
      · subst k
        simp
      · have hsucc : prefixCount + 1 ≤ k := by omega
        have hnot : ¬ k < prefixCount + 1 := Nat.not_lt_of_ge hsucc
        have hsubpos : k - prefixCount ≠ 0 := by omega
        have hsub : k - (prefixCount + 1) = k - prefixCount - 1 := by omega
        by_cases htail : k < prefixCount + (tailCount + 1)
        · have htail' : k < prefixCount + 1 + tailCount := by omega
          simp [hk, htail, hnot, hsubpos, hsub, htail']
        · have htail' : ¬ k < prefixCount + 1 + tailCount := by omega
          simp [hk, htail, hnot, htail', heq]
  · ring

/-- The recursive executable law, viewed after an already accumulated
chronological prefix.  This is the bridge between front-cons recursion and
the forward snoc interpreter. -/
noncomputable def scheduledExecutableCoolingHistoryFrom
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (variances : List ℝ)
    (head : BalancedCoolingHistory q.n) :
    Measure (Option (BalancedCoolingHistory q.n)) :=
  (scheduledExecutableCoolingHistoryLaw parameters q I variances head.2.2.2).map
    (balancedCoolingHistoryConcatOption head)

theorem scheduledExecutableCoolingHistoryFrom_nil
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (head : BalancedCoolingHistory q.n) :
    scheduledExecutableCoolingHistoryFrom parameters q I [] head =
      Measure.dirac (some head) := by
  unfold scheduledExecutableCoolingHistoryFrom
  rw [scheduledExecutableCoolingHistoryLaw, Measure.map_dirac'
    (measurable_balancedCoolingHistoryConcatOption head)]
  rw [balancedCoolingHistoryConcatOption_initial]

theorem scheduledExecutableCoolingHistoryFrom_singleton
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (sigma2 : ℝ)
    (head : BalancedCoolingHistory q.n) :
    scheduledExecutableCoolingHistoryFrom parameters q I [sigma2] head =
      Measure.dirac (some head) := by
  unfold scheduledExecutableCoolingHistoryFrom
  rw [scheduledExecutableCoolingHistoryLaw, Measure.map_dirac'
    (measurable_balancedCoolingHistoryConcatOption head)]
  rw [balancedCoolingHistoryConcatOption_initial]

theorem scheduledExecutableCoolingHistoryFrom_cons_cons
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (sigma2 tau2 : ℝ) (rest : List ℝ)
    (hsigma2 : 0 < sigma2)
    (htailPositive : ∀ s ∈ tau2 :: rest, 0 < s)
    (head : BalancedCoolingHistory q.n) :
    scheduledExecutableCoolingHistoryFrom parameters q I
        (sigma2 :: tau2 :: rest) head =
      (scheduledBalancedCoolingRatioLaw parameters q I sigma2 tau2
        head.2.2.2).bind fun phase =>
          match phase with
          | none => Measure.dirac none
          | some (ratio, nextPoint) =>
              scheduledExecutableCoolingHistoryFrom parameters q I
                (tau2 :: rest)
                ((fun k => if k = head.2.1 then ratio else head.1 k),
                  head.2.1 + 1, head.2.2.1 * ratio, nextPoint) := by
  have htail := scheduledExecutableCoolingHistoryLaw_measurable_and_probability
    parameters q I (tau2 :: rest) htailPositive
  let oldContinuation : Option (ℝ × AmbientSpace q.n) →
      Measure (Option (BalancedCoolingHistory q.n)) := fun phase =>
    match phase with
    | none => Measure.dirac none
    | some (ratio, nextPoint) =>
        (scheduledExecutableCoolingHistoryLaw parameters q I
          (tau2 :: rest) nextPoint).map (balancedCoolingHistoryCons ratio)
  have holdContinuation : Measurable oldContinuation := by
    have hsome : Measurable fun value : ℝ × AmbientSpace q.n =>
        (scheduledExecutableCoolingHistoryLaw parameters q I
          (tau2 :: rest) value.2).map
            (balancedCoolingHistoryCons value.1) := by
      apply measurable_measure_map_param_variable
        (htail.1.comp measurable_snd) (fun value => htail.2 value.2)
      exact measurable_balancedCoolingHistoryCons.comp <|
        (measurable_fst.comp measurable_fst).prodMk measurable_snd
    convert Measurable.optionElim
      (Measure.dirac (none : Option (BalancedCoolingHistory q.n))) hsome using 1
    funext phase
    cases phase <;> rfl
  unfold scheduledExecutableCoolingHistoryFrom
  rw [scheduledExecutableCoolingHistoryLaw]
  change ((scheduledBalancedCoolingRatioLaw parameters q I sigma2 tau2
    head.2.2.2).bind oldContinuation).map
      (balancedCoolingHistoryConcatOption head) = _
  rw [map_bind_eq_bind_map_of_measurable _ holdContinuation
    (measurable_balancedCoolingHistoryConcatOption head)]
  apply Measure.bind_congr_right
  filter_upwards with phase
  cases phase with
  | none =>
      rw [Measure.map_dirac'
        (measurable_balancedCoolingHistoryConcatOption head)]
      rfl
  | some value =>
      rcases value with ⟨ratio, nextPoint⟩
      have hcons : Measurable (balancedCoolingHistoryCons (n := q.n) ratio) :=
        (measurable_balancedCoolingHistoryCons (n := q.n)).comp
          (measurable_const.prodMk measurable_id)
      rw [Measure.map_map
        (measurable_balancedCoolingHistoryConcatOption head) hcons]
      apply Measure.map_congr
      filter_upwards with tail
      cases tail with
      | none => rfl
      | some tail =>
          simp only [Function.comp_apply, balancedCoolingHistoryCons,
            balancedCoolingHistoryConcatOption]
          exact congrArg some
            (balancedCoolingHistoryConcat_snoc_cons head tail ratio nextPoint)

noncomputable def scheduledVarianceSegment
    (q : VolumeParams) (offset steps : ℕ) : List ℝ :=
  List.ofFn fun i : Fin (steps + 1) => scheduleValue q (offset + i.1)

@[simp] theorem scheduledVarianceSegment_zero
    (q : VolumeParams) (offset : ℕ) :
    scheduledVarianceSegment q offset 0 = [scheduleValue q offset] := by
  simp [scheduledVarianceSegment]

theorem scheduledVarianceSegment_succ
    (q : VolumeParams) (offset steps : ℕ) :
    scheduledVarianceSegment q offset (steps + 1) =
      scheduleValue q offset :: scheduledVarianceSegment q (offset + 1) steps := by
  unfold scheduledVarianceSegment
  rw [List.ofFn_succ]
  congr 1
  apply List.ofFn_inj.mpr
  funext i
  congr 1
  simp only [Fin.val_succ]
  omega

theorem scheduledVarianceSegment_eq_cons_head_tail
    (q : VolumeParams) (offset steps : ℕ) :
    scheduledVarianceSegment q offset steps =
      scheduleValue q offset :: (scheduledVarianceSegment q offset steps).tail := by
  cases steps with
  | zero => simp
  | succ steps =>
      rw [scheduledVarianceSegment_succ]
      simp only [List.tail_cons]

/-- Front-recursive form of the scheduled chronological Gaussian phase law. -/
noncomputable def scheduledExecutableFrontHistoryLaw
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) :
    ℕ → ℕ → Option (BalancedCoolingHistory q.n) →
      Measure (Option (BalancedCoolingHistory q.n))
  | _, 0, history => Measure.dirac history
  | offset, steps + 1, history =>
      match history with
      | none => Measure.dirac none
      | some head =>
          (scheduledBalancedCoolingRatioLaw parameters q I
            (scheduleValue q offset) (scheduleValue q (offset + 1))
            head.2.2.2).bind fun phase =>
              match phase with
              | none => Measure.dirac none
              | some (ratio, nextPoint) =>
                  scheduledExecutableFrontHistoryLaw parameters q I
                    (offset + 1) steps
                    (some ((fun k => if k = head.2.1 then ratio else head.1 k),
                      head.2.1 + 1, head.2.2.1 * ratio, nextPoint))

@[simp] theorem scheduledExecutableFrontHistoryLaw_none
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (offset : ℕ) :
    ∀ steps,
      scheduledExecutableFrontHistoryLaw parameters q I offset steps none =
        Measure.dirac none := by
  intro steps
  cases steps <;> rfl

theorem scheduledExecutableCoolingHistoryFrom_segment_eq_front
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (offset : ℕ) :
    ∀ steps (head : BalancedCoolingHistory q.n),
      scheduledExecutableCoolingHistoryFrom parameters q I
          (scheduledVarianceSegment q offset steps) head =
        scheduledExecutableFrontHistoryLaw parameters q I offset steps
          (some head) := by
  intro steps
  induction steps generalizing offset with
  | zero =>
      intro head
      rw [scheduledVarianceSegment_zero,
        scheduledExecutableCoolingHistoryFrom_singleton]
      rfl
  | succ steps ih =>
      intro head
      rw [scheduledVarianceSegment_succ]
      rw [scheduledVarianceSegment_eq_cons_head_tail q (offset + 1) steps]
      rw [scheduledExecutableCoolingHistoryFrom_cons_cons parameters q I
        (scheduleValue q offset) (scheduleValue q (offset + 1))
        (scheduledVarianceSegment q (offset + 1) steps).tail
        (scheduleValue_pos q offset)]
      · rw [scheduledExecutableFrontHistoryLaw]
        apply Measure.bind_congr_right
        filter_upwards with phase
        cases phase with
        | none => rfl
        | some value =>
            rcases value with ⟨ratio, nextPoint⟩
            simpa only [← scheduledVarianceSegment_eq_cons_head_tail] using
              ih (offset + 1)
                ((fun k => if k = head.2.1 then ratio else head.1 k),
                  head.2.1 + 1, head.2.2.1 * ratio, nextPoint)
      · intro s hs
        rw [show scheduleValue q (offset + 1) ::
            (scheduledVarianceSegment q (offset + 1) steps).tail =
            scheduledVarianceSegment q (offset + 1) steps by
          cases steps with
          | zero => simp
          | succ steps =>
              rw [scheduledVarianceSegment_succ]
              rfl] at hs
        rw [scheduledVarianceSegment, List.mem_ofFn'] at hs
        obtain ⟨i, rfl⟩ := hs
        exact scheduleValue_pos q _

theorem measurable_iteratedKernelLaw_from_firstKernel
    {S : Type*} [MeasurableSpace S]
    (K : ℕ → S → Measure S) (hK : ∀ phase, Measurable (K phase)) :
    ∀ steps,
      Measurable fun state =>
        iteratedKernelLaw (fun phase => K (phase + 1)) (K 0 state) steps := by
  intro steps
  induction steps with
  | zero => exact hK 0
  | succ steps ih =>
      exact (Measure.measurable_bind' (hK (steps + 1))).comp ih

/-- A nonhomogeneous kernel iteration may be exposed from its first step. -/
theorem iteratedKernelLaw_succ_eq_bind_front
    {S : Type*} [MeasurableSpace S]
    (K : ℕ → S → Measure S) (hK : ∀ phase, Measurable (K phase))
    (mu : Measure S) :
    ∀ steps,
      iteratedKernelLaw K mu (steps + 1) =
        mu.bind fun state =>
          iteratedKernelLaw (fun phase => K (phase + 1)) (K 0 state) steps := by
  intro steps
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [iteratedKernelLaw_succ, ih]
      rw [Measure.bind_bind
        (measurable_iteratedKernelLaw_from_firstKernel K hK steps).aemeasurable
        (hK (steps + 1)).aemeasurable]
      rfl

theorem scheduledExecutableFrontHistoryLaw_eq_iterated
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) :
    ∀ steps offset (history : Option (BalancedCoolingHistory q.n)),
      offset + steps ≤ terminalPhaseSteps q →
      scheduledExecutableFrontHistoryLaw parameters q I offset steps history =
        iteratedKernelLaw
          (fun phase => scheduledBalancedForwardPhaseKernel parameters q I
            (offset + phase)) (Measure.dirac history) steps := by
  intro steps
  induction steps with
  | zero =>
      intro offset history _
      rfl
  | succ steps ih =>
      intro offset history hbound
      let K := fun phase => scheduledBalancedForwardPhaseKernel parameters q I
        (offset + phase)
      have hK : ∀ phase, Measurable (K phase) := fun phase =>
        (scheduledBalancedForwardPhaseKernel_measurable_and_probability
          parameters q I (offset + phase)).1
      rw [iteratedKernelLaw_succ_eq_bind_front K hK (Measure.dirac history) steps]
      rw [Measure.dirac_bind
        (measurable_iteratedKernelLaw_from_firstKernel K hK steps) history]
      let KS := fun phase => scheduledBalancedForwardPhaseKernel parameters q I
        (offset + 1 + phase)
      rw [show (fun phase => K (phase + 1)) = KS by
        funext phase
        unfold K KS
        rw [show offset + (phase + 1) = offset + 1 + phase by omega]]
      have hKS : ∀ phase, Measurable (KS phase) := fun phase =>
        (scheduledBalancedForwardPhaseKernel_measurable_and_probability
          parameters q I (offset + 1 + phase)).1
      have hKSprob : ∀ phase state, IsProbabilityMeasure (KS phase state) :=
        fun phase state =>
          (scheduledBalancedForwardPhaseKernel_measurable_and_probability
            parameters q I (offset + 1 + phase)).2 state
      have hlift := bind_iteratedKernelLaw_dirac_eq_iteratedKernelLaw_map
        KS hKS hKSprob (K 0 history) id measurable_id steps
      rw [Measure.map_id] at hlift
      rw [← hlift]
      simp only [id_eq]
      cases history with
        | none =>
            simp only [scheduledExecutableFrontHistoryLaw, K,
              scheduledBalancedForwardPhaseKernel]
            rw [Measure.dirac_bind]
            · rw [← ih (offset + 1) none (by omega)]
              exact (scheduledExecutableFrontHistoryLaw_none
                parameters q I (offset + 1) steps).symm
            · exact (iteratedKernelLaw_dirac_measurable_and_probability
                KS hKS hKSprob steps).1
        | some head =>
            have hoffset : offset < terminalPhaseSteps q := by omega
            simp only [scheduledExecutableFrontHistoryLaw]
            have hsnoc : Measurable (balancedCoolingHistorySnocTerminal head) :=
              measurable_balancedCoolingHistorySnocTerminal.comp
                (measurable_const.prodMk measurable_id)
            have hcontinuation : Measurable fun state =>
                iteratedKernelLaw KS (Measure.dirac state) steps :=
              (iteratedKernelLaw_dirac_measurable_and_probability
                KS hKS hKSprob steps).1
            simp only [K, scheduledBalancedForwardPhaseKernel, Nat.add_zero,
              hoffset, if_true]
            rw [← scheduledBalancedCoolingRatioLaw_eq_transitionLaw parameters q I
              (scheduleValue_pos q offset) (scheduleValue q (offset + 1))
              head.2.2.2]
            rw [Measure.map_bind_eq_bind_comp _ hsnoc hcontinuation]
            apply Measure.bind_congr_right
            filter_upwards with phase
            cases phase with
            | none =>
                simp only [balancedCoolingHistorySnocTerminal,
                  Function.comp_apply]
                calc
                  Measure.dirac none =
                      scheduledExecutableFrontHistoryLaw parameters q I
                        (offset + 1) steps none :=
                    (scheduledExecutableFrontHistoryLaw_none
                      parameters q I (offset + 1) steps).symm
                  _ = _ := by
                    simpa only [KS, K, Nat.add_assoc] using
                      ih (offset + 1) none (by omega)
            | some value =>
                rcases value with ⟨ratio, nextPoint⟩
                simpa only [balancedCoolingHistorySnocTerminal, Function.comp_apply,
                  KS, K, Nat.add_assoc] using
                    ih (offset + 1)
                      (some ((fun k => if k = head.2.1 then ratio else head.1 k),
                        head.2.1 + 1, head.2.2.1 * ratio, nextPoint)) (by omega)

theorem explicitScheduleVariances_eq_scheduledVarianceSegment
    (q : VolumeParams) :
    (explicitVolumeCoolingSchedule q).variances =
      scheduledVarianceSegment q 0 (terminalPhaseSteps q) := by
  unfold explicitVolumeCoolingSchedule explicitScheduleVariances
    scheduledVarianceSegment
  congr 1
  apply List.ofFn_inj.mpr
  funext i
  congr 1
  omega

theorem balancedCoolingHistoryOutput_concat_initial
    (point : AmbientSpace n)
    (tail : Option (BalancedCoolingHistory n)) :
    balancedCoolingHistoryOutput
        (balancedCoolingHistoryConcatOption
          ((fun _ => 0), 0, 1, point) tail) =
      balancedCoolingHistoryOutput tail := by
  cases tail with
  | none => rfl
  | some tail =>
      simp [balancedCoolingHistoryConcatOption,
        balancedCoolingHistoryConcat, balancedCoolingHistoryOutput]

/-- The Gaussian part of the executable program and the chronological
forward interpreter have exactly the same accumulated-product/retained-point
law.  No equality of irrelevant out-of-range sequence coordinates is needed. -/
theorem map_scheduledExecutableFigureOneCoolingHistory_output_eq_forward
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (point : AmbientSpace q.n) :
    (scheduledExecutableFigureOneCoolingHistoryLaw parameters q I point).map
        balancedCoolingHistoryOutput =
      (scheduledBalancedForwardHistoryLawFromPoint parameters q I
        (terminalPhaseSteps q) point).map balancedCoolingHistoryOutput := by
  let head : BalancedCoolingHistory q.n := ((fun _ => 0), 0, 1, point)
  have hfront := scheduledExecutableCoolingHistoryFrom_segment_eq_front
    parameters q I 0 (terminalPhaseSteps q) head
  have hiter := scheduledExecutableFrontHistoryLaw_eq_iterated
    parameters q I (terminalPhaseSteps q) 0 (some head) (by omega)
  have hfrom :
      scheduledExecutableCoolingHistoryFrom parameters q I
          (scheduledVarianceSegment q 0 (terminalPhaseSteps q)) head =
        scheduledBalancedForwardHistoryLawFromPoint parameters q I
          (terminalPhaseSteps q) point := by
    rw [hfront, hiter]
    unfold scheduledBalancedForwardHistoryLawFromPoint head
    congr 3
    funext phase
    congr 2
    omega
  rw [← hfrom]
  unfold scheduledExecutableCoolingHistoryFrom
  rw [← explicitScheduleVariances_eq_scheduledVarianceSegment q]
  unfold scheduledExecutableFigureOneCoolingHistoryLaw
  rw [Measure.map_map measurable_balancedCoolingHistoryOutput
    (measurable_balancedCoolingHistoryConcatOption head)]
  apply Measure.map_congr
  filter_upwards with tail
  exact (balancedCoolingHistoryOutput_concat_initial point tail).symm

noncomputable def scheduledExecutableTerminalHistoryKernel
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) :
    Option (BalancedCoolingHistory q.n) →
      Measure (Option (BalancedCoolingHistory q.n))
  | none => Measure.dirac none
  | some history =>
      (scheduledBalancedCoolingUniformCollectorLawWithState parameters q I
        (terminalVariance q) history.2.2.2).map
          (balancedCoolingHistorySnocTerminal history)

noncomputable def scheduledExecutableTerminalScalarKernel
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) :
    Option (ℝ × AmbientSpace q.n) → Measure ℝ
  | none => Measure.dirac 0
  | some (product, point) =>
      (scheduledBalancedCoolingUniformCollectorLawWithState parameters q I
        (terminalVariance q) point).map
          (balancedFigureOneTerminalScalar q product)

theorem scheduledExecutableTerminalHistoryKernel_measurable
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) :
    Measurable (scheduledExecutableTerminalHistoryKernel parameters q I) := by
  have hterminal :=
    scheduledBalancedCoolingUniformCollectorLawWithState_measurable_and_probability
      parameters q I (terminalVariance_pos' q)
  have hsome : Measurable fun history : BalancedCoolingHistory q.n =>
      (scheduledBalancedCoolingUniformCollectorLawWithState parameters q I
        (terminalVariance q) history.2.2.2).map
          (balancedCoolingHistorySnocTerminal history) := by
    apply measurable_measure_map_param_variable
    · exact hterminal.1.comp <|
        measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_id))
    · intro history
      exact hterminal.2 history.2.2.2
    · exact measurable_balancedCoolingHistorySnocTerminal.comp <|
        measurable_fst.prodMk measurable_snd
  convert Measurable.optionElim
    (Measure.dirac (none : Option (BalancedCoolingHistory q.n))) hsome using 1
  funext history
  cases history <;> rfl

theorem scheduledExecutableTerminalScalarKernel_measurable
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) :
    Measurable (scheduledExecutableTerminalScalarKernel parameters q I) := by
  have hterminal :=
    scheduledBalancedCoolingUniformCollectorLawWithState_measurable_and_probability
      parameters q I (terminalVariance_pos' q)
  have hsome : Measurable fun value : ℝ × AmbientSpace q.n =>
      (scheduledBalancedCoolingUniformCollectorLawWithState parameters q I
        (terminalVariance q) value.2).map
          (balancedFigureOneTerminalScalar q value.1) := by
    apply measurable_measure_map_param_variable
      (hterminal.1.comp measurable_snd) (fun value => hterminal.2 value.2)
    exact (measurable_balancedFigureOneTerminalScalar q).comp <|
      (measurable_fst.comp measurable_fst).prodMk measurable_snd
  convert Measurable.optionElim (Measure.dirac (0 : ℝ)) hsome using 1
  funext value
  cases value <;> rfl

theorem map_bind_scheduledExecutableTerminalHistoryKernel
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n)
    (mu : Measure (Option (BalancedCoolingHistory q.n))) :
    (mu.bind (scheduledExecutableTerminalHistoryKernel parameters q I)).map
        (balancedFigureOneHistoryEstimate q) =
      (mu.map balancedCoolingHistoryOutput).bind
        (scheduledExecutableTerminalScalarKernel parameters q I) := by
  have hhistory := scheduledExecutableTerminalHistoryKernel_measurable
    parameters q I
  have hscalar := scheduledExecutableTerminalScalarKernel_measurable
    parameters q I
  rw [map_bind_eq_bind_map_of_measurable _ hhistory
    (measurable_balancedFigureOneHistoryEstimate q)]
  rw [Measure.map_bind_eq_bind_comp _ measurable_balancedCoolingHistoryOutput hscalar]
  apply Measure.bind_congr_right
  filter_upwards with history
  cases history with
  | none =>
      simp [scheduledExecutableTerminalHistoryKernel,
        scheduledExecutableTerminalScalarKernel,
        balancedCoolingHistoryOutput, balancedFigureOneHistoryEstimate,
        Measure.map_dirac' (measurable_balancedFigureOneHistoryEstimate q)]
  | some history =>
      change
        ((scheduledBalancedCoolingUniformCollectorLawWithState parameters q I
          (terminalVariance q) history.2.2.2).map
            (balancedCoolingHistorySnocTerminal history)).map
              (balancedFigureOneHistoryEstimate q) =
          (scheduledBalancedCoolingUniformCollectorLawWithState parameters q I
            (terminalVariance q) history.2.2.2).map
              (balancedFigureOneTerminalScalar q history.2.2.1)
      have hsnoc : Measurable (balancedCoolingHistorySnocTerminal history) :=
        measurable_balancedCoolingHistorySnocTerminal.comp
          (measurable_const.prodMk measurable_id)
      rw [Measure.map_map (measurable_balancedFigureOneHistoryEstimate q) hsnoc]
      apply Measure.map_congr
      filter_upwards with terminal
      exact balancedFigureOneHistoryEstimate_snocTerminal q history terminal

theorem scheduledExecutableFigureOneFullHistory_map_estimate_factor
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (point : AmbientSpace q.n) :
    (scheduledExecutableFigureOneFullHistoryLaw parameters q I point).map
        (balancedFigureOneHistoryEstimate q) =
      ((scheduledExecutableFigureOneCoolingHistoryLaw parameters q I point).map
        balancedCoolingHistoryOutput).bind
          (scheduledExecutableTerminalScalarKernel parameters q I) := by
  change
    ((scheduledExecutableFigureOneCoolingHistoryLaw parameters q I point).bind
      (scheduledExecutableTerminalHistoryKernel parameters q I)).map
        (balancedFigureOneHistoryEstimate q) = _
  exact map_bind_scheduledExecutableTerminalHistoryKernel parameters q I _

theorem scheduledBalancedForwardHistoryLawFromPoint_succ_terminal
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (point : AmbientSpace q.n) :
    scheduledBalancedForwardHistoryLawFromPoint parameters q I
        (terminalPhaseSteps q + 1) point =
      (scheduledBalancedForwardHistoryLawFromPoint parameters q I
        (terminalPhaseSteps q) point).bind
          (scheduledExecutableTerminalHistoryKernel parameters q I) := by
  unfold scheduledBalancedForwardHistoryLawFromPoint
  rw [iteratedKernelLaw_succ]
  apply Measure.bind_congr_right
  filter_upwards with history
  cases history with
  | none => rfl
  | some history =>
      unfold scheduledBalancedForwardPhaseKernel
        scheduledExecutableTerminalHistoryKernel
      simp only [lt_self_iff_false, if_false]
      rw [scheduledBalancedCoolingUniformLaw_eq_transitionLaw parameters q I
        (terminalVariance_pos' q) history.2.2.2]

theorem scheduledBalancedForwardHistoryLawFromPoint_map_estimate_factor
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (point : AmbientSpace q.n) :
    (scheduledBalancedForwardHistoryLawFromPoint parameters q I
        (terminalPhaseSteps q + 1) point).map
          (balancedFigureOneHistoryEstimate q) =
      ((scheduledBalancedForwardHistoryLawFromPoint parameters q I
        (terminalPhaseSteps q) point).map balancedCoolingHistoryOutput).bind
          (scheduledExecutableTerminalScalarKernel parameters q I) := by
  rw [scheduledBalancedForwardHistoryLawFromPoint_succ_terminal]
  exact map_bind_scheduledExecutableTerminalHistoryKernel parameters q I _

/-- Exact `hpoint` required by the scheduled Lemma 7.17(c) accuracy wrapper:
the executable post-initial continuation is the chronological finite history
law, including its terminal coordinate. -/
theorem scheduledBalancedFigureOnePointContinuation_runEstimate_eq_forwardHistory_map
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (point : AmbientSpace q.n) :
    (scheduledBalancedFigureOnePointContinuation parameters q point).runEstimate
        oracle.query =
      (scheduledBalancedForwardHistoryLawFromPoint parameters q I
        (figureOneDependentPhaseCount q) point).map
          (balancedFigureOneHistoryEstimate q) := by
  rw [figureOneDependentPhaseCount]
  calc
    _ = (scheduledExecutableFigureOneFullHistoryLaw parameters q I point).map
          (balancedFigureOneHistoryEstimate q) :=
      scheduledBalancedFigureOnePointContinuation_runEstimate_eq_history_map
        parameters q I oracle point
    _ = ((scheduledExecutableFigureOneCoolingHistoryLaw parameters q I point).map
          balancedCoolingHistoryOutput).bind
            (scheduledExecutableTerminalScalarKernel parameters q I) :=
      scheduledExecutableFigureOneFullHistory_map_estimate_factor
        parameters q I point
    _ = ((scheduledBalancedForwardHistoryLawFromPoint parameters q I
          (terminalPhaseSteps q) point).map balancedCoolingHistoryOutput).bind
            (scheduledExecutableTerminalScalarKernel parameters q I) := by
      rw [map_scheduledExecutableFigureOneCoolingHistory_output_eq_forward]
    _ = (scheduledBalancedForwardHistoryLawFromPoint parameters q I
          (terminalPhaseSteps q + 1) point).map
            (balancedFigureOneHistoryEstimate q) :=
      (scheduledBalancedForwardHistoryLawFromPoint_map_estimate_factor
        parameters q I point).symm

#print axioms balancedCoolingHistoryConcat_initial
#print axioms measurable_balancedCoolingHistoryConcatOption
#print axioms balancedCoolingHistoryConcat_snoc_cons
#print axioms scheduledExecutableCoolingHistoryFrom_cons_cons
#print axioms scheduledExecutableCoolingHistoryFrom_segment_eq_front
#print axioms iteratedKernelLaw_succ_eq_bind_front
#print axioms scheduledExecutableFrontHistoryLaw_eq_iterated
#print axioms map_scheduledExecutableFigureOneCoolingHistory_output_eq_forward
#print axioms scheduledBalancedFigureOnePointContinuation_runEstimate_eq_forwardHistory_map

end ArlibCommunity.Algorithms.CV18
