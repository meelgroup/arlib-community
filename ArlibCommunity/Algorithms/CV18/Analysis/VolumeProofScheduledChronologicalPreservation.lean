/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.SequentialRecordedKernelPreservation
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledChronologicalResetReference
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledReferenceCoordinateExtension

/-!
# Joint preservation of completed chronological coordinates

A coordinatewise list of marginal identities is enough to retain moments but
not enough to retain earlier approximate-independence statements.  This file
packages all completed scalar coordinates as one finite measurable prefix.
A valid trace append preserves that prefix pointwise, hence a
history-preserving reset preserves its complete joint law.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

noncomputable section

/-- A history-preserving reset followed by a valid trace append preserves the
complete joint law of all already completed coordinates. -/
theorem map_scheduledResetPrefixCoordinates_resetAppend_eq
    (q : VolumeParams) (phase : ℕ)
    (hphase : phase < figureOneDependentPhaseCount q)
    (reset : Measure (ScheduledBalancedCoolingTrace q.n ×
      (ℝ × Option (AmbientSpace q.n))))
    (source : Measure (ScheduledBalancedCoolingTrace q.n))
    (hfst : reset.map Prod.fst = source)
    (hvalid : ∀ᵐ trace ∂source,
      ScheduledBalancedCoolingTraceValid phase trace) :
    (reset.map (scheduledResetTraceAppend (n := q.n))).map
        (scheduledResetPrefixCoordinates q phase) =
      source.map (scheduledResetPrefixCoordinates q phase) := by
  apply map_map_uncurry_update_eq_source_of_ae reset source
    (fun trace result => scheduledResetTraceAppend (trace, result))
    (scheduledResetPrefixCoordinates q phase)
    measurable_scheduledResetTraceAppend
    (measurable_scheduledResetPrefixCoordinates q phase) hfst
  have hvalidReset : ∀ᵐ state ∂reset,
      ScheduledBalancedCoolingTraceValid phase state.1 := by
    have hmapped : ∀ᵐ trace ∂reset.map Prod.fst,
        ScheduledBalancedCoolingTraceValid phase trace := by
      rw [hfst]
      exact hvalid
    exact (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_scheduledBalancedCoolingTraceValid phase)).1 hmapped
  filter_upwards [hvalidReset] with state hstate
  exact scheduledResetPrefixCoordinates_resetAppend_eq
    q phase hphase state.1 hstate state.2

/-- Any measurable scalar observable of an exactly preserved prefix retains
its `L²` membership, mean, and second moment. -/
theorem coordinate_moments_of_shared_prefix_law
    {H H' P : Type*} [MeasurableSpace H] [MeasurableSpace H']
    [MeasurableSpace P]
    (source : Measure H) (reference : Measure H')
    (oldMap : H → P) (newMap : H' → P) (F : P → ℝ)
    (hOldMap : Measurable oldMap) (hNewMap : Measurable newMap)
    (hF : Measurable F)
    (hlaw : reference.map newMap = source.map oldMap)
    (hmem : MemLp (F ∘ oldMap) 2 source) :
    MemLp (F ∘ newMap) 2 reference ∧
      (∫ state, F (newMap state) ∂reference) =
        ∫ state, F (oldMap state) ∂source ∧
      (∫ state, F (newMap state) ^ 2 ∂reference) =
        ∫ state, F (oldMap state) ^ 2 ∂source := by
  apply coordinate_moments_of_map_eq source reference
    (F ∘ oldMap) (F ∘ newMap) (hF.comp hOldMap) (hF.comp hNewMap)
  · calc
      reference.map (F ∘ newMap) =
          (reference.map newMap).map F :=
        (Measure.map_map hF hNewMap).symm
      _ = (source.map oldMap).map F := by rw [hlaw]
      _ = source.map (F ∘ oldMap) := Measure.map_map hF hOldMap
  · exact hmem

/-- Approximate independence of two measurable functions of a prefix depends
only on the prefix's joint law.  Thus all prior Lemma 7.17(c) facts transport
unchanged once the complete prefix pushforward is preserved. -/
theorem ApproxIndepFun.of_shared_prefix_law
    {H H' P S T : Type*} [MeasurableSpace H] [MeasurableSpace H']
    [MeasurableSpace P] [MeasurableSpace S] [MeasurableSpace T]
    (source : Measure H) (reference : Measure H')
    (oldMap : H → P) (newMap : H' → P)
    (F : P → S) (G : P → T)
    (hOldMap : Measurable oldMap) (hNewMap : Measurable newMap)
    (hF : Measurable F) (hG : Measurable G)
    (hlaw : reference.map newMap = source.map oldMap)
    {epsilon : ℝ}
    (hind : ApproxIndepFun epsilon (F ∘ oldMap) (G ∘ oldMap) source) :
    ApproxIndepFun epsilon (F ∘ newMap) (G ∘ newMap) reference := by
  apply ApproxIndepFun.of_map_pair_eq
    (hF.comp hOldMap) (hG.comp hOldMap)
    (hF.comp hNewMap) (hG.comp hNewMap) _ hind
  let pair : P → S × T := fun values => (F values, G values)
  have hpair : Measurable pair := hF.prodMk hG
  calc
    source.map (fun state => (F (oldMap state), G (oldMap state))) =
        (source.map oldMap).map pair :=
      (Measure.map_map hpair hOldMap).symm
    _ = (reference.map newMap).map pair := by rw [hlaw]
    _ = reference.map
        (fun state => (F (newMap state), G (newMap state))) :=
      Measure.map_map hpair hNewMap

/-! ## Concrete factorization of the Lemma 7.17(c) observables -/

/-- Total one-based coordinate reader on a finite reset prefix.  Only the
used interval matters; zero is a harmless value outside it. -/
noncomputable def scheduledResetPrefixPhaseVariable
    (phase j : ℕ) (values : Fin phase → ℝ) : ℝ :=
  if h : 1 ≤ j ∧ j ≤ phase then
    values ⟨j - 1, by omega⟩
  else 0

theorem measurable_scheduledResetPrefixPhaseVariable
    (phase j : ℕ) :
    Measurable (scheduledResetPrefixPhaseVariable phase j) := by
  unfold scheduledResetPrefixPhaseVariable
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const

theorem scheduledResetPrefixPhaseVariable_apply
    (q : VolumeParams) (phase j : ℕ)
    (hj1 : 1 ≤ j) (hjphase : j ≤ phase)
    (trace : ScheduledBalancedCoolingTrace q.n) :
    scheduledResetPrefixPhaseVariable phase j
        (scheduledResetPrefixCoordinates q phase trace) =
      scheduledBalancedTracePhaseVariable q j trace := by
  simp only [scheduledResetPrefixPhaseVariable, hj1, hjphase, and_self,
    dite_true, scheduledResetPrefixCoordinates]
  congr 2
  omega

/-- The first-truncated phase coordinate, expressed solely on the finite
score prefix. -/
noncomputable def scheduledResetPrefixTruncatedPhase
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    ℕ → (Fin phase → ℝ) → ℝ :=
  dependentTruncatedPhase (figureOneDependentAlpha q)
    (scheduledFigureOneTraceRawMean q I)
    (scheduledResetPrefixPhaseVariable phase)

theorem measurable_scheduledResetPrefixTruncatedPhase
    (q : VolumeParams) (I : VolumeInput q.n) (phase j : ℕ) :
    Measurable (scheduledResetPrefixTruncatedPhase q I phase j) :=
  (measurable_scheduledResetPrefixPhaseVariable phase j).min measurable_const

/-- The recursively truncated accumulated product, expressed solely on the
finite score prefix. -/
noncomputable def scheduledResetPrefixTruncatedProduct
    (q : VolumeParams) (I : VolumeInput q.n) (phase i : ℕ) :
    (Fin phase → ℝ) → ℝ :=
  dependentTruncatedProduct (figureOneDependentAlpha q)
    (scheduledFigureOneTraceTruncatedMean q I)
    (scheduledResetPrefixTruncatedPhase q I phase) i

theorem measurable_scheduledResetPrefixTruncatedProduct
    (q : VolumeParams) (I : VolumeInput q.n) (phase i : ℕ) :
    Measurable (scheduledResetPrefixTruncatedProduct q I phase i) :=
  measurable_dependentTruncatedProduct
    (figureOneDependentAlpha q)
    (scheduledFigureOneTraceTruncatedMean q I)
    (scheduledResetPrefixTruncatedPhase q I phase)
    (measurable_scheduledResetPrefixTruncatedPhase q I phase) i

/-- For a completed coordinate, the trace-side first truncation factors
through the finite reset prefix. -/
theorem scheduledFigureOneTraceTruncatedPhase_factor_prefix
    (q : VolumeParams) (I : VolumeInput q.n) (phase j : ℕ)
    (hj1 : 1 ≤ j) (hjphase : j ≤ phase) :
    scheduledFigureOneTraceTruncatedPhase q I j =
      scheduledResetPrefixTruncatedPhase q I phase j ∘
        scheduledResetPrefixCoordinates q phase := by
  funext trace
  unfold scheduledFigureOneTraceTruncatedPhase
    scheduledResetPrefixTruncatedPhase dependentTruncatedPhase
  simp only [Function.comp_apply]
  rw [scheduledResetPrefixPhaseVariable_apply q phase j hj1 hjphase trace]

/-- The complete CV18 recursively truncated product through coordinate `i`
factors through any reset prefix containing those `i` coordinates. -/
theorem dependentTruncatedProduct_scheduledTrace_factor_prefix
    (q : VolumeParams) (I : VolumeInput q.n) (phase i : ℕ)
    (hi : i ≤ phase) :
    dependentTruncatedProduct (figureOneDependentAlpha q)
        (scheduledFigureOneTraceTruncatedMean q I)
        (scheduledFigureOneTraceTruncatedPhase q I) i =
      scheduledResetPrefixTruncatedProduct q I phase i ∘
        scheduledResetPrefixCoordinates q phase := by
  induction i with
  | zero => rfl
  | succ i ih =>
      funext trace
      change dependentTruncatedProduct (figureOneDependentAlpha q)
          (scheduledFigureOneTraceTruncatedMean q I)
          (scheduledFigureOneTraceTruncatedPhase q I) (i + 1) trace =
        dependentTruncatedProduct (figureOneDependentAlpha q)
          (scheduledFigureOneTraceTruncatedMean q I)
          (scheduledResetPrefixTruncatedPhase q I phase) (i + 1)
            (scheduledResetPrefixCoordinates q phase trace)
      rw [dependentTruncatedProduct_succ,
        dependentTruncatedProduct_succ]
      have hi' : i ≤ phase := by omega
      have hcoordinate : scheduledFigureOneTraceTruncatedPhase q I (i + 1) =
          scheduledResetPrefixTruncatedPhase q I phase (i + 1) ∘
            scheduledResetPrefixCoordinates q phase :=
        scheduledFigureOneTraceTruncatedPhase_factor_prefix q I phase
          (i + 1) (by omega) hi
      have ih' := congrFun (ih hi') trace
      rw [ih', congrFun hcoordinate trace]
      rfl

/-- Concrete recurrence consumer: exact preservation of the completed score
prefix transports every earlier trace-side Lemma 7.17(c) fact unchanged. -/
theorem ApproxIndepFun.scheduledTrace_of_resetPrefix_map_eq
    (q : VolumeParams) (I : VolumeInput q.n) (phase i : ℕ)
    (hi : i < phase)
    (source reference : Measure (ScheduledBalancedCoolingTrace q.n))
    (hlaw : reference.map (scheduledResetPrefixCoordinates q phase) =
      source.map (scheduledResetPrefixCoordinates q phase))
    {epsilon : ℝ}
    (hind : ApproxIndepFun epsilon
      (dependentTruncatedProduct (figureOneDependentAlpha q)
        (scheduledFigureOneTraceTruncatedMean q I)
        (scheduledFigureOneTraceTruncatedPhase q I) i)
      (scheduledFigureOneTraceTruncatedPhase q I (i + 1)) source) :
    ApproxIndepFun epsilon
      (dependentTruncatedProduct (figureOneDependentAlpha q)
        (scheduledFigureOneTraceTruncatedMean q I)
        (scheduledFigureOneTraceTruncatedPhase q I) i)
      (scheduledFigureOneTraceTruncatedPhase q I (i + 1)) reference := by
  rw [dependentTruncatedProduct_scheduledTrace_factor_prefix q I phase i hi.le,
    scheduledFigureOneTraceTruncatedPhase_factor_prefix q I phase (i + 1)
      (by omega) (by omega)] at hind ⊢
  exact ApproxIndepFun.of_shared_prefix_law source reference
    (scheduledResetPrefixCoordinates q phase)
    (scheduledResetPrefixCoordinates q phase)
    (scheduledResetPrefixTruncatedProduct q I phase i)
    (scheduledResetPrefixTruncatedPhase q I phase (i + 1))
    (measurable_scheduledResetPrefixCoordinates q phase)
    (measurable_scheduledResetPrefixCoordinates q phase)
    (measurable_scheduledResetPrefixTruncatedProduct q I phase i)
    (measurable_scheduledResetPrefixTruncatedPhase q I phase (i + 1))
    hlaw hind

/-! ## Final-capstone chronological truncation -/

/-- Prefix-side version of the truncation used by the final reset-reference
capstone.  Its cap is the ideal chronological raw mean, not the executable
trace mean. -/
noncomputable def scheduledResetPrefixChronologicalTruncatedPhase
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    ℕ → (Fin phase → ℝ) → ℝ :=
  dependentTruncatedPhase (figureOneDependentAlpha q)
    (figureOneChronologicalRawMean q I)
    (scheduledResetPrefixPhaseVariable phase)

theorem measurable_scheduledResetPrefixChronologicalTruncatedPhase
    (q : VolumeParams) (I : VolumeInput q.n) (phase j : ℕ) :
    Measurable
      (scheduledResetPrefixChronologicalTruncatedPhase q I phase j) :=
  (measurable_scheduledResetPrefixPhaseVariable phase j).min measurable_const

/-- Prefix-side recursively truncated product with an arbitrary deterministic
mean function.  In the recurrence this is instantiated with the truncated
means under the evolving reference law. -/
noncomputable def scheduledResetPrefixChronologicalTruncatedProduct
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (mean : ℕ → ℝ) (i : ℕ) : (Fin phase → ℝ) → ℝ :=
  dependentTruncatedProduct (figureOneDependentAlpha q) mean
    (scheduledResetPrefixChronologicalTruncatedPhase q I phase) i

theorem measurable_scheduledResetPrefixChronologicalTruncatedProduct
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (mean : ℕ → ℝ) (i : ℕ) :
    Measurable
      (scheduledResetPrefixChronologicalTruncatedProduct q I phase mean i) :=
  measurable_dependentTruncatedProduct (figureOneDependentAlpha q) mean
    (scheduledResetPrefixChronologicalTruncatedPhase q I phase)
    (measurable_scheduledResetPrefixChronologicalTruncatedPhase q I phase) i

/-- On the used interval, the final capstone's chronological truncated
coordinate factors through the finite score prefix. -/
theorem figureOneChronologicalTruncatedPhase_extension_factor_prefix
    (q : VolumeParams) (I : VolumeInput q.n) (phase j : ℕ)
    (hphase : phase ≤ figureOneDependentPhaseCount q)
    (hj1 : 1 ≤ j) (hjphase : j ≤ phase) :
    figureOneChronologicalTruncatedPhase q I
        (figureOneScheduledReferenceCoordinateExtension q I) j =
      scheduledResetPrefixChronologicalTruncatedPhase q I phase j ∘
        scheduledResetPrefixCoordinates q phase := by
  funext trace
  unfold figureOneChronologicalTruncatedPhase
    scheduledResetPrefixChronologicalTruncatedPhase dependentTruncatedPhase
  simp only [Function.comp_apply]
  rw [figureOneScheduledReferenceCoordinateExtension_apply_of_used q I
      hj1 (hjphase.trans hphase),
    scheduledResetPrefixPhaseVariable_apply q phase j hj1 hjphase trace]

/-- The truncated mean of any already completed coordinate is unchanged by
an exact reset-prefix law identity. -/
theorem figureOneChronologicalTruncatedMean_extension_eq_of_prefix_map_eq
    (q : VolumeParams) (I : VolumeInput q.n) (phase j : ℕ)
    (hphase : phase ≤ figureOneDependentPhaseCount q)
    (hj1 : 1 ≤ j) (hjphase : j ≤ phase)
    (source reference : Measure (ScheduledBalancedCoolingTrace q.n))
    (hlaw : reference.map (scheduledResetPrefixCoordinates q phase) =
      source.map (scheduledResetPrefixCoordinates q phase)) :
    figureOneChronologicalTruncatedMean q I reference
        (figureOneScheduledReferenceCoordinateExtension q I) j =
      figureOneChronologicalTruncatedMean q I source
        (figureOneScheduledReferenceCoordinateExtension q I) j := by
  let F := scheduledResetPrefixChronologicalTruncatedPhase q I phase j
  have hF : Measurable F :=
    measurable_scheduledResetPrefixChronologicalTruncatedPhase q I phase j
  have hprefix := measurable_scheduledResetPrefixCoordinates q phase
  have hfactor :=
    figureOneChronologicalTruncatedPhase_extension_factor_prefix
      q I phase j hphase hj1 hjphase
  unfold figureOneChronologicalTruncatedMean
  rw [hfactor]
  calc
    (∫ trace, (F ∘ scheduledResetPrefixCoordinates q phase) trace
        ∂reference) =
        ∫ values, F values
          ∂reference.map (scheduledResetPrefixCoordinates q phase) :=
      (integral_map hprefix.aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ values, F values
          ∂source.map (scheduledResetPrefixCoordinates q phase) := by rw [hlaw]
    _ = (∫ trace, (F ∘ scheduledResetPrefixCoordinates q phase) trace
        ∂source) :=
      integral_map hprefix.aemeasurable hF.aestronglyMeasurable

/-- A recursively truncated product only inspects deterministic means at the
coordinates it has already accumulated. -/
theorem dependentTruncatedProduct_congr_mean_prefix
    {Omega : Type*} [MeasurableSpace Omega]
    (alpha : ℝ) (mean mean' : ℕ → ℝ) (V : ℕ → Omega → ℝ)
    (i : ℕ)
    (hmean : ∀ j, 1 ≤ j → j ≤ i → mean j = mean' j) :
    dependentTruncatedProduct alpha mean V i =
      dependentTruncatedProduct alpha mean' V i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      funext omega
      rw [dependentTruncatedProduct_succ,
        dependentTruncatedProduct_succ]
      have ihMean : ∀ j, 1 ≤ j → j ≤ i → mean j = mean' j := by
        intro j hj1 hji
        exact hmean j hj1 (hji.trans (Nat.le_succ i))
      rw [congrFun (ih ihMean) omega]
      congr 2
      unfold dependentPhaseMeanProduct
      apply Finset.prod_congr rfl
      intro k hk
      exact hmean (k + 1) (by omega) (by
        have := Finset.mem_range.mp hk
        omega)

/-- The final capstone's recursively truncated statistic factors through the
finite prefix for any supplied deterministic truncated-mean function. -/
theorem dependentTruncatedProduct_chronological_extension_factor_prefix
    (q : VolumeParams) (I : VolumeInput q.n) (phase i : ℕ)
    (hphase : phase ≤ figureOneDependentPhaseCount q)
    (hi : i ≤ phase) (mean : ℕ → ℝ) :
    dependentTruncatedProduct (figureOneDependentAlpha q) mean
        (figureOneChronologicalTruncatedPhase q I
          (figureOneScheduledReferenceCoordinateExtension q I)) i =
      scheduledResetPrefixChronologicalTruncatedProduct q I phase mean i ∘
        scheduledResetPrefixCoordinates q phase := by
  induction i with
  | zero => rfl
  | succ i ih =>
      funext trace
      change dependentTruncatedProduct (figureOneDependentAlpha q) mean
          (figureOneChronologicalTruncatedPhase q I
            (figureOneScheduledReferenceCoordinateExtension q I))
            (i + 1) trace =
        dependentTruncatedProduct (figureOneDependentAlpha q) mean
          (scheduledResetPrefixChronologicalTruncatedPhase q I phase)
            (i + 1) (scheduledResetPrefixCoordinates q phase trace)
      rw [dependentTruncatedProduct_succ, dependentTruncatedProduct_succ]
      have hi' : i ≤ phase := by omega
      have hcoordinate :=
        figureOneChronologicalTruncatedPhase_extension_factor_prefix
          q I phase (i + 1) hphase (by omega) hi
      rw [congrFun (ih hi') trace, congrFun hcoordinate trace]
      rfl

/-- Exact preservation of the completed prefix transports every earlier
final-capstone Lemma 7.17(c) fact, including the change from source-law to
reference-law truncated means. -/
theorem ApproxIndepFun.chronological_extension_of_resetPrefix_map_eq
    (q : VolumeParams) (I : VolumeInput q.n) (phase i : ℕ)
    (hphase : phase ≤ figureOneDependentPhaseCount q) (hi : i < phase)
    (source reference : Measure (ScheduledBalancedCoolingTrace q.n))
    (hlaw : reference.map (scheduledResetPrefixCoordinates q phase) =
      source.map (scheduledResetPrefixCoordinates q phase))
    {epsilon : ℝ}
    (hind : ApproxIndepFun epsilon
      (dependentTruncatedProduct (figureOneDependentAlpha q)
        (figureOneChronologicalTruncatedMean q I source
          (figureOneScheduledReferenceCoordinateExtension q I))
        (figureOneChronologicalTruncatedPhase q I
          (figureOneScheduledReferenceCoordinateExtension q I)) i)
      (figureOneChronologicalTruncatedPhase q I
        (figureOneScheduledReferenceCoordinateExtension q I) (i + 1))
      source) :
    ApproxIndepFun epsilon
      (dependentTruncatedProduct (figureOneDependentAlpha q)
        (figureOneChronologicalTruncatedMean q I reference
          (figureOneScheduledReferenceCoordinateExtension q I))
        (figureOneChronologicalTruncatedPhase q I
          (figureOneScheduledReferenceCoordinateExtension q I)) i)
      (figureOneChronologicalTruncatedPhase q I
        (figureOneScheduledReferenceCoordinateExtension q I) (i + 1))
      reference := by
  let meanSource := figureOneChronologicalTruncatedMean q I source
    (figureOneScheduledReferenceCoordinateExtension q I)
  let meanReference := figureOneChronologicalTruncatedMean q I reference
    (figureOneScheduledReferenceCoordinateExtension q I)
  have hmean : ∀ j, 1 ≤ j → j ≤ i → meanSource j = meanReference j := by
    intro j hj1 hji
    exact (figureOneChronologicalTruncatedMean_extension_eq_of_prefix_map_eq
      q I phase j hphase hj1 (hji.trans hi.le) source reference hlaw).symm
  have hproductMean :
      dependentTruncatedProduct (figureOneDependentAlpha q) meanSource
          (figureOneChronologicalTruncatedPhase q I
            (figureOneScheduledReferenceCoordinateExtension q I)) i =
        dependentTruncatedProduct (figureOneDependentAlpha q) meanReference
          (figureOneChronologicalTruncatedPhase q I
            (figureOneScheduledReferenceCoordinateExtension q I)) i :=
    dependentTruncatedProduct_congr_mean_prefix _ _ _ _ i hmean
  have hsourceFactor :=
    dependentTruncatedProduct_chronological_extension_factor_prefix
      q I phase i hphase hi.le meanSource
  have hreferenceFactor :=
    dependentTruncatedProduct_chronological_extension_factor_prefix
      q I phase i hphase hi.le meanReference
  have hcoordinateFactor :=
    figureOneChronologicalTruncatedPhase_extension_factor_prefix
      q I phase (i + 1) hphase (by omega) (by omega)
  rw [hsourceFactor, hcoordinateFactor] at hind
  have htransport := ApproxIndepFun.of_shared_prefix_law source reference
    (scheduledResetPrefixCoordinates q phase)
    (scheduledResetPrefixCoordinates q phase)
    (scheduledResetPrefixChronologicalTruncatedProduct
      q I phase meanSource i)
    (scheduledResetPrefixChronologicalTruncatedPhase q I phase (i + 1))
    (measurable_scheduledResetPrefixCoordinates q phase)
    (measurable_scheduledResetPrefixCoordinates q phase)
    (measurable_scheduledResetPrefixChronologicalTruncatedProduct
      q I phase meanSource i)
    (measurable_scheduledResetPrefixChronologicalTruncatedPhase
      q I phase (i + 1)) hlaw hind
  rw [← hsourceFactor, hproductMean, ← hcoordinateFactor] at htransport
  simpa only [meanReference] using htransport

/-- Local creation adapter for the chronological recurrence.  A reset step
typically proves independence of the accumulated old product and the *raw*
newly recorded score.  Exact preservation of the old prefix changes the
product's deterministic truncated-mean constants from the source law to the
new reference law, while measurable postprocessing truncates the raw score
exactly as required by the final capstone. -/
theorem ApproxIndepFun.chronological_extension_created_of_resetPrefix_map_eq
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < figureOneDependentPhaseCount q)
    (source reference : Measure (ScheduledBalancedCoolingTrace q.n))
    (hlaw : reference.map (scheduledResetPrefixCoordinates q phase) =
      source.map (scheduledResetPrefixCoordinates q phase))
    {epsilon : ℝ}
    (hind : ApproxIndepFun epsilon
      (dependentTruncatedProduct (figureOneDependentAlpha q)
        (figureOneChronologicalTruncatedMean q I source
          (figureOneScheduledReferenceCoordinateExtension q I))
        (figureOneChronologicalTruncatedPhase q I
          (figureOneScheduledReferenceCoordinateExtension q I)) phase)
      (scheduledBalancedTracePhaseVariable q (phase + 1)) reference) :
    ApproxIndepFun epsilon
      (dependentTruncatedProduct (figureOneDependentAlpha q)
        (figureOneChronologicalTruncatedMean q I reference
          (figureOneScheduledReferenceCoordinateExtension q I))
        (figureOneChronologicalTruncatedPhase q I
          (figureOneScheduledReferenceCoordinateExtension q I)) phase)
      (figureOneChronologicalTruncatedPhase q I
        (figureOneScheduledReferenceCoordinateExtension q I) (phase + 1))
      reference := by
  let W := figureOneScheduledReferenceCoordinateExtension q I
  let meanSource := figureOneChronologicalTruncatedMean q I source W
  let meanReference := figureOneChronologicalTruncatedMean q I reference W
  let V := figureOneChronologicalTruncatedPhase q I W
  have hmean : ∀ j, 1 ≤ j → j ≤ phase →
      meanSource j = meanReference j := by
    intro j hj1 hjphase
    exact (figureOneChronologicalTruncatedMean_extension_eq_of_prefix_map_eq
      q I phase j hphase.le hj1 hjphase source reference hlaw).symm
  have hproductMean :
      dependentTruncatedProduct (figureOneDependentAlpha q) meanSource V
          phase =
        dependentTruncatedProduct (figureOneDependentAlpha q) meanReference V
          phase :=
    dependentTruncatedProduct_congr_mean_prefix _ _ _ _ phase hmean
  let truncateNew : ℝ → ℝ := fun value =>
    min value
      (figureOneDependentAlpha q *
        figureOneChronologicalRawMean q I (phase + 1))
  have htruncateNew : Measurable truncateNew :=
    measurable_id.min measurable_const
  have hpost := hind.comp measurable_id htruncateNew
  have hWused : W (phase + 1) =
      scheduledBalancedTracePhaseVariable q (phase + 1) := by
    exact figureOneScheduledReferenceCoordinateExtension_eq_of_used
      q I (by omega) hphase
  have hVnew : V (phase + 1) =
      truncateNew ∘ scheduledBalancedTracePhaseVariable q (phase + 1) := by
    funext trace
    simp only [V, W, figureOneChronologicalTruncatedPhase,
      dependentTruncatedPhase, hWused, truncateNew, Function.comp_apply]
  rw [hproductMean] at hpost
  simpa only [meanSource, meanReference, V, W, Function.id_comp, hVnew]
    using hpost

#print axioms map_scheduledResetPrefixCoordinates_resetAppend_eq
#print axioms coordinate_moments_of_shared_prefix_law
#print axioms ApproxIndepFun.of_shared_prefix_law
#print axioms scheduledFigureOneTraceTruncatedPhase_factor_prefix
#print axioms dependentTruncatedProduct_scheduledTrace_factor_prefix
#print axioms ApproxIndepFun.scheduledTrace_of_resetPrefix_map_eq
#print axioms figureOneChronologicalTruncatedPhase_extension_factor_prefix
#print axioms
  figureOneChronologicalTruncatedMean_extension_eq_of_prefix_map_eq
#print axioms dependentTruncatedProduct_congr_mean_prefix
#print axioms
  dependentTruncatedProduct_chronological_extension_factor_prefix
#print axioms
  ApproxIndepFun.chronological_extension_of_resetPrefix_map_eq
#print axioms
  ApproxIndepFun.chronological_extension_created_of_resetPrefix_map_eq

end

end ArlibCommunity.Algorithms.CV18
