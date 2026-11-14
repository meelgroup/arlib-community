/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Foundations.Convex.Basic.Polytope
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Analysis.HitAndRun

section
/-!
# Finite-facet endpoints for a hit-and-run chord

For a finite polytope `body A b`, the line constraint in direction `theta` is

`inner (A i) x + t * inner (A i) theta <= b i`.

Negative directional coefficients provide lower endpoints and positive coefficients
provide upper endpoints.  We encode absent lower/upper constraints by `⊥`/`⊤` in
`EReal`, take the finite supremum/infimum, and then use `EReal.toReal`.  On a bounded
polytope and a nonzero direction both kinds of constraints exist, so the endpoints are
finite and the chord is exactly their closed interval.
-/

open ArlibCommunity.Foundations.Convex ArlibCommunity.Foundations.MarkovChainTheory

open ArlibCommunity.Foundations.Convex ArlibCommunity.Foundations.MarkovChainTheory

namespace ArlibCommunity.Foundations.MarkovChainTheory.PolytopeChord

open MeasureTheory Set Metric
open scoped InnerProductSpace ENNReal Classical

variable {n : Nat} {ι : Type*} [Fintype ι]

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- Directional coefficient of facet `i`. -/
noncomputable def coeff (A : ι → State n) (theta : State n) (i : ι) : Real :=
  ⟪A i, theta⟫_Real

/-- Available slack in facet `i` at `x`. -/
noncomputable def slack (A : ι → State n) (b : ι → Real) (x : State n) (i : ι) : Real :=
  b i - ⟪A i, x⟫_Real

/-- The line parameter where facet `i` is met. -/
noncomputable def ratio (A : ι → State n) (b : ι → Real) (x theta : State n) (i : ι) : Real :=
  slack A b x i / coeff A theta i

/-- A negative coefficient contributes a finite lower endpoint; every other facet
contributes `⊥`. -/
noncomputable def lowerCandidate (A : ι → State n) (b : ι → Real)
    (x theta : State n) (i : ι) : EReal :=
  if coeff A theta i < 0 then (ratio A b x theta i : EReal) else ⊥

/-- A positive coefficient contributes a finite upper endpoint; every other facet
contributes `⊤`. -/
noncomputable def upperCandidate (A : ι → State n) (b : ι → Real)
    (x theta : State n) (i : ι) : EReal :=
  if 0 < coeff A theta i then (ratio A b x theta i : EReal) else ⊤

/-- Extended-real lower endpoint. -/
noncomputable def lowerE (A : ι → State n) (b : ι → Real) (x theta : State n) : EReal :=
  ⨆ i, lowerCandidate A b x theta i

/-- Extended-real upper endpoint. -/
noncomputable def upperE (A : ι → State n) (b : ι → Real) (x theta : State n) : EReal :=
  ⨅ i, upperCandidate A b x theta i

/-- Real lower endpoint (finite under the hypotheses used below). -/
noncomputable def lower (A : ι → State n) (b : ι → Real) (x theta : State n) : Real :=
  (lowerE A b x theta).toReal

/-- Real upper endpoint (finite under the hypotheses used below). -/
noncomputable def upper (A : ι → State n) (b : ι → Real) (x theta : State n) : Real :=
  (upperE A b x theta).toReal

/-! ## Measurability -/

theorem measurable_coeff (A : ι → State n) (i : ι) :
    Measurable (fun theta => coeff A theta i) := by
  exact (continuous_const.inner continuous_id).measurable

theorem measurable_slack (A : ι → State n) (b : ι → Real) (i : ι) :
    Measurable (fun x => slack A b x i) := by
  exact measurable_const.sub (continuous_const.inner continuous_id).measurable

theorem measurable_ratio (A : ι → State n) (b : ι → Real) (i : ι) :
    Measurable (fun p : State n × State n => ratio A b p.1 p.2 i) := by
  exact ((measurable_slack A b i).comp measurable_fst).div
    ((measurable_coeff A i).comp measurable_snd)

theorem measurable_lowerCandidate (A : ι → State n) (b : ι → Real) (i : ι) :
    Measurable (fun p : State n × State n => lowerCandidate A b p.1 p.2 i) := by
  unfold lowerCandidate
  apply Measurable.ite
  · exact measurableSet_lt ((measurable_coeff A i).comp measurable_snd) measurable_const
  · exact (measurable_ratio A b i).coe_real_ereal
  · exact measurable_const

theorem measurable_upperCandidate (A : ι → State n) (b : ι → Real) (i : ι) :
    Measurable (fun p : State n × State n => upperCandidate A b p.1 p.2 i) := by
  unfold upperCandidate
  apply Measurable.ite
  · exact measurableSet_lt measurable_const ((measurable_coeff A i).comp measurable_snd)
  · exact (measurable_ratio A b i).coe_real_ereal
  · exact measurable_const

theorem measurable_lowerE (A : ι → State n) (b : ι → Real) :
    Measurable (fun p : State n × State n => lowerE A b p.1 p.2) := by
  unfold lowerE
  exact Measurable.iSup (fun i => measurable_lowerCandidate A b i)

theorem measurable_upperE (A : ι → State n) (b : ι → Real) :
    Measurable (fun p : State n × State n => upperE A b p.1 p.2) := by
  unfold upperE
  exact Measurable.iInf (fun i => measurable_upperCandidate A b i)

theorem measurable_lower (A : ι → State n) (b : ι → Real) :
    Measurable (fun p : State n × State n => lower A b p.1 p.2) := by
  exact (measurable_lowerE A b).ereal_toReal

theorem measurable_upper (A : ι → State n) (b : ι → Real) :
    Measurable (fun p : State n × State n => upper A b p.1 p.2) := by
  exact (measurable_upperE A b).ereal_toReal

/-! ## Finite endpoint order characterizations -/

theorem lowerE_le_coe_iff (A : ι → State n) (b : ι → Real)
    (x theta : State n) (t : Real) :
    lowerE A b x theta ≤ (t : EReal) ↔
      ∀ i, coeff A theta i < 0 → ratio A b x theta i ≤ t := by
  simp only [lowerE, iSup_le_iff, lowerCandidate]
  constructor
  · intro h i hi
    have := h i
    rw [if_pos hi] at this
    exact EReal.coe_le_coe_iff.mp this
  · intro h i
    by_cases hi : coeff A theta i < 0
    · rw [if_pos hi]
      exact EReal.coe_le_coe_iff.mpr (h i hi)
    · rw [if_neg hi]
      exact bot_le

theorem coe_le_upperE_iff (A : ι → State n) (b : ι → Real)
    (x theta : State n) (t : Real) :
    (t : EReal) ≤ upperE A b x theta ↔
      ∀ i, 0 < coeff A theta i → t ≤ ratio A b x theta i := by
  simp only [upperE, le_iInf_iff, upperCandidate]
  constructor
  · intro h i hi
    have := h i
    rw [if_pos hi] at this
    exact EReal.coe_le_coe_iff.mp this
  · intro h i
    by_cases hi : 0 < coeff A theta i
    · rw [if_pos hi]
      exact EReal.coe_le_coe_iff.mpr (h i hi)
    · rw [if_neg hi]
      exact le_top

theorem lowerE_le_zero_of_mem
    {A : ι → State n} {b : ι → Real} {x theta : State n}
    (hx : x ∈ ArlibCommunity.Foundations.Convex.Polytope.body A b) :
    lowerE A b x theta ≤ (0 : EReal) := by
  change lowerE A b x theta ≤ ((0 : Real) : EReal)
  rw [lowerE_le_coe_iff]
  intro i hi
  have hs : 0 ≤ slack A b x i := sub_nonneg.mpr (hx i)
  exact div_nonpos_of_nonneg_of_nonpos hs hi.le

theorem zero_le_upperE_of_mem
    {A : ι → State n} {b : ι → Real} {x theta : State n}
    (hx : x ∈ ArlibCommunity.Foundations.Convex.Polytope.body A b) :
    (0 : EReal) ≤ upperE A b x theta := by
  change ((0 : Real) : EReal) ≤ upperE A b x theta
  rw [coe_le_upperE_iff]
  intro i hi
  have hs : 0 ≤ slack A b x i := sub_nonneg.mpr (hx i)
  exact div_nonneg hs hi.le

theorem lowerE_ne_bot_of_exists_neg
    {A : ι → State n} {b : ι → Real} {x theta : State n}
    (hneg : ∃ i, coeff A theta i < 0) : lowerE A b x theta ≠ ⊥ := by
  obtain ⟨i, hi⟩ := hneg
  intro hbot
  have hle : (ratio A b x theta i : EReal) ≤ lowerE A b x theta := by
    exact le_iSup_of_le i (by simp [lowerCandidate, hi])
  rw [hbot] at hle
  exact EReal.coe_ne_bot _ (le_bot_iff.mp hle)

theorem upperE_ne_top_of_exists_pos
    {A : ι → State n} {b : ι → Real} {x theta : State n}
    (hpos : ∃ i, 0 < coeff A theta i) : upperE A b x theta ≠ ⊤ := by
  obtain ⟨i, hi⟩ := hpos
  intro htop
  have hle : upperE A b x theta ≤ (ratio A b x theta i : EReal) := by
    exact iInf_le_of_le i (by simp [upperCandidate, hi])
  rw [htop] at hle
  exact EReal.coe_ne_top _ (top_le_iff.mp hle)

theorem lowerE_ne_top_of_mem
    {A : ι → State n} {b : ι → Real} {x theta : State n}
    (hx : x ∈ ArlibCommunity.Foundations.Convex.Polytope.body A b) : lowerE A b x theta ≠ ⊤ :=
  ne_top_of_le_ne_top (EReal.coe_ne_top (0 : Real)) (lowerE_le_zero_of_mem hx)

theorem upperE_ne_bot_of_mem
    {A : ι → State n} {b : ι → Real} {x theta : State n}
    (hx : x ∈ ArlibCommunity.Foundations.Convex.Polytope.body A b) : upperE A b x theta ≠ ⊥ :=
  ne_bot_of_le_ne_bot (EReal.coe_ne_bot (0 : Real)) (zero_le_upperE_of_mem hx)

theorem lower_le_iff
    {A : ι → State n} {b : ι → Real} {x theta : State n}
    (hx : x ∈ ArlibCommunity.Foundations.Convex.Polytope.body A b) (hneg : ∃ i, coeff A theta i < 0)
    (t : Real) :
    lower A b x theta ≤ t ↔
      ∀ i, coeff A theta i < 0 → ratio A b x theta i ≤ t := by
  rw [← lowerE_le_coe_iff A b x theta t]
  unfold lower
  rw [← EReal.coe_le_coe_iff, EReal.coe_toReal
    (lowerE_ne_top_of_mem hx) (lowerE_ne_bot_of_exists_neg hneg)]

theorem le_upper_iff
    {A : ι → State n} {b : ι → Real} {x theta : State n}
    (hx : x ∈ ArlibCommunity.Foundations.Convex.Polytope.body A b) (hpos : ∃ i, 0 < coeff A theta i)
    (t : Real) :
    t ≤ upper A b x theta ↔
      ∀ i, 0 < coeff A theta i → t ≤ ratio A b x theta i := by
  rw [← coe_le_upperE_iff A b x theta t]
  unfold upper
  rw [← EReal.coe_le_coe_iff, EReal.coe_toReal
    (upperE_ne_top_of_exists_pos hpos) (upperE_ne_bot_of_mem hx)]

/-! ## Bounded polytopes have both endpoint types -/

theorem exists_pos_coeff_of_isBounded
    {A : ι → State n} {b : ι → Real} {theta : State n}
    (hK : Bornology.IsBounded (ArlibCommunity.Foundations.Convex.Polytope.body A b)) (hne : theta ≠ 0)
    (hx : (ArlibCommunity.Foundations.Convex.Polytope.body A b).Nonempty) :
    ∃ i, 0 < coeff A theta i := by
  by_contra h
  push Not at h
  obtain ⟨x, hxK⟩ := hx
  have hray : ∀ t : Real, 0 ≤ t → x + t • theta ∈ ArlibCommunity.Foundations.Convex.Polytope.body A b := by
    intro t ht i
    have hi := h i
    have hxi := hxK i
    simp only [inner_add_right, real_inner_smul_right]
    dsimp [coeff] at hi
    nlinarith
  obtain ⟨C, hC⟩ := hK.exists_norm_le
  have hCx : ‖x‖ ≤ C := hC x hxK
  have htheta : 0 < ‖theta‖ := norm_pos_iff.mpr hne
  let t : Real := (C + ‖x‖ + 1) / ‖theta‖
  have ht : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg (by linarith [norm_nonneg x]) htheta.le
  have hCt : ‖x + t • theta‖ ≤ C := hC _ (hray t ht)
  have hlower : C + ‖x‖ + 1 ≤ ‖x + t • theta‖ + ‖x‖ := by
    calc
      _ = ‖t • theta‖ := by
        rw [norm_smul, Real.norm_of_nonneg ht]
        dsimp [t]
        rw [div_mul_cancel₀ _ htheta.ne']
      _ ≤ ‖x + t • theta‖ + ‖x‖ := by
        simpa only [add_sub_cancel_left] using norm_sub_le (x + t • theta) x
  linarith

theorem exists_neg_coeff_of_isBounded
    {A : ι → State n} {b : ι → Real} {theta : State n}
    (hK : Bornology.IsBounded (ArlibCommunity.Foundations.Convex.Polytope.body A b)) (hne : theta ≠ 0)
    (hx : (ArlibCommunity.Foundations.Convex.Polytope.body A b).Nonempty) :
    ∃ i, coeff A theta i < 0 := by
  obtain ⟨i, hi⟩ := exists_pos_coeff_of_isBounded hK (neg_ne_zero.mpr hne) hx
    (theta := -theta)
  refine ⟨i, ?_⟩
  simpa [coeff] using hi

/-! ## Exact chord interval -/

theorem mem_chordSet_iff
    {A : ι → State n} {b : ι → Real} {x theta : State n}
    (hx : x ∈ ArlibCommunity.Foundations.Convex.Polytope.body A b)
    (hneg : ∃ i, coeff A theta i < 0) (hpos : ∃ i, 0 < coeff A theta i)
    (t : Real) :
    t ∈ chordSet (ArlibCommunity.Foundations.Convex.Polytope.body A b) x theta ↔
      t ∈ Icc (lower A b x theta) (upper A b x theta) := by
  rw [ArlibCommunity.Foundations.MarkovChainTheory.mem_chordSet_iff, ArlibCommunity.Foundations.Convex.Polytope.mem_body, mem_Icc,
    lower_le_iff hx hneg, le_upper_iff hx hpos]
  constructor
  · intro ht
    constructor
    · intro i hi
      have hti := ht i
      simp only [inner_add_right, real_inner_smul_right] at hti
      apply (div_le_iff_of_neg hi).2
      dsimp [ratio, slack, coeff]
      nlinarith
    · intro i hi
      have hti := ht i
      simp only [inner_add_right, real_inner_smul_right] at hti
      apply (le_div_iff₀ hi).2
      dsimp [ratio, slack, coeff]
      nlinarith
  · rintro ⟨hlow, hupp⟩ i
    simp only [inner_add_right, real_inner_smul_right]
    rcases lt_trichotomy (coeff A theta i) 0 with hi | hi | hi
    · have hr := hlow i hi
      have := (div_le_iff_of_neg hi).1 hr
      dsimp [ratio, slack, coeff] at this ⊢
      nlinarith
    · have hxi := hx i
      dsimp [coeff] at hi
      rw [hi, mul_zero, add_zero]
      exact hxi
    · have hr := hupp i hi
      have := (le_div_iff₀ hi).1 hr
      dsimp [ratio, slack, coeff] at this ⊢
      nlinarith

theorem chordSet_eq_Icc
    {A : ι → State n} {b : ι → Real} {x theta : State n}
    (hx : x ∈ ArlibCommunity.Foundations.Convex.Polytope.body A b)
    (hneg : ∃ i, coeff A theta i < 0) (hpos : ∃ i, 0 < coeff A theta i) :
    chordSet (ArlibCommunity.Foundations.Convex.Polytope.body A b) x theta =
      Icc (lower A b x theta) (upper A b x theta) := by
  ext t
  exact mem_chordSet_iff hx hneg hpos t

theorem chordSet_eq_Icc_of_isBounded
    {A : ι → State n} {b : ι → Real} {x theta : State n}
    (hK : Bornology.IsBounded (ArlibCommunity.Foundations.Convex.Polytope.body A b))
    (hx : x ∈ ArlibCommunity.Foundations.Convex.Polytope.body A b) (htheta : theta ≠ 0) :
    chordSet (ArlibCommunity.Foundations.Convex.Polytope.body A b) x theta =
      Icc (lower A b x theta) (upper A b x theta) := by
  exact chordSet_eq_Icc hx
    (exists_neg_coeff_of_isBounded hK htheta ⟨x, hx⟩)
    (exists_pos_coeff_of_isBounded hK htheta ⟨x, hx⟩)

#print axioms measurable_lower
#print axioms measurable_upper
#print axioms chordSet_eq_Icc_of_isBounded

end ArlibCommunity.Foundations.MarkovChainTheory.PolytopeChord

end

section
/-!
# A finite-facet presentation of the hit-and-run proposal

This file turns the measurable facet endpoints from `PolytopeChord` into a parameterized
uniform interval kernel.  It then samples a sphere direction, samples the interval, and
maps `(x, theta, t)` to `x + t • theta`.
-/

open ArlibCommunity.Foundations.Convex ArlibCommunity.Foundations.MarkovChainTheory

open ArlibCommunity.Foundations.Convex ArlibCommunity.Foundations.MarkovChainTheory

namespace ArlibCommunity.Foundations.MarkovChainTheory.PolytopeHitAndRunExecution

open MeasureTheory ProbabilityTheory Set Metric
open ArlibCommunity.Foundations.Convex ArlibCommunity.Foundations.MarkovChainTheory ArlibCommunity.Foundations.MarkovChainTheory.PolytopeChord
open scoped InnerProductSpace ENNReal Classical

variable {n : Nat} {ι : Type*} [Fintype ι]

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev Direction (n : Nat) := Metric.sphere (0 : State n) 1

/-- Uniform line-parameter law on the interval computed by the finite facet scan. -/
noncomputable def intervalKernel (A : ι → State n) (b : ι → Real) :
    Kernel (State n × State n) Real where
  toFun p := ArlibCommunity.Foundations.Convex.uniformOn volume
    (Icc (lower A b p.1 p.2) (upper A b p.1 p.2))
  measurable' := by
    apply Measure.measurable_of_measurable_coe _
    intro T hT
    let S : Set ((State n × State n) × Real) :=
      {q | (q.2 ∈ T ∧ lower A b q.1.1 q.1.2 ≤ q.2) ∧
        q.2 ≤ upper A b q.1.1 q.1.2}
    let U : Set ((State n × State n) × Real) :=
      {q | lower A b q.1.1 q.1.2 ≤ q.2 ∧ q.2 ≤ upper A b q.1.1 q.1.2}
    have hS : MeasurableSet S := by
      exact (hT.preimage measurable_snd).inter
        (measurableSet_le ((measurable_lower A b).comp measurable_fst) measurable_snd) |>.inter
        (measurableSet_le measurable_snd ((measurable_upper A b).comp measurable_fst))
    have hU : MeasurableSet U := by
      exact (measurableSet_le ((measurable_lower A b).comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd ((measurable_upper A b).comp measurable_fst))
    have hnum : Measurable (fun p => volume {t | (p, t) ∈ S}) :=
      measurable_measure_prodMk_left hS
    have hden : Measurable (fun p => volume {t | (p, t) ∈ U}) :=
      measurable_measure_prodMk_left hU
    have hquot := hnum.div hden
    convert hquot using 1
    funext p
    rw [ArlibCommunity.Foundations.Convex.uniformOn_apply volume measurableSet_Icc hT]
    congr 1
    · congr 1
      ext t
      simp only [S, mem_inter_iff, mem_Icc, mem_setOf_eq]
      tauto
theorem intervalKernel_apply (A : ι → State n) (b : ι → Real)
    (p : State n × State n) :
    intervalKernel A b p = ArlibCommunity.Foundations.Convex.uniformOn volume
      (Icc (lower A b p.1 p.2) (upper A b p.1 p.2)) := rfl

instance (A : ι → State n) (b : ι → Real) : IsFiniteKernel (intervalKernel A b) := by
  refine ⟨1, ENNReal.one_lt_top, fun p => ?_⟩
  rw [intervalKernel_apply, ArlibCommunity.Foundations.Convex.uniformOn_def, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  exact ENNReal.inv_mul_le_one _

/-- Keep the starting point while drawing an independent sphere direction. -/
noncomputable def startDirectionKernel : Kernel (State n) (State n × Direction n) :=
  Kernel.prod Kernel.id (Kernel.const (State n) (unifSphere n))

instance [NeZero n] : IsMarkovKernel (startDirectionKernel (n := n)) := by
  unfold startDirectionKernel
  infer_instance

instance : IsFiniteKernel (startDirectionKernel (n := n)) := by
  unfold startDirectionKernel
  infer_instance

/-- The interval kernel with the subtype direction coerced to the ambient vector. -/
noncomputable def subtypeIntervalKernel (A : ι → State n) (b : ι → Real) :
    Kernel (State n × Direction n) Real :=
  Kernel.comap (intervalKernel A b)
    (fun p => (p.1, (p.2 : State n)))
    (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))

instance (A : ι → State n) (b : ι → Real) :
    IsFiniteKernel (subtypeIntervalKernel A b) := by
  unfold subtypeIntervalKernel
  infer_instance

instance (A : ι → State n) (b : ι → Real) :
    IsFiniteKernel (Kernel.prodMkLeft (State n) (subtypeIntervalKernel A b)) := by
  infer_instance

/-- Joint law of start, direction, and line parameter. -/
noncomputable def lineDrawKernel (A : ι → State n) (b : ι → Real) :
    Kernel (State n) ((State n × Direction n) × Real) :=
  Kernel.compProd startDirectionKernel
    (Kernel.prodMkLeft (State n) (subtypeIntervalKernel A b))

/-- Map a finite-facet line draw to its endpoint. -/
def lineEndpoint (q : (State n × Direction n) × Real) : State n :=
  q.1.1 + q.2 • (q.1.2 : State n)

theorem measurable_lineEndpoint : Measurable (lineEndpoint (n := n)) := by
  exact (continuous_fst.comp continuous_fst).add
    (continuous_snd.smul (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))) |>.measurable

/-- For a fixed start, the direction-indexed mapped interval law is a kernel. -/
noncomputable def directionEndpointKernel (A : ι → State n) (b : ι → Real)
    (x : State n) : Kernel (Direction n) (State n) where
  toFun theta := Measure.map (fun t : Real => x + t • (theta : State n))
    (ArlibCommunity.Foundations.Convex.uniformOn volume (Icc (lower A b x theta) (upper A b x theta)))
  measurable' := by
    let pull : Direction n → State n × State n := fun theta => (x, (theta : State n))
    let base : Kernel (Direction n) Real := Kernel.comap (intervalKernel A b) pull (by fun_prop)
    let joint : Kernel (Direction n) (Direction n × Real) :=
      Kernel.compProd Kernel.id (Kernel.prodMkLeft (Direction n) base)
    let out : Direction n × Real → State n := fun q => x + q.2 • (q.1 : State n)
    have hout : Measurable out := by fun_prop
    have hmap : Measurable fun theta => Kernel.map joint out theta := Kernel.measurable _
    convert hmap using 1
    funext theta
    ext T hT
    rw [Kernel.map_apply joint hout, Measure.map_apply hout hT]
    dsimp only [joint]
    rw [Kernel.compProd_apply (hT.preimage hout)]
    simp only [Kernel.id_apply, Kernel.prodMkLeft_apply, base, Kernel.comap_apply,
      intervalKernel_apply]
    rw [lintegral_dirac theta, Measure.map_apply (by fun_prop) hT]
    rfl

theorem directionEndpointKernel_apply (A : ι → State n) (b : ι → Real)
    (x : State n) (theta : Direction n) :
    directionEndpointKernel A b x theta =
      Measure.map (fun t : Real => x + t • (theta : State n))
        (ArlibCommunity.Foundations.Convex.uniformOn volume (Icc (lower A b x theta) (upper A b x theta))) := rfl

/-- The finite-facet proposal kernel. -/
noncomputable def finiteFacetProposal (A : ι → State n) (b : ι → Real) :
    Kernel (State n) (State n) :=
  Kernel.map (lineDrawKernel A b) lineEndpoint

theorem finiteFacetProposal_apply
    (A : ι → State n) (b : ι → Real) (x : State n) :
    finiteFacetProposal A b x =
      (unifSphere n).bind (fun theta =>
        Measure.map (fun t : Real => x + t • (theta : State n))
          (ArlibCommunity.Foundations.Convex.uniformOn volume
            (Icc (lower A b x theta) (upper A b x theta)))) := by
  ext T hT
  rw [finiteFacetProposal, Kernel.map_apply _ measurable_lineEndpoint,
    Measure.map_apply measurable_lineEndpoint hT,
    lineDrawKernel, Kernel.compProd_apply (hT.preimage measurable_lineEndpoint),
    Measure.bind_apply hT
      ((Kernel.aemeasurable (directionEndpointKernel A b x)).congr
        (Filter.Eventually.of_forall fun theta => directionEndpointKernel_apply A b x theta))]
  simp only [startDirectionKernel, Kernel.prod_apply, Kernel.id_apply,
    Kernel.const_apply, Kernel.prodMkLeft_apply]
  rw [lintegral_prod _
    ((Kernel.measurable_kernel_prodMk_left
      (hT.preimage measurable_lineEndpoint)).aemeasurable)]
  simp only [subtypeIntervalKernel, Kernel.comap_apply, intervalKernel_apply]
  rw [lintegral_dirac x]
  apply lintegral_congr
  intro theta
  rw [Measure.map_apply (by fun_prop) hT]
  rfl

theorem finiteFacetProposal_univ_le_one
    (A : ι → State n) (b : ι → Real) (x : State n) :
    finiteFacetProposal A b x Set.univ ≤ 1 := by
  rw [finiteFacetProposal_apply, Measure.bind_apply MeasurableSet.univ
    ((Kernel.aemeasurable (directionEndpointKernel A b x)).congr
      (Filter.Eventually.of_forall fun theta => directionEndpointKernel_apply A b x theta))]
  calc
    (∫⁻ theta, Measure.map (fun t : Real => x + t • (theta : State n))
          (ArlibCommunity.Foundations.Convex.uniformOn volume (Icc (lower A b x theta) (upper A b x theta))) Set.univ
        ∂unifSphere n) ≤ ∫⁻ _theta, 1 ∂unifSphere n := by
      apply lintegral_mono
      intro theta
      change Measure.map (fun t : Real => x + t • (theta : State n))
        (ArlibCommunity.Foundations.Convex.uniformOn volume (Icc (lower A b x theta) (upper A b x theta))) Set.univ ≤ 1
      rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, preimage_univ,
        ArlibCommunity.Foundations.Convex.uniformOn_def, Measure.smul_apply, smul_eq_mul,
        Measure.restrict_apply MeasurableSet.univ, univ_inter]
      exact ENNReal.inv_mul_le_one _
    _ = unifSphere n Set.univ := by simp
    _ ≤ 1 := unifSphere_univ_le_one n

/-- On a bounded polytope, the finite-facet proposal is exactly the existing denotational
hit-and-run proposal at every point of the body. -/
theorem finiteFacetProposal_eq_hitAndRunProposal
    (A : ι → State n) (b : ι → Real)
    (hK : Bornology.IsBounded (ArlibCommunity.Foundations.Convex.Polytope.body A b))
    (x : State n) (hx : x ∈ ArlibCommunity.Foundations.Convex.Polytope.body A b) [NeZero n] :
    finiteFacetProposal A b x = hitAndRunProposal (ArlibCommunity.Foundations.Convex.Polytope.body A b) x := by
  ext T hT
  rw [finiteFacetProposal_apply, hitAndRunProposal_apply_uniformOn
    (ArlibCommunity.Foundations.Convex.Polytope.measurableSet_body A b) x hT]
  rw [Measure.bind_apply hT
    ((Kernel.aemeasurable (directionEndpointKernel A b x)).congr
      (Filter.Eventually.of_forall fun theta => directionEndpointKernel_apply A b x theta))]
  apply lintegral_congr
  intro theta
  have htheta : (theta : State n) ≠ 0 := by
    intro hz
    have hnorm := theta.property
    simp [mem_sphere, dist_zero_right, hz] at hnorm
  rw [Measure.map_apply (by fun_prop) hT,
    chordSet_eq_Icc_of_isBounded hK hx htheta]
  rfl

/-! ## Completed Markov kernel -/

/-- Add the usual stay-put deficit to the finite-facet proposal. -/
noncomputable def finiteFacetHitAndRunAux (A : ι → State n) (b : ι → Real) :
    Kernel (State n) (State n) where
  toFun x := finiteFacetProposal A b x +
    (1 - finiteFacetProposal A b x Set.univ) • Measure.dirac x
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun T hT => ?_
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hT]
    exact (Kernel.measurable_coe (finiteFacetProposal A b) hT).add
      ((measurable_const.sub (Kernel.measurable_coe (finiteFacetProposal A b)
        MeasurableSet.univ)).mul ((measurable_one.indicator hT)))

theorem finiteFacetHitAndRunAux_apply (A : ι → State n) (b : ι → Real)
    (x : State n) :
    finiteFacetHitAndRunAux A b x = finiteFacetProposal A b x +
      (1 - finiteFacetProposal A b x Set.univ) • Measure.dirac x := rfl

instance (A : ι → State n) (b : ι → Real) :
    IsMarkovKernel (finiteFacetHitAndRunAux A b) := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [finiteFacetHitAndRunAux_apply, Measure.add_apply, Measure.smul_apply,
    smul_eq_mul, Measure.dirac_apply' _ MeasurableSet.univ]
  simp only [mem_univ, indicator_of_mem, Pi.one_apply, mul_one]
  exact add_tsub_cancel_of_le (finiteFacetProposal_univ_le_one A b x)

/-- Use the finite facet scan on the body.  Outside the body we retain the existing
totalized kernel; this branch is unreachable for a trajectory started in the body and it
makes the equality of kernels global rather than merely support-relative. -/
noncomputable def finiteFacetHitAndRun (A : ι → State n) (b : ι → Real) :
    Kernel (State n) (State n) :=
  Kernel.piecewise (ArlibCommunity.Foundations.Convex.Polytope.measurableSet_body A b)
    (finiteFacetHitAndRunAux A b) (hitAndRun (ArlibCommunity.Foundations.Convex.Polytope.body A b))

instance (A : ι → State n) (b : ι → Real) :
    IsMarkovKernel (finiteFacetHitAndRun A b) := by
  unfold finiteFacetHitAndRun
  infer_instance

/-- The finite-facet completed kernel is extensionally the repository's hit-and-run
kernel on every input. -/
theorem finiteFacetHitAndRun_eq_hitAndRun
    (A : ι → State n) (b : ι → Real)
    (hK : Bornology.IsBounded (ArlibCommunity.Foundations.Convex.Polytope.body A b)) [NeZero n] :
    finiteFacetHitAndRun A b = hitAndRun (ArlibCommunity.Foundations.Convex.Polytope.body A b) := by
  ext x T hT
  by_cases hx : x ∈ ArlibCommunity.Foundations.Convex.Polytope.body A b
  · rw [finiteFacetHitAndRun, Kernel.piecewise_apply, if_pos hx,
      finiteFacetHitAndRunAux_apply,
      hitAndRun_apply_set (ArlibCommunity.Foundations.Convex.Polytope.measurableSet_body A b) x hT,
      Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hT]
    rw [finiteFacetProposal_eq_hitAndRunProposal A b hK x hx]
  · rw [finiteFacetHitAndRun, Kernel.piecewise_apply, if_neg hx]

#print axioms finiteFacetHitAndRun_eq_hitAndRun

#print axioms intervalKernel_apply
#print axioms finiteFacetProposal_apply
#print axioms finiteFacetProposal_eq_hitAndRunProposal

end ArlibCommunity.Foundations.MarkovChainTheory.PolytopeHitAndRunExecution

end
