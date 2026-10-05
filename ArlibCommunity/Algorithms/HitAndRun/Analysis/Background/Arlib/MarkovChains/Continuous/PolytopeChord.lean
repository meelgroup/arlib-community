/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.Polytope
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.HitAndRun

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

namespace Arlib.MarkovChains.PolytopeChord

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
    (hx : x ∈ Arlib.Polytope.body A b) :
    lowerE A b x theta ≤ (0 : EReal) := by
  change lowerE A b x theta ≤ ((0 : Real) : EReal)
  rw [lowerE_le_coe_iff]
  intro i hi
  have hs : 0 ≤ slack A b x i := sub_nonneg.mpr (hx i)
  exact div_nonpos_of_nonneg_of_nonpos hs hi.le

theorem zero_le_upperE_of_mem
    {A : ι → State n} {b : ι → Real} {x theta : State n}
    (hx : x ∈ Arlib.Polytope.body A b) :
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
    (hx : x ∈ Arlib.Polytope.body A b) : lowerE A b x theta ≠ ⊤ :=
  ne_top_of_le_ne_top (EReal.coe_ne_top (0 : Real)) (lowerE_le_zero_of_mem hx)

theorem upperE_ne_bot_of_mem
    {A : ι → State n} {b : ι → Real} {x theta : State n}
    (hx : x ∈ Arlib.Polytope.body A b) : upperE A b x theta ≠ ⊥ :=
  ne_bot_of_le_ne_bot (EReal.coe_ne_bot (0 : Real)) (zero_le_upperE_of_mem hx)

theorem lower_le_iff
    {A : ι → State n} {b : ι → Real} {x theta : State n}
    (hx : x ∈ Arlib.Polytope.body A b) (hneg : ∃ i, coeff A theta i < 0)
    (t : Real) :
    lower A b x theta ≤ t ↔
      ∀ i, coeff A theta i < 0 → ratio A b x theta i ≤ t := by
  rw [← lowerE_le_coe_iff A b x theta t]
  unfold lower
  rw [← EReal.coe_le_coe_iff, EReal.coe_toReal
    (lowerE_ne_top_of_mem hx) (lowerE_ne_bot_of_exists_neg hneg)]

theorem le_upper_iff
    {A : ι → State n} {b : ι → Real} {x theta : State n}
    (hx : x ∈ Arlib.Polytope.body A b) (hpos : ∃ i, 0 < coeff A theta i)
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
    (hK : Bornology.IsBounded (Arlib.Polytope.body A b)) (hne : theta ≠ 0)
    (hx : (Arlib.Polytope.body A b).Nonempty) :
    ∃ i, 0 < coeff A theta i := by
  by_contra h
  push Not at h
  obtain ⟨x, hxK⟩ := hx
  have hray : ∀ t : Real, 0 ≤ t → x + t • theta ∈ Arlib.Polytope.body A b := by
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
    (hK : Bornology.IsBounded (Arlib.Polytope.body A b)) (hne : theta ≠ 0)
    (hx : (Arlib.Polytope.body A b).Nonempty) :
    ∃ i, coeff A theta i < 0 := by
  obtain ⟨i, hi⟩ := exists_pos_coeff_of_isBounded hK (neg_ne_zero.mpr hne) hx
    (theta := -theta)
  refine ⟨i, ?_⟩
  simpa [coeff] using hi

/-! ## Exact chord interval -/

theorem mem_chordSet_iff
    {A : ι → State n} {b : ι → Real} {x theta : State n}
    (hx : x ∈ Arlib.Polytope.body A b)
    (hneg : ∃ i, coeff A theta i < 0) (hpos : ∃ i, 0 < coeff A theta i)
    (t : Real) :
    t ∈ chordSet (Arlib.Polytope.body A b) x theta ↔
      t ∈ Icc (lower A b x theta) (upper A b x theta) := by
  rw [Arlib.MarkovChains.mem_chordSet_iff, Arlib.Polytope.mem_body, mem_Icc,
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
    (hx : x ∈ Arlib.Polytope.body A b)
    (hneg : ∃ i, coeff A theta i < 0) (hpos : ∃ i, 0 < coeff A theta i) :
    chordSet (Arlib.Polytope.body A b) x theta =
      Icc (lower A b x theta) (upper A b x theta) := by
  ext t
  exact mem_chordSet_iff hx hneg hpos t

theorem chordSet_eq_Icc_of_isBounded
    {A : ι → State n} {b : ι → Real} {x theta : State n}
    (hK : Bornology.IsBounded (Arlib.Polytope.body A b))
    (hx : x ∈ Arlib.Polytope.body A b) (htheta : theta ≠ 0) :
    chordSet (Arlib.Polytope.body A b) x theta =
      Icc (lower A b x theta) (upper A b x theta) := by
  exact chordSet_eq_Icc hx
    (exists_neg_coeff_of_isBounded hK htheta ⟨x, hx⟩)
    (exists_pos_coeff_of_isBounded hK htheta ⟨x, hx⟩)

#print axioms measurable_lower
#print axioms measurable_upper
#print axioms chordSet_eq_Icc_of_isBounded

end Arlib.MarkovChains.PolytopeChord
