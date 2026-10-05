/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.IntervalReduction

/-!
# The interleaved case: one-dimensional isoperimetry for the logistic measure

WIP.
-/

namespace Arlib

open MeasureTheory Set

/-! ### The Möbius shift `T` -/

/-- **The Möbius map `T c x = (1+c)x / (1+cx)`.**

On `[0,1]` it is the increasing bijection that, in the coordinate `ξ = log (x/(1-x))`, is the
translation `ξ ↦ ξ + log (1+c)`.  Equivalently: `x` is the mass `∫_α^t D / ∫_α^β D` carried by
`[α,t]`, and `T c x` is the mass carried by `[α,t']` where `t'` is the point at logistic
distance `log (1+c)` to the right of `t`. -/
noncomputable def logisticShift (c x : ℝ) : ℝ := (1 + c) * x / (1 + c * x)

theorem logisticShift_zero (c : ℝ) : logisticShift c 0 = 0 := by simp [logisticShift]

theorem logisticShift_one {c : ℝ} (hc : 0 ≤ c) : logisticShift c 1 = 1 := by
  have h : (1 : ℝ) + c * 1 ≠ 0 := by positivity
  rw [logisticShift, mul_one, div_eq_one_iff_eq h]
  ring

/-- The denominator of `Arlib.logisticShift` is positive on the relevant range. -/
theorem logisticShift_den_pos {c x : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) : 0 < 1 + c * x := by
  positivity

theorem logisticShift_nonneg {c x : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) : 0 ≤ logisticShift c x :=
  div_nonneg (by positivity) (logisticShift_den_pos hc hx).le

theorem logisticShift_le_one {c x : ℝ} (hc : 0 ≤ c) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    logisticShift c x ≤ 1 := by
  rw [logisticShift, div_le_one (logisticShift_den_pos hc hx0)]
  nlinarith

/-- `T` is monotone on `[0, ∞)`. -/
theorem logisticShift_mono {c x y : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) (hxy : x ≤ y) :
    logisticShift c x ≤ logisticShift c y := by
  have hdx := logisticShift_den_pos hc hx
  have hdy := logisticShift_den_pos hc (hx.trans hxy)
  rw [logisticShift, logisticShift, div_le_div_iff₀ hdx hdy]
  nlinarith

/-- `T` moves points to the right on `[0,1]`. -/
theorem self_le_logisticShift {c x : ℝ} (hc : 0 ≤ c) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x ≤ logisticShift c x := by
  rw [logisticShift, le_div_iff₀ (logisticShift_den_pos hc hx0)]
  nlinarith [mul_nonneg (mul_nonneg hc hx0) (sub_nonneg.2 hx1)]

/-- **`T` is subadditive, in the ratio form.**  Because `T` is concave with `T 0 = 0`, the
quotient `T z / z` decreases, so `T S * z ≤ T z * S` whenever `0 ≤ z ≤ S`.  Summing this over a
countable partition is what turns the one-interval bound into the general one. -/
theorem logisticShift_ratio {c z S : ℝ} (hc : 0 ≤ c) (hz : 0 ≤ z) (hzS : z ≤ S) :
    logisticShift c S * z ≤ logisticShift c z * S := by
  have hdz := logisticShift_den_pos hc hz
  have hdS := logisticShift_den_pos hc (hz.trans hzS)
  have hS0 : 0 ≤ S := hz.trans hzS
  have h1 : 0 ≤ (1 + c) * S * z * (c * (S - z)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hS0) hz) (mul_nonneg hc (by linarith))
  rw [logisticShift, logisticShift, div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_le_div_iff₀ hdS hdz]
  nlinarith [h1]

/-- **The Möbius inequality, in the form the component argument consumes.**

If `P ≤ a ≤ b ≤ Q` lie in `[0,1]` and the outer pair dominates the inner pair under `T` — that
is `T P ≤ a` and `T b ≤ Q`, which says `[P,Q]` contains the full `log(1+c)`-neighbourhood of
`[a,b]` — then `T (b - a) ≤ Q - P`.

The engine is the polynomial identity

  `(1+c)b(1+c-ca)(1+c(b-a)) - a(1+cb)(1+c(b-a)) - (1+c)(b-a)(1+cb)(1+c-ca)`
    `= c·a·(1-b)·(2 + c(1+b-a))`,

whose right-hand side is nonnegative exactly because `a ≥ 0` and `b ≤ 1`.  Written without
denominators it is the statement `T b - T⁻¹ a ≥ T (b - a)`. -/
theorem mobius_key {c P a b Q : ℝ} (hc : 0 ≤ c) (hP0 : 0 ≤ P) (hPa : P ≤ a) (hab : a ≤ b)
    (hbQ : b ≤ Q) (hQ1 : Q ≤ 1) (hTP : logisticShift c P ≤ a) (hTb : logisticShift c b ≤ Q) :
    logisticShift c (b - a) ≤ Q - P := by
  have ha0 : 0 ≤ a := hP0.trans hPa
  have hb0 : 0 ≤ b := ha0.trans hab
  have hb1 : b ≤ 1 := hbQ.trans hQ1
  have hA : (0 : ℝ) < 1 + c * b := by positivity
  have hB : (0 : ℝ) < 1 + c - c * a := by nlinarith [hab.trans hb1]
  have hC : (0 : ℝ) < 1 + c * (b - a) := by nlinarith
  -- clear the denominators in the two hypotheses
  have hP' : P * (1 + c - c * a) ≤ a := by
    rw [logisticShift, div_le_iff₀ (logisticShift_den_pos hc hP0)] at hTP
    nlinarith
  have hQ' : (1 + c) * b ≤ Q * (1 + c * b) := by
    rw [logisticShift, div_le_iff₀ hA] at hTb
    linarith
  have e1 : (1 + c) * b * ((1 + c - c * a) * (1 + c * (b - a)))
      ≤ Q * (1 + c * b) * ((1 + c - c * a) * (1 + c * (b - a))) :=
    mul_le_mul_of_nonneg_right hQ' (by positivity)
  have e2 : P * (1 + c - c * a) * ((1 + c * b) * (1 + c * (b - a)))
      ≤ a * ((1 + c * b) * (1 + c * (b - a))) :=
    mul_le_mul_of_nonneg_right hP' (by positivity)
  have e3 : 0 ≤ c * a * (1 - b) * (2 + c * (1 + b - a)) := by
    have : (0 : ℝ) ≤ 2 + c * (1 + b - a) := by nlinarith
    have h1b : (0 : ℝ) ≤ 1 - b := by linarith
    positivity
  rw [logisticShift, div_le_iff₀ hC]
  have key : 0 ≤ ((Q - P) * (1 + c * (b - a)) - (1 + c) * (b - a))
      * ((1 + c * b) * (1 + c - c * a)) := by nlinarith [e1, e2, e3]
  nlinarith [key, mul_pos hA hB]

/-- `T` moves points of `(0,1)` strictly to the right. -/
theorem lt_logisticShift {c x : ℝ} (hc : 0 < c) (hx0 : 0 < x) (hx1 : x < 1) :
    x < logisticShift c x := by
  rw [logisticShift, lt_div_iff₀ (logisticShift_den_pos hc.le hx0.le)]
  nlinarith [mul_pos (mul_pos hc hx0) (sub_pos.2 hx1)]

/-- Composing with `T` preserves continuity, on functions with nonnegative values. -/
theorem continuous_logisticShift_comp {c : ℝ} (hc : 0 ≤ c) {f : ℝ → ℝ} (hf : Continuous f)
    (hf0 : ∀ t, 0 ≤ f t) : Continuous fun t => logisticShift c (f t) := by
  simp only [logisticShift]
  exact Continuous.div (continuous_const.mul hf) (continuous_const.add (continuous_const.mul hf))
    fun t => (logisticShift_den_pos hc (hf0 t)).ne'

/-! ### Two elementary transfer principles -/

/-- A continuous inequality valid on `S` is valid at `sSup S`. -/
theorem nonneg_csSup {Φ : ℝ → ℝ} (hΦ : Continuous Φ) {S : Set ℝ} (hne : S.Nonempty)
    (hbd : BddAbove S) (h : ∀ s ∈ S, 0 ≤ Φ s) : 0 ≤ Φ (sSup S) :=
  closure_minimal h (isClosed_le continuous_const hΦ) (csSup_mem_closure hne hbd)

/-- A continuous inequality valid on `S` is valid at `sInf S`. -/
theorem nonneg_csInf {Φ : ℝ → ℝ} (hΦ : Continuous Φ) {S : Set ℝ} (hne : S.Nonempty)
    (hbd : BddBelow S) (h : ∀ s ∈ S, 0 ≤ Φ s) : 0 ≤ Φ (sInf S) :=
  closure_minimal h (isClosed_le continuous_const hΦ) (csInf_mem_closure hne hbd)

/-- Two connected components of the same set are equal or disjoint. -/
theorem connectedComponentIn_eq_or_disjoint {X : Type*} [TopologicalSpace X] (U : Set X)
    (y z : X) : connectedComponentIn U y = connectedComponentIn U z ∨
      Disjoint (connectedComponentIn U y) (connectedComponentIn U z) := by
  by_cases h : Disjoint (connectedComponentIn U y) (connectedComponentIn U z)
  · exact Or.inr h
  · obtain ⟨w, hwy, hwz⟩ := Set.not_disjoint_iff.mp h
    exact Or.inl ((connectedComponentIn_eq hwy).trans (connectedComponentIn_eq hwz).symm)

/-! ### The separation neighbourhood -/

section Nbhd

variable {c : ℝ} {F : ℝ → ℝ} {α β : ℝ}

/-- **The open `log(1+c)`-neighbourhood of `Z`, read through `F`.**

`t` belongs to `Arlib.sepNbhd c F Z` exactly when some `s ∈ Z` fails the separation condition
`max (F s) (F t) ≥ T c (min (F s) (F t))` against `t`.  In the logistic coordinate
`ξ = log (x/(1-x))` this is the open `log(1+c)`-neighbourhood of `ξ (F '' Z)`. -/
def sepNbhd (c : ℝ) (F : ℝ → ℝ) (Z : Set ℝ) : Set ℝ :=
  {t | ∃ s ∈ Z, F t < logisticShift c (F s) ∧ F s < logisticShift c (F t)}

theorem isOpen_sepNbhd (hc : 0 ≤ c) (hFc : Continuous F) (hF0 : ∀ t, 0 ≤ F t) (Z : Set ℝ) :
    IsOpen (sepNbhd c F Z) := by
  have hTF := continuous_logisticShift_comp hc hFc hF0
  have hEq : sepNbhd c F Z = ⋃ s ∈ Z, (F ⁻¹' Set.Iio (logisticShift c (F s))) ∩
      ((fun t => logisticShift c (F t)) ⁻¹' Set.Ioi (F s)) := by
    ext t
    constructor
    · rintro ⟨s, hs, h1, h2⟩; exact Set.mem_biUnion hs ⟨h1, h2⟩
    · intro h
      obtain ⟨s, hs, h1, h2⟩ := Set.mem_iUnion₂.1 h
      exact ⟨s, hs, h1, h2⟩
  rw [hEq]
  exact isOpen_biUnion fun s _ =>
    (hFc.isOpen_preimage _ isOpen_Iio).inter (hTF.isOpen_preimage _ isOpen_Ioi)

theorem sepNbhd_subset_Ioo (hc : 0 ≤ c) (hFm : Monotone F) (hF0 : ∀ t, 0 ≤ F t)
    (hF1 : ∀ t, F t ≤ 1) (hFα : F α = 0) (hFβ : F β = 1) (Z : Set ℝ) :
    sepNbhd c F Z ⊆ Set.Ioo α β := by
  rintro t ⟨s, hs, h1, h2⟩
  refine ⟨?_, ?_⟩
  · rcases le_or_gt t α with hcon | h
    · exfalso
      have hle : F t ≤ 0 := hFα ▸ hFm hcon
      have hz : F t = 0 := le_antisymm hle (hF0 t)
      rw [hz, logisticShift_zero] at h2
      exact absurd h2 (not_lt.2 (hF0 s))
    · exact h
  · rcases lt_or_ge t β with h | hcon
    · exact h
    · exfalso
      have hge : 1 ≤ F t := hFβ ▸ hFm hcon
      have := logisticShift_le_one hc (hF0 s) (hF1 s)
      linarith

/-- A point of `Z` at which `F` is strictly between `0` and `1` lies in its own
neighbourhood. -/
theorem mem_sepNbhd_self (hc : 0 < c) {Z : Set ℝ} {s : ℝ} (hs : s ∈ Z) (h0 : 0 < F s)
    (h1 : F s < 1) : s ∈ sepNbhd c F Z :=
  ⟨s, hs, lt_logisticShift hc h0 h1, lt_logisticShift hc h0 h1⟩

end Nbhd

/-! ### Measure-theoretic bookkeeping for a continuous distribution function -/

section Stieltjes

variable {F : ℝ → ℝ} {μ : Measure ℝ}

/-- With no atoms, the closed interval is bounded by the increment of `F`. -/
theorem measureReal_Icc_le [IsFiniteMeasure μ] (hpt : ∀ x : ℝ, μ {x} = 0)
    (hIoc : ∀ p q : ℝ, p ≤ q → μ.real (Set.Ioc p q) = F q - F p) {u v : ℝ} (huv : u ≤ v) :
    μ.real (Set.Icc u v) ≤ F v - F u := by
  have hsub : Set.Icc u v ⊆ Set.Ioc u v ∪ {u} := by
    intro y hy
    rcases lt_or_eq_of_le hy.1 with h | h
    · exact Or.inl ⟨h, hy.2⟩
    · exact Or.inr h.symm
  have h1 : μ.real (Set.Icc u v) ≤ μ.real (Set.Ioc u v ∪ {u}) := measureReal_mono hsub
  have h2 : μ.real (Set.Ioc u v ∪ {u}) ≤ μ.real (Set.Ioc u v) + μ.real ({u} : Set ℝ) :=
    measureReal_union_le _ _
  have h3 : μ.real ({u} : Set ℝ) = 0 := by simp [Measure.real, hpt u]
  rw [hIoc u v huv] at h2
  linarith

/-- With no atoms, the open interval already carries the full increment of `F`. -/
theorem le_measureReal_Ioo [IsFiniteMeasure μ] (hpt : ∀ x : ℝ, μ {x} = 0)
    (hIoc : ∀ p q : ℝ, p ≤ q → μ.real (Set.Ioc p q) = F q - F p) {u v : ℝ} (huv : u ≤ v) :
    F v - F u ≤ μ.real (Set.Ioo u v) := by
  have hsub : Set.Ioc u v ⊆ Set.Ioo u v ∪ {v} := by
    intro y hy
    rcases lt_or_eq_of_le hy.2 with h | h
    · exact Or.inl ⟨hy.1, h⟩
    · exact Or.inr h
  have h1 : μ.real (Set.Ioc u v) ≤ μ.real (Set.Ioo u v ∪ {v}) := measureReal_mono hsub
  have h2 : μ.real (Set.Ioo u v ∪ {v}) ≤ μ.real (Set.Ioo u v) + μ.real ({v} : Set ℝ) :=
    measureReal_union_le _ _
  have h3 : μ.real ({v} : Set ℝ) = 0 := by simp [Measure.real, hpt v]
  rw [hIoc u v huv] at h1
  linarith

end Stieltjes

/-! ### The one-component logistic isoperimetric inequality -/

section Component

variable {c : ℝ} {F : ℝ → ℝ} {α β : ℝ} {μ : Measure ℝ}

/-- **The crux: the logistic isoperimetric inequality on a single connected component.**

Let `J` be a connected component of the open neighbourhood `N = Arlib.sepNbhd c F Z`, and let
`p = inf J`, `q = sup J`, `a = inf (Z ∩ J)`, `b = sup (Z ∩ J)`.  Maximality of `J` forces
`T c (F b) ≤ F q` and `T c (F p) ≤ F a` — every point within logistic distance `log(1+c)` of a
point of `Z ∩ J` is again in `N`, and is joined to it by a segment inside `N`, hence lies in the
same component.  The Möbius inequality `Arlib.mobius_key` then converts those two endpoint
bounds into `T c (F b - F a) ≤ F q - F p`, which is the claim, since `μ (Z ∩ J) ≤ F b - F a` and
`F q - F p ≤ μ J`. -/
theorem logisticShift_measureReal_connectedComponentIn (hc : 0 < c) (hFc : Continuous F)
    (hFm : Monotone F) (hF0 : ∀ t, 0 ≤ F t) (hF1 : ∀ t, F t ≤ 1) (hFα : F α = 0) (hFβ : F β = 1)
    [IsFiniteMeasure μ] (hpt : ∀ x : ℝ, μ {x} = 0)
    (hIoc : ∀ p q : ℝ, p ≤ q → μ.real (Set.Ioc p q) = F q - F p)
    (Z : Set ℝ) {x : ℝ} (hx : x ∈ sepNbhd c F Z) :
    logisticShift c (μ.real (Z ∩ connectedComponentIn (sepNbhd c F Z) x))
      ≤ μ.real (connectedComponentIn (sepNbhd c F Z) x) := by
  set N := sepNbhd c F Z with hNdef
  have hNsub : N ⊆ Set.Ioo α β := sepNbhd_subset_Ioo hc.le hFm hF0 hF1 hFα hFβ Z
  set J := connectedComponentIn N x with hJdef
  have hxJ : x ∈ J := mem_connectedComponentIn hx
  have hJsub : J ⊆ N := connectedComponentIn_subset N x
  have hJconn : IsConnected J := isConnected_connectedComponentIn_iff.2 hx
  have hJbA : BddAbove J := (bddAbove_Ioo (a := α) (b := β)).mono (hJsub.trans hNsub)
  have hJbB : BddBelow J := (bddBelow_Ioo (a := β) (b := α)).mono (hJsub.trans hNsub)
  set p := sInf J with hpdef
  set q := sSup J with hqdef
  have hpq : p ≤ q := csInf_le_csSup hJconn.nonempty hJbB hJbA
  have hIooJ : Set.Ioo p q ⊆ J := hJconn.Ioo_csInf_csSup_subset hJbB hJbA
  have hJlower : F q - F p ≤ μ.real J :=
    (le_measureReal_Ioo hpt hIoc hpq).trans (measureReal_mono hIooJ)
  rcases Set.eq_empty_or_nonempty (Z ∩ J) with hZJe | hZJn
  · rw [hZJe]
    simp [logisticShift_zero]
  have hZJsub : Z ∩ J ⊆ J := Set.inter_subset_right
  have hbA : BddAbove (Z ∩ J) := hJbA.mono hZJsub
  have hbB : BddBelow (Z ∩ J) := hJbB.mono hZJsub
  set a := sInf (Z ∩ J) with hadef
  set b := sSup (Z ∩ J) with hbdef
  have hab : a ≤ b := csInf_le_csSup hZJn hbB hbA
  have hupper : μ.real (Z ∩ J) ≤ F b - F a :=
    (measureReal_mono (subset_Icc_csInf_csSup hbB hbA)).trans (measureReal_Icc_le hpt hIoc hab)
  -- **right maximality**: no point of `Z ∩ J` reaches past `q` under `T`
  have hptq : ∀ s ∈ Z ∩ J, logisticShift c (F s) ≤ F q := by
    intro s hs
    by_contra hcon
    rw [not_le] at hcon
    have hsq : s ≤ q := le_csSup hJbA hs.2
    have hlt : F s < logisticShift c (F s) := lt_of_le_of_lt (hFm hsq) hcon
    have hmem : Set.Iio (logisticShift c (F s)) ∈ nhds (F q) := isOpen_Iio.mem_nhds hcon
    have h0 : ∀ᶠ y in nhds q, F y < logisticShift c (F s) := hFc.tendsto q hmem
    obtain ⟨t, hFt, htq⟩ :=
      ((h0.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Set.Ioi q))).exists
    have hst : s ≤ t := hsq.trans htq.le
    have hIccN : Set.Icc s t ⊆ N := fun r hr =>
      ⟨s, hs.1, lt_of_le_of_lt (hFm hr.2) hFt,
        lt_of_lt_of_le hlt (logisticShift_mono hc.le (hF0 s) (hFm hr.1))⟩
    have hsubJ : Set.Icc s t ⊆ J := by
      have h := (isPreconnected_Icc (a := s) (b := t)).subset_connectedComponentIn
        (Set.left_mem_Icc.2 hst) hIccN
      rwa [← connectedComponentIn_eq hs.2] at h
    exact absurd (le_csSup hJbA (hsubJ (Set.right_mem_Icc.2 hst))) (not_le.2 htq)
  -- **left maximality**: no point of `Z ∩ J` reaches before `p` under `T⁻¹`
  have hptp : ∀ s ∈ Z ∩ J, logisticShift c (F p) ≤ F s := by
    intro s hs
    by_contra hcon
    rw [not_le] at hcon
    have hps : p ≤ s := csInf_le hJbB hs.2
    have hlt : F s < logisticShift c (F s) :=
      lt_of_lt_of_le hcon (logisticShift_mono hc.le (hF0 p) (hFm hps))
    have hTFc : Continuous fun y => logisticShift c (F y) :=
      continuous_logisticShift_comp hc.le hFc hF0
    have hmem : Set.Ioi (F s) ∈ nhds (logisticShift c (F p)) := isOpen_Ioi.mem_nhds hcon
    have h0 : ∀ᶠ y in nhds p, F s < logisticShift c (F y) := hTFc.tendsto p hmem
    obtain ⟨t, hFt, htp⟩ :=
      ((h0.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Set.Iio p))).exists
    have hts : t ≤ s := htp.le.trans hps
    have hIccN : Set.Icc t s ⊆ N := fun r hr =>
      ⟨s, hs.1, lt_of_le_of_lt (hFm hr.2) hlt,
        lt_of_lt_of_le hFt (logisticShift_mono hc.le (hF0 t) (hFm hr.1))⟩
    have hsubJ : Set.Icc t s ⊆ J := by
      have h := (isPreconnected_Icc (a := t) (b := s)).subset_connectedComponentIn
        (Set.right_mem_Icc.2 hts) hIccN
      rwa [← connectedComponentIn_eq hs.2] at h
    exact absurd (csInf_le hJbB (hsubJ (Set.left_mem_Icc.2 hts))) (not_le.2 htp)
  -- transfer the two endpoint bounds to `b = sup` and `a = inf`
  have hTFc : Continuous fun y => logisticShift c (F y) :=
    continuous_logisticShift_comp hc.le hFc hF0
  have hFq : logisticShift c (F b) ≤ F q := by
    have h := nonneg_csSup (Φ := fun s => F q - logisticShift c (F s))
      (continuous_const.sub hTFc) hZJn hbA fun s hs => sub_nonneg.2 (hptq s hs)
    simpa [hbdef] using sub_nonneg.1 h
  have hFp : logisticShift c (F p) ≤ F a := by
    have h := nonneg_csInf (Φ := fun s => F s - logisticShift c (F p))
      (hFc.sub continuous_const) hZJn hbB fun s hs => sub_nonneg.2 (hptp s hs)
    simpa [hadef] using sub_nonneg.1 h
  have hPa : F p ≤ F a := (self_le_logisticShift hc.le (hF0 p) (hF1 p)).trans hFp
  have hbq : F b ≤ F q := hFm (csSup_le_csSup hJbA hZJn hZJsub)
  calc logisticShift c (μ.real (Z ∩ J))
      ≤ logisticShift c (F b - F a) :=
        logisticShift_mono hc.le measureReal_nonneg hupper
    _ ≤ F q - F p := mobius_key hc.le (hF0 p) hPa (hFm hab) hbq (hF1 q) hFp hFq
    _ ≤ μ.real J := hJlower

/-- **The one-dimensional isoperimetric inequality for the logistic measure.**

`T c (μ Z) ≤ μ (Z^δ)`, where `Z^δ = Arlib.sepNbhd c F Z` is the open `log(1+c)`-neighbourhood of
`Z` measured in the logistic coordinate.

The proof decomposes the open set `Z^δ` into its (countably many) connected components, applies
`Arlib.logisticShift_measureReal_connectedComponentIn` on each, and reassembles with the
subadditivity of `T` in its ratio form `Arlib.logisticShift_ratio`.  Working with the ratio
rather than with `∑ T zₙ ≥ T (∑ zₙ)` keeps the whole summation inside `ℝ≥0∞`, where no
summability side conditions arise. -/
theorem logistic_isoperimetry (hc : 0 < c) (hFc : Continuous F) (hFm : Monotone F)
    (hF0 : ∀ t, 0 ≤ F t) (hF1 : ∀ t, F t ≤ 1) (hFα : F α = 0) (hFβ : F β = 1)
    [IsFiniteMeasure μ] (hpt : ∀ x : ℝ, μ {x} = 0)
    (hIoc : ∀ p q : ℝ, p ≤ q → μ.real (Set.Ioc p q) = F q - F p)
    {Z : Set ℝ} (hZm : MeasurableSet Z) (hZsub : Z ⊆ Set.Icc α β) :
    logisticShift c (μ.real Z) ≤ μ.real (sepNbhd c F Z) := by
  classical
  set N := sepNbhd c F Z with hNdef
  have hNopen : IsOpen N := isOpen_sepNbhd hc.le hFc hF0 Z
  have hNsub : N ⊆ Set.Ioo α β := sepNbhd_subset_Ioo hc.le hFm hF0 hF1 hFα hFβ Z
  -- **Step 1.**  `Z` and `Z ∩ N` carry the same mass: what `Z` loses is contained in the two
  -- level sets `F = 0` and `F = 1`, and each of those is `μ`-null.
  have hE0 : μ.real {t | t ∈ Set.Icc α β ∧ F t = 0} = 0 := by
    rcases Set.eq_empty_or_nonempty {t | t ∈ Set.Icc α β ∧ F t = 0} with h | ⟨t₁, ht₁⟩
    · rw [h]; simp
    · have hbA : BddAbove {t | t ∈ Set.Icc α β ∧ F t = 0} := ⟨β, fun t ht => ht.1.2⟩
      have hαt : α ≤ sSup {t | t ∈ Set.Icc α β ∧ F t = 0} := ht₁.1.1.trans (le_csSup hbA ht₁)
      have hFs : F (sSup {t | t ∈ Set.Icc α β ∧ F t = 0}) = 0 := by
        have h1 := nonneg_csSup (Φ := fun s => -F s) (continuous_neg.comp hFc) ⟨t₁, ht₁⟩ hbA
          fun s hs => by simp [hs.2]
        have h2 := hF0 (sSup {t | t ∈ Set.Icc α β ∧ F t = 0})
        simp only [neg_nonneg] at h1
        linarith
      have hsub : {t | t ∈ Set.Icc α β ∧ F t = 0} ⊆
          Set.Icc α (sSup {t | t ∈ Set.Icc α β ∧ F t = 0}) := fun t ht => ⟨ht.1.1, le_csSup hbA ht⟩
      have h2 := (measureReal_mono hsub (μ := μ)).trans (measureReal_Icc_le hpt hIoc hαt)
      rw [hFs, hFα] at h2
      have h3 := measureReal_nonneg (μ := μ) (s := {t | t ∈ Set.Icc α β ∧ F t = 0})
      linarith
  have hE1 : μ.real {t | t ∈ Set.Icc α β ∧ F t = 1} = 0 := by
    rcases Set.eq_empty_or_nonempty {t | t ∈ Set.Icc α β ∧ F t = 1} with h | ⟨t₁, ht₁⟩
    · rw [h]; simp
    · have hbB : BddBelow {t | t ∈ Set.Icc α β ∧ F t = 1} := ⟨α, fun t ht => ht.1.1⟩
      have htβ : sInf {t | t ∈ Set.Icc α β ∧ F t = 1} ≤ β := (csInf_le hbB ht₁).trans ht₁.1.2
      have hFs : F (sInf {t | t ∈ Set.Icc α β ∧ F t = 1}) = 1 := by
        have h1 := nonneg_csInf (Φ := fun s => F s - 1) (hFc.sub continuous_const) ⟨t₁, ht₁⟩ hbB
          fun s hs => by simp [hs.2]
        have h2 := hF1 (sInf {t | t ∈ Set.Icc α β ∧ F t = 1})
        simp only [sub_nonneg] at h1
        linarith
      have hsub : {t | t ∈ Set.Icc α β ∧ F t = 1} ⊆
          Set.Icc (sInf {t | t ∈ Set.Icc α β ∧ F t = 1}) β := fun t ht => ⟨csInf_le hbB ht, ht.1.2⟩
      have h2 := (measureReal_mono hsub (μ := μ)).trans (measureReal_Icc_le hpt hIoc htβ)
      rw [hFs, hFβ] at h2
      have h3 := measureReal_nonneg (μ := μ) (s := {t | t ∈ Set.Icc α β ∧ F t = 1})
      linarith
  have hdiff : Z \ N ⊆ {t | t ∈ Set.Icc α β ∧ F t = 0} ∪ {t | t ∈ Set.Icc α β ∧ F t = 1} := by
    rintro s ⟨hsZ, hsN⟩
    rcases eq_or_lt_of_le (hF0 s) with h0 | h0
    · exact Or.inl ⟨hZsub hsZ, h0.symm⟩
    rcases eq_or_lt_of_le (hF1 s) with h1 | h1
    · exact Or.inr ⟨hZsub hsZ, h1⟩
    · exact absurd (mem_sepNbhd_self hc hsZ h0 h1) hsN
  have hZN : μ.real (Z ∩ N) = μ.real Z := by
    refine measureReal_eq_measureReal_of_null_sdiff Set.inter_subset_left ?_
    have hEq : Z \ (Z ∩ N) = Z \ N := by
      ext y; simp only [Set.mem_sdiff, Set.mem_inter_iff, not_and]; tauto
    rw [hEq]
    exact measureReal_mono_null hdiff (measureReal_union_null hE0 hE1)
  rw [← hZN]
  -- **Step 2.**  Decompose `N` into its connected components.
  rcases eq_or_lt_of_le (measureReal_nonneg : (0 : ℝ) ≤ μ.real (Z ∩ N)) with hS0 | hS0
  · rw [← hS0, logisticShift_zero]; exact measureReal_nonneg
  set S := μ.real (Z ∩ N) with hSdef
  obtain ⟨e, he⟩ := exists_surjective_nat ℚ
  set B : ℕ → Set ℝ := fun n => connectedComponentIn N ((e n : ℚ) : ℝ) with hBdef
  set A : ℕ → Set ℝ := fun n => if ∀ m, m < n → B m ≠ B n then B n else ∅ with hAdef
  have hBsubN : ∀ n, B n ⊆ N := fun n => connectedComponentIn_subset N _
  have hAsub : ∀ n, A n ⊆ B n := by
    intro n
    simp only [hAdef]
    split_ifs
    · exact subset_rfl
    · exact Set.empty_subset _
  have hAmeas : ∀ n, MeasurableSet (A n) := by
    intro n
    simp only [hAdef]
    split_ifs
    · exact (hNopen.connectedComponentIn).measurableSet
    · exact MeasurableSet.empty
  have hAunion : ⋃ n, A n = N := by
    refine Set.Subset.antisymm (Set.iUnion_subset fun n => (hAsub n).trans (hBsubN n)) ?_
    intro t ht
    have hex : ∃ n, t ∈ B n := by
      have hCopen : IsOpen (connectedComponentIn N t) := hNopen.connectedComponentIn
      have hCne : (connectedComponentIn N t).Nonempty := ⟨t, mem_connectedComponentIn ht⟩
      obtain ⟨r, hyC⟩ := Rat.denseRange_cast.exists_mem_open hCopen hCne
      obtain ⟨n, rfl⟩ := he r
      refine ⟨n, ?_⟩
      have hmem := mem_connectedComponentIn ht
      rwa [connectedComponentIn_eq hyC] at hmem
    refine Set.mem_iUnion.2 ⟨Nat.find hex, ?_⟩
    have hn0 : t ∈ B (Nat.find hex) := Nat.find_spec hex
    simp only [hAdef]
    rw [if_pos]
    · exact hn0
    · exact fun m hm hEq => Nat.find_min hex hm (hEq ▸ hn0)
  have hAdisj : Pairwise (Function.onFun Disjoint A) := by
    have key : ∀ m n : ℕ, m < n → Disjoint (A m) (A n) := by
      intro m n hmn
      by_cases hn : ∀ k, k < n → B k ≠ B n
      · have hAn : A n = B n := by simp only [hAdef]; rw [if_pos hn]
        rw [hAn]
        exact ((connectedComponentIn_eq_or_disjoint N _ _).resolve_left (hn m hmn)).mono_left
          (hAsub m)
      · have hAn : A n = ∅ := by simp only [hAdef]; rw [if_neg hn]
        rw [hAn]
        simp
    intro m n hmn
    rcases lt_or_gt_of_ne hmn with h | h
    · exact key m n h
    · exact (key n m h).symm
  have hcomp : ∀ n, logisticShift c (μ.real (Z ∩ A n)) ≤ μ.real (A n) := by
    intro n
    by_cases hn : ∀ k, k < n → B k ≠ B n
    · have hAn : A n = B n := by simp only [hAdef]; rw [if_pos hn]
      rw [hAn]
      by_cases hmem : ((e n : ℚ) : ℝ) ∈ N
      · exact logisticShift_measureReal_connectedComponentIn hc hFc hFm hF0 hF1 hFα hFβ hpt
          hIoc Z hmem
      · simp only [hBdef, connectedComponentIn_eq_empty hmem]
        simp [logisticShift_zero]
    · have hAn : A n = ∅ := by simp only [hAdef]; rw [if_neg hn]
      rw [hAn]
      simp [logisticShift_zero]
  -- **Step 3.**  Sum the component bounds through the subadditivity ratio of `T`.
  set ρ := logisticShift c S / S with hρdef
  have hρ0 : 0 ≤ ρ := div_nonneg (logisticShift_nonneg hc.le measureReal_nonneg) hS0.le
  have hkeyR : ∀ n, ρ * μ.real (Z ∩ A n) ≤ μ.real (A n) := by
    intro n
    have hzS : μ.real (Z ∩ A n) ≤ S :=
      measureReal_mono (Set.inter_subset_inter_right _ ((hAsub n).trans (hBsubN n)))
    have hr := logisticShift_ratio hc.le (measureReal_nonneg (μ := μ) (s := Z ∩ A n)) hzS
    refine le_trans ?_ (hcomp n)
    rw [hρdef, div_mul_eq_mul_div, div_le_iff₀ hS0]
    linarith
  have hkey : ∀ n, ENNReal.ofReal ρ * μ (Z ∩ A n) ≤ μ (A n) := by
    intro n
    rw [← ofReal_measureReal (μ := μ) (s := Z ∩ A n), ← ofReal_measureReal (μ := μ) (s := A n),
      ← ENNReal.ofReal_mul hρ0]
    exact ENNReal.ofReal_le_ofReal (hkeyR n)
  have hsum : ENNReal.ofReal ρ * μ (Z ∩ N) ≤ μ N := by
    have h2 : μ (Z ∩ N) = ∑' n, μ (Z ∩ A n) := by
      rw [show Z ∩ N = ⋃ n, Z ∩ A n by rw [← Set.inter_iUnion, hAunion]]
      exact measure_iUnion
        (fun m n hmn => (hAdisj hmn).mono Set.inter_subset_right Set.inter_subset_right)
        fun n => hZm.inter (hAmeas n)
    have h3 : μ N = ∑' n, μ (A n) := by
      rw [← hAunion]; exact measure_iUnion hAdisj hAmeas
    rw [h2, h3, ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum hkey
  have hfin := ENNReal.toReal_mono (measure_ne_top μ N) hsum
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hρ0, ← measureReal_def, ← measureReal_def] at hfin
  calc logisticShift c S = ρ * S := by rw [hρdef, div_mul_cancel₀ _ hS0.ne']
    _ ≤ μ.real N := hfin

end Component

/-! ### `hcombinatorial`, with no side condition -/

section Partition

/-- **The one-dimensional isoperimetric inequality for an arbitrary measurable three-way
partition, deduced from its interval case.**

This is exactly the hypothesis `hcombinatorial` of
`Arlib.gaussianRestricted_isoperimetry`: same binders, same order, no extra hypothesis.  In
particular it covers the **interleaved** configurations that `Arlib.oneDim_partition_of_side`
must exclude, and which `Arlib.hside_not_implied` shows the remaining hypotheses do not rule
out.

Substituting `x = F t` for the normalised primitive `F = (∫_α^t D)/(∫_α^β D)` turns `hint`
together with `hcross` into the statement that `Z₁` and `Z₂` are separated by the Möbius map
`T c x = (1+c)x/(1+cx)`, and turns the goal into the logistic isoperimetric inequality
`Arlib.logistic_isoperimetry`.  Writing `w` for the mass of the open `T`-neighbourhood `N` of
`Z₁`, the three facts

  `T c (mass Z₁) ≤ w`,   `mass Z₂ ≤ 1 - w`,   `w - mass Z₁ ≤ mass Z₃`

(the second because `N` misses `Z₂`, the third because `N \ Z₁ ⊆ Z₃`) combine by pure algebra
into `c · mass Z₁ · mass Z₂ ≤ mass Z₃`. -/
theorem oneDim_partition (D : ℝ → ℝ) (Z₁ Z₂ Z₃ : Set ℝ) (κ : ℝ → ℝ → ℝ) (α β c : ℝ)
    (hαβ : α ≤ β) (hD0 : ∀ t ∈ Set.Icc α β, 0 ≤ D t)
    (hDint : IntervalIntegrable D volume α β)
    (hpart : IsPartition3 (Set.Icc α β) Z₁ Z₂ Z₃)
    (hmZ₁ : MeasurableSet Z₁) (hmZ₂ : MeasurableSet Z₂) (hmZ₃ : MeasurableSet Z₃)
    (hint : ∀ x y : ℝ, α ≤ x → x ≤ y → y ≤ β →
      κ x y * ((∫ t in α..x, D t) * ∫ t in y..β, D t)
        ≤ (∫ t in α..β, D t) * ∫ t in x..y, D t)
    (hcross : ∀ s ∈ Z₁, ∀ t ∈ Z₂, c ≤ κ (min s t) (max s t)) :
    c * ((∫ t in Z₁, D t) * ∫ t in Z₂, D t) ≤ (∫ t in α..β, D t) * ∫ t in Z₃, D t := by
  classical
  have hZ1sub : Z₁ ⊆ Set.Icc α β := hpart.subset₁
  have hZ2sub : Z₂ ⊆ Set.Icc α β := hpart.subset₂
  have hZ3sub : Z₃ ⊆ Set.Icc α β := hpart.subset₃
  have ha1nn : 0 ≤ ∫ t in Z₁, D t := setIntegral_nonneg hmZ₁ fun t ht => hD0 t (hZ1sub ht)
  have ha2nn : 0 ≤ ∫ t in Z₂, D t := setIntegral_nonneg hmZ₂ fun t ht => hD0 t (hZ2sub ht)
  have ha3nn : 0 ≤ ∫ t in Z₃, D t := setIntegral_nonneg hmZ₃ fun t ht => hD0 t (hZ3sub ht)
  have hMnn : 0 ≤ ∫ t in α..β, D t := intervalIntegral.integral_nonneg hαβ fun t ht => hD0 t ht
  have hRHS : 0 ≤ (∫ t in α..β, D t) * ∫ t in Z₃, D t := mul_nonneg hMnn ha3nn
  -- `c ≤ 0` is trivial
  rcases le_or_gt c 0 with hc | hc
  · exact le_trans (mul_nonpos_of_nonpos_of_nonneg hc (mul_nonneg ha1nn ha2nn)) hRHS
  -- the truncated weight and its primitive
  set Dc : ℝ → ℝ := (Set.Icc α β).indicator D with hDcdef
  have hDc0 : ∀ t, 0 ≤ Dc t := Set.indicator_nonneg (fun s hs => hD0 s hs)
  have hDcI : Integrable Dc :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hαβ).mp hDint)
  have hDceq : ∀ t ∈ Set.Icc α β, Dc t = D t := fun t ht => Set.indicator_of_mem ht D
  have hII : ∀ x y : ℝ, x ∈ Set.Icc α β → y ∈ Set.Icc α β →
      (∫ t in x..y, Dc t) = ∫ t in x..y, D t := fun x y hx hy =>
    intervalIntegral.integral_congr fun t ht => hDceq t (Set.uIcc_subset_Icc hx hy ht)
  have hSI : ∀ S : Set ℝ, MeasurableSet S → S ⊆ Set.Icc α β →
      (∫ t in S, Dc t) = ∫ t in S, D t := fun S hS hsub =>
    setIntegral_congr_fun hS fun t ht => hDceq t (hsub ht)
  set G : ℝ → ℝ := fun x => ∫ t in α..x, Dc t with hGdef
  have hGcont : Continuous G := hDcI.continuous_primitive α
  have hGsub : ∀ x y : ℝ, (∫ t in x..y, Dc t) = G y - G x := by
    intro x y
    have := intervalIntegral.integral_add_adjacent_intervals
      (a := α) (b := x) (c := y) (f := Dc) hDcI.intervalIntegrable hDcI.intervalIntegrable
    simp only [hGdef]
    linarith
  have hGmono : Monotone G := by
    intro x y hxy
    have h1 : (0 : ℝ) ≤ ∫ t in x..y, Dc t :=
      intervalIntegral.integral_nonneg hxy fun t _ => hDc0 t
    rw [hGsub] at h1; linarith
  have hGα : G α = 0 := by simp [hGdef]
  set M : ℝ := G β with hMdef
  have hMeq : M = ∫ t in α..β, D t := hII α β ⟨le_rfl, hαβ⟩ ⟨hαβ, le_rfl⟩
  -- `M = 0` is trivial
  rcases eq_or_lt_of_le (hMeq ▸ hMnn : (0 : ℝ) ≤ M) with hM | hM
  · have h1 : (∫ t in Z₁, D t) ≤ M := by
      rw [← hSI Z₁ hmZ₁ hZ1sub]
      have h2 := setIntegral_le_intervalIntegral hDcI hDc0 hαβ hZ1sub
      rw [hGsub, hGα, sub_zero] at h2
      exact h2
    have : (∫ t in Z₁, D t) = 0 := le_antisymm (by linarith) ha1nn
    rw [this]
    simpa using hRHS
  -- `G` is flat outside `[α,β]`
  have hGlow : ∀ t, t ≤ α → G t = 0 := by
    intro t ht
    have h1 : (∫ s in t..α, Dc s) = 0 := by
      rw [intervalIntegral.integral_of_le ht, hDcdef, setIntegral_indicator measurableSet_Icc]
      refine setIntegral_measure_zero _ ?_
      refine measure_mono_null (fun y hy => ?_) (Real.volume_singleton (a := α))
      exact le_antisymm hy.1.2 hy.2.1
    rw [hGsub, hGα] at h1
    linarith
  have hGhigh : ∀ t, β ≤ t → G t = M := by
    intro t ht
    have h1 : (∫ s in β..t, Dc s) = 0 := by
      rw [intervalIntegral.integral_of_le ht, hDcdef, setIntegral_indicator measurableSet_Icc]
      have he : Set.Ioc β t ∩ Set.Icc α β = ∅ :=
        Set.eq_empty_iff_forall_notMem.2 fun y hy => absurd hy.2.2 (not_le.2 hy.1.1)
      rw [he]
      simp
    rw [hGsub] at h1
    linarith [hMdef]
  have hGnn : ∀ t, 0 ≤ G t := by
    intro t
    rcases le_or_gt t α with h | h
    · rw [hGlow t h]
    · rw [← hGα]; exact hGmono h.le
  have hGle : ∀ t, G t ≤ M := by
    intro t
    rcases le_or_gt β t with h | h
    · rw [hGhigh t h]
    · rw [hMdef]; exact hGmono h.le
  -- the normalised primitive and the normalised weight
  set F : ℝ → ℝ := fun x => G x / M with hFdef
  have hFc : Continuous F := hGcont.div_const M
  have hFm : Monotone F := by
    intro x y hxy
    simp only [hFdef]
    have h := div_nonneg (sub_nonneg.2 (hGmono hxy)) hM.le
    rw [sub_div] at h
    linarith
  have hF0 : ∀ t, 0 ≤ F t := fun t => div_nonneg (hGnn t) hM.le
  have hF1 : ∀ t, F t ≤ 1 := fun t => (div_le_one hM).2 (hGle t)
  have hFα : F α = 0 := by simp [hFdef, hGα]
  have hFβ : F β = 1 := by simp [hFdef, ← hMdef, div_self hM.ne']
  set Dn : ℝ → ℝ := fun t => Dc t / M with hDndef
  have hDn0 : ∀ t, 0 ≤ Dn t := fun t => div_nonneg (hDc0 t) hM.le
  have hDnI : Integrable Dn := hDcI.div_const M
  set μ : Measure ℝ := volume.withDensity (fun t => ENNReal.ofReal (Dn t)) with hμdef
  have hμS : ∀ S : Set ℝ, MeasurableSet S → μ.real S = ∫ t in S, Dn t := by
    intro S hS
    rw [measureReal_def, hμdef, withDensity_apply _ hS,
      ← ofReal_integral_eq_lintegral_ofReal hDnI.restrict (Filter.Eventually.of_forall hDn0),
      ENNReal.toReal_ofReal (setIntegral_nonneg hS fun t _ => hDn0 t)]
  haveI : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    rw [hμdef, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hDnI (Filter.Eventually.of_forall hDn0)]
    exact ENNReal.ofReal_lt_top
  have hpt : ∀ x : ℝ, μ {x} = 0 := by
    intro x
    rw [hμdef, withDensity_apply _ (measurableSet_singleton x)]
    have hz : (volume : Measure ℝ).restrict {x} = 0 := by
      rw [Measure.restrict_eq_zero]; exact Real.volume_singleton
    rw [hz, lintegral_zero_measure]
  have hIoc : ∀ p q : ℝ, p ≤ q → μ.real (Set.Ioc p q) = F q - F p := by
    intro p q hpq
    rw [hμS _ measurableSet_Ioc, hDndef]
    simp only
    rw [integral_div, ← intervalIntegral.integral_of_le hpq, hGsub, hFdef]
    simp only
    ring
  -- the masses
  have hmass : ∀ S : Set ℝ, MeasurableSet S → S ⊆ Set.Icc α β →
      (∫ t in S, D t) = M * μ.real S := by
    intro S hS hsub
    rw [hμS S hS, hDndef]
    simp only
    rw [integral_div, hSI S hS hsub]
    field_simp
  have hunit : μ.real (Set.Icc α β) = 1 := by
    have h1 := hmass (Set.Icc α β) measurableSet_Icc subset_rfl
    have h2 : (∫ t in Set.Icc α β, D t) = M := by
      rw [← hSI _ measurableSet_Icc subset_rfl, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hαβ, hGsub, hGα, ← hMdef, sub_zero]
    rw [h2] at h1
    field_simp at h1
    linarith
  -- the neighbourhood
  set N : Set ℝ := sepNbhd c F Z₁ with hNdef
  have hNopen : IsOpen N := isOpen_sepNbhd hc.le hFc hF0 Z₁
  have hNsub : N ⊆ Set.Ioo α β := sepNbhd_subset_Ioo hc.le hFm hF0 hF1 hFα hFβ Z₁
  have hNmeas : MeasurableSet N := hNopen.measurableSet
  -- **separation**: `hint` and `hcross` say `T (F (min s t)) ≤ F (max s t)` on cross pairs
  have hsep : ∀ s ∈ Z₁, ∀ t ∈ Z₂, logisticShift c (F (min s t)) ≤ F (max s t) := by
    intro s hs t ht
    have hsI := hZ1sub hs
    have htI := hZ2sub ht
    have hxI : min s t ∈ Set.Icc α β := ⟨le_min hsI.1 htI.1, (min_le_left s t).trans hsI.2⟩
    have hyI : max s t ∈ Set.Icc α β := ⟨hsI.1.trans (le_max_left s t), max_le hsI.2 htI.2⟩
    have hxy : min s t ≤ max s t := min_le_max
    have hi := hint (min s t) (max s t) hxI.1 hxy hyI.2
    rw [← hII α _ ⟨le_rfl, hαβ⟩ hxI, ← hII _ β hyI ⟨hαβ, le_rfl⟩,
      ← hII α β ⟨le_rfl, hαβ⟩ ⟨hαβ, le_rfl⟩, ← hII _ _ hxI hyI] at hi
    simp only [hGsub, hGα, sub_zero, ← hMdef] at hi
    have hGx : 0 ≤ G (min s t) := hGnn _
    have hGy : G (max s t) ≤ M := hGle _
    have hprod : 0 ≤ G (min s t) * (M - G (max s t)) := mul_nonneg hGx (by linarith)
    have hκ := mul_le_mul_of_nonneg_right (hcross s hs t ht) hprod
    have hkey : c * (G (min s t) * (M - G (max s t))) ≤ M * (G (max s t) - G (min s t)) := by
      linarith
    rw [logisticShift, div_le_iff₀ (logisticShift_den_pos hc.le (hF0 _)), ← sub_nonneg]
    have expand : F (max s t) * (1 + c * F (min s t)) - (1 + c) * F (min s t)
        = (M * (G (max s t) - G (min s t)) - c * (G (min s t) * (M - G (max s t)))) / M ^ 2 := by
      simp only [hFdef]
      field_simp
      ring
    rw [expand]
    exact div_nonneg (by linarith) (by positivity)
  have hNZ2 : ∀ t ∈ Z₂, t ∉ N := by
    intro t ht htN
    obtain ⟨s, hs, h1, h2⟩ := htN
    have := hsep s hs t ht
    rcases le_total s t with h | h
    · rw [min_eq_left h, max_eq_right h] at this; linarith
    · rw [min_eq_right h, max_eq_left h] at this; linarith
  have hNZ3 : N \ Z₁ ⊆ Z₃ := by
    intro t ht
    have htI : t ∈ Set.Icc α β := Set.Ioo_subset_Icc_self (hNsub ht.1)
    rw [← hpart.union] at htI
    rcases htI with (h | h) | h
    · exact absurd h ht.2
    · exact absurd ht.1 (hNZ2 t h)
    · exact h
  -- the three mass relations
  have hw : logisticShift c (μ.real Z₁) ≤ μ.real N :=
    logistic_isoperimetry hc hFc hFm hF0 hF1 hFα hFβ hpt hIoc hmZ₁ hZ1sub
  have hθ₂ : μ.real Z₂ + μ.real N ≤ 1 := by
    have hdisj : Disjoint Z₂ N := Set.disjoint_left.2 fun t ht => hNZ2 t ht
    rw [← measureReal_union hdisj hNmeas, ← hunit]
    exact measureReal_mono (Set.union_subset hZ2sub (fun t ht => Set.Ioo_subset_Icc_self (hNsub ht)))
  have hθ₃ : μ.real N - μ.real Z₁ ≤ μ.real Z₃ := by
    have h1 : μ.real (N \ Z₁) ≤ μ.real Z₃ := measureReal_mono hNZ3
    have h2 : μ.real N ≤ μ.real (N \ Z₁) + μ.real Z₁ :=
      le_trans (measureReal_mono (Set.subset_diff_union N Z₁)) (measureReal_union_le _ _)
    linarith
  -- pure algebra
  have hθ₁0 : 0 ≤ μ.real Z₁ := measureReal_nonneg
  have hwexp : (1 + c) * μ.real Z₁ ≤ μ.real N * (1 + c * μ.real Z₁) := by
    rw [logisticShift, div_le_iff₀ (logisticShift_den_pos hc.le hθ₁0)] at hw
    linarith
  have hfinal : c * (μ.real Z₁ * μ.real Z₂) ≤ μ.real Z₃ := by
    have h1 : c * (μ.real Z₁ * μ.real Z₂) ≤ c * (μ.real Z₁ * (1 - μ.real N)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (by linarith) hθ₁0) hc.le
    nlinarith [hwexp, hθ₃]
  rw [hmass Z₁ hmZ₁ hZ1sub, hmass Z₂ hmZ₂ hZ2sub, hmass Z₃ hmZ₃ hZ3sub, ← hMeq]
  nlinarith [hfinal, hM, sq_nonneg M]

end Partition

end Arlib

/-! ### Axiom audit -/

#print axioms Arlib.mobius_key
#print axioms Arlib.logisticShift_ratio
#print axioms Arlib.isOpen_sepNbhd
#print axioms Arlib.sepNbhd_subset_Ioo
#print axioms Arlib.measureReal_Icc_le
#print axioms Arlib.le_measureReal_Ioo
#print axioms Arlib.connectedComponentIn_eq_or_disjoint
