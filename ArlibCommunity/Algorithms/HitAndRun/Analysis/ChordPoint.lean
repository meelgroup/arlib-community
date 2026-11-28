/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.TapeAlgorithm
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Kernel

/-!
# One chord: bisection, then rejection

Along a direction `θ` from a point `x` of a convex body `K`:

* **bisection** (`bisectVal_spec`): `Tape.bisect` makes no draws, so it has a value,
  `bisectVal`; started with `x` inside and `x + outer·θ` outside, after `k` halvings it
  returns an `outer` still outside, with a point inside within `(outer − inner)/2^k` of it;
* **the chord is bracketed** (`chordSet_subset`, `Icc_subset_chordSet`): the chord's
  parameter set lies in `(-lo, hi)` and contains `[-lo + w, hi - w]`, `w` the final gap;
* **rejection** (`chordPoint_le`, `le_chordPoint`): with acceptance probability `p` per
  try, the law of `r` capped tries is within `(1 − p)^r` of the uniform law on the chord,
  on every event.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ArlibCommunity.Algorithms.HitAndRun

open ArlibCommunity.Algorithms.HitAndRun.Model.Operations
open ArlibCommunity.Foundations.MarkovChainTheory (chordSet)
open TapeProgram

variable {n : ℕ}

/-! ## Bisection -/

/-- The value of `Tape.bisect`, which makes membership calls but no draws. -/
noncomputable def bisectVal (member : State n → Bool) (x θ : State n) :
    ℕ → ℝ → ℝ → ℝ
  | 0, _, outer => outer
  | k + 1, inner, outer =>
      if member (x + ((inner + outer) / 2) • θ) = true then
        bisectVal member x θ k ((inner + outer) / 2) outer
      else bisectVal member x θ k inner ((inner + outer) / 2)

/-- A program after a bisection has the law of the program after its value. -/
theorem law_bisect_bind {β : Type} [MeasurableSpace β] (member : State n → Bool)
    (x θ : State n) (F : ℝ → TapeProgram n β) :
    ∀ (k : ℕ) (inner outer : ℝ), law member ((Tape.bisect x θ k inner outer).bind F) =
      law member (F (bisectVal member x θ k inner outer))
  | 0, _, _ => rfl
  | k + 1, inner, outer => by
      show law member (((isMember (x + ((inner + outer) / 2) • θ)).bind fun inside =>
        if inside = true then Tape.bisect x θ k ((inner + outer) / 2) outer
        else Tape.bisect x θ k inner ((inner + outer) / 2)).bind F) = _
      rw [TapeProgram.bind_assoc]
      show law member ((if member (x + ((inner + outer) / 2) • θ) = true then
        Tape.bisect x θ k ((inner + outer) / 2) outer
        else Tape.bisect x θ k inner ((inner + outer) / 2)).bind F) = _
      rw [bisectVal]
      split
      · exact law_bisect_bind member x θ F k _ _
      · exact law_bisect_bind member x θ F k _ _

variable {K : Set (State n)} {member : State n → Bool}

/-- **Bisection keeps its invariant.**  Started with `x + inner·θ` inside, `x + outer·θ`
outside and `inner ≤ outer`, the value `h` has `x + h·θ` outside and `x + (h − w)·θ` inside,
where `w = (outer − inner)/2^k`, and `inner ≤ h − w`. -/
theorem bisectVal_spec (hmem : ∀ y, member y = true ↔ y ∈ K) (x θ : State n) :
    ∀ (k : ℕ) (inner outer : ℝ), x + inner • θ ∈ K → x + outer • θ ∉ K → inner ≤ outer →
      x + bisectVal member x θ k inner outer • θ ∉ K ∧
      x + (bisectVal member x θ k inner outer - (outer - inner) / 2 ^ k) • θ ∈ K ∧
      inner ≤ bisectVal member x θ k inner outer - (outer - inner) / 2 ^ k
  | 0, inner, outer, hin, hout, _ => by
      simp only [bisectVal, pow_zero, div_one, sub_sub_cancel]
      exact ⟨hout, hin, le_rfl⟩
  | k + 1, inner, outer, hin, hout, hle => by
      rw [bisectVal]
      split
      · rename_i hmid
        obtain ⟨h1, h2, h3⟩ := bisectVal_spec hmem x θ k _ outer ((hmem _).1 hmid) hout
          (by linarith)
        have hw : (outer - (inner + outer) / 2) / 2 ^ k = (outer - inner) / 2 ^ (k + 1) := by
          rw [pow_succ]; field_simp; ring
        rw [hw] at h2 h3
        exact ⟨h1, h2, by linarith⟩
      · rename_i hmid
        have hmid' : x + ((inner + outer) / 2) • θ ∉ K := fun h => hmid ((hmem _).2 h)
        obtain ⟨h1, h2, h3⟩ := bisectVal_spec hmem x θ k inner _ hin hmid' (by linarith)
        have hw : ((inner + outer) / 2 - inner) / 2 ^ k = (outer - inner) / 2 ^ (k + 1) := by
          rw [pow_succ]; field_simp; ring
        rw [hw] at h2 h3
        exact ⟨h1, h2, h3⟩

/-! ## The chord is bracketed -/

/-- If `x` is in a convex `K` and `x + h·θ` is not, the chord along `θ` stops before `h`. -/
theorem chordSet_lt (hKc : Convex ℝ K) {x θ : State n} (hx : x ∈ K) {h : ℝ}
    (hh : x + h • θ ∉ K) (h0 : 0 ≤ h) {t : ℝ} (ht : t ∈ chordSet K x θ) : t < h := by
  by_contra hlt
  push Not at hlt
  have hpos : 0 < t := lt_of_lt_of_le (lt_of_le_of_ne h0 fun h0' => hh (by
    rw [← h0', zero_smul, add_zero]; exact hx)) hlt
  have hmem : x + h • θ = (1 - h / t) • x + (h / t) • (x + t • θ) := by
    rw [smul_add, smul_smul, div_mul_cancel₀ _ hpos.ne', ← add_assoc, ← add_smul,
      sub_add_cancel, one_smul]
  exact hh (hmem ▸ hKc hx ht (by rw [sub_nonneg, div_le_one hpos]; exact hlt)
    (div_nonneg h0 hpos.le) (by ring))

/-- The chord's parameters along `-θ` are the negatives of those along `θ`. -/
theorem mem_chordSet_neg {x θ : State n} {t : ℝ} :
    t ∈ chordSet K x (-θ) ↔ -t ∈ chordSet K x θ := by
  simp only [ArlibCommunity.Foundations.MarkovChainTheory.mem_chordSet_iff, smul_neg,
    neg_smul]

/-- **The chord lies in the bracket** `(-lo, hi)`. -/
theorem chordSet_subset (hKc : Convex ℝ K) {x θ : State n} (hx : x ∈ K) {lo hi : ℝ}
    (hhi : x + hi • θ ∉ K) (hlo : x + lo • (-θ) ∉ K) (hhi0 : 0 ≤ hi) (hlo0 : 0 ≤ lo) :
    chordSet K x θ ⊆ Ioo (-lo) hi := by
  intro t ht
  refine ⟨?_, chordSet_lt hKc hx hhi hhi0 ht⟩
  have hneg : -t ∈ chordSet K x (-θ) := mem_chordSet_neg.2 (by rw [neg_neg]; exact ht)
  have := chordSet_lt hKc hx hlo hlo0 hneg
  linarith

/-- **The chord contains the inner points** `[-lo', hi']`. -/
theorem Icc_subset_chordSet (hKc : Convex ℝ K) {x θ : State n} {lo' hi' : ℝ}
    (hhi : x + hi' • θ ∈ K) (hlo : x + lo' • (-θ) ∈ K) :
    Icc (-lo') hi' ⊆ chordSet K x θ := by
  have hconv := ArlibCommunity.Foundations.MarkovChainTheory.convex_chordSet hKc x θ
  have h1 : -lo' ∈ chordSet K x θ := by
    rw [ArlibCommunity.Foundations.MarkovChainTheory.mem_chordSet_iff, neg_smul, ← smul_neg]
    exact hlo
  exact hconv.ordConnected.out h1 hhi

/-! ## Rejection -/

/-- A membership oracle for a measurable set is measurable. -/
theorem measurable_member (hK : MeasurableSet K) (hmem : ∀ y, member y = true ↔ y ∈ K) :
    Measurable member := by
  apply measurable_to_bool
  have : member ⁻¹' {true} = K := by ext y; simpa using hmem y
  rw [this]; exact hK

/-- **The bracket parameterisation.**  For `L = lo + hi > 0`, the uniform number `u` lands
on `x + (-lo + u·L)·θ ∈ E` with probability `vol({t ∈ [-lo, hi] | x + t·θ ∈ E}) / L`. -/
theorem uniformUnit_bracket (x θ : State n) {lo hi : ℝ} (hL : 0 < lo + hi)
    {E : Set (State n)} (hE : MeasurableSet E) :
    uniformUnit {u : ℝ | x + (-lo + u * (lo + hi)) • θ ∈ E} =
      ENNReal.ofReal (lo + hi)⁻¹ * volume ({t : ℝ | x + t • θ ∈ E} ∩ Icc (-lo) hi) := by
  have hT : MeasurableSet {t : ℝ | x + t • θ ∈ E} := hE.preimage (by fun_prop)
  have hset : {u : ℝ | x + (-lo + u * (lo + hi)) • θ ∈ E} ∩ Icc 0 1 =
      (fun u : ℝ => u * (lo + hi)) ⁻¹' ((fun s : ℝ => -lo + s) ⁻¹'
        ({t : ℝ | x + t • θ ∈ E} ∩ Icc (-lo) hi)) := by
    ext u
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Icc, mem_preimage]
    constructor
    · rintro ⟨h, h0, h1⟩
      exact ⟨h, by nlinarith, by nlinarith⟩
    · rintro ⟨h, h0, h1⟩
      refine ⟨h, ?_, ?_⟩
      · by_contra hu; push Not at hu; nlinarith
      · by_contra hu; push Not at hu; nlinarith
  rw [uniformUnit, Measure.restrict_apply (show MeasurableSet
      {u : ℝ | x + (-lo + u * (lo + hi)) • θ ∈ E} from hE.preimage (by fun_prop)), hset,
    Real.volume_preimage_mul_right hL.ne', measure_preimage_add,
    abs_of_pos (inv_pos.2 hL)]

variable (member) in
/-- The law of a try: the uniform number `u`, and the point `x + (-lo + u·L)·θ` if it is in
the body, else the remaining tries. -/
theorem law_chordPoint_succ (x θ : State n) (lo hi : ℝ) (r : ℕ) :
    law member (Tape.chordPoint x θ lo hi (r + 1)) =
      uniformUnit.bind fun u =>
        if member (x + (-lo + u * (lo + hi)) • θ) = true then
          Measure.dirac (x + (-lo + u * (lo + hi)) • θ)
        else law member (Tape.chordPoint x θ lo hi r) := by
  show uniformUnit.bind (fun u => law member
    (if member (x + (-lo + u * (lo + hi)) • θ) = true then
      TapeProgram.pure (x + (-lo + u * (lo + hi)) • θ)
     else Tape.chordPoint x θ lo hi r)) = _
  congr 1
  funext u
  split <;> rfl

/-- **One try, on an event `S`**: accepted inside `S`, or rejected and the remaining tries
land in `S`. -/
theorem law_chordPoint_succ_apply (hK : MeasurableSet K)
    (hmem : ∀ y, member y = true ↔ y ∈ K) (x θ : State n) (lo hi : ℝ) (r : ℕ)
    {S : Set (State n)} (hS : MeasurableSet S) :
    law member (Tape.chordPoint x θ lo hi (r + 1)) S =
      uniformUnit {u : ℝ | x + (-lo + u * (lo + hi)) • θ ∈ K ∩ S} +
        law member (Tape.chordPoint x θ lo hi r) S *
          uniformUnit {u : ℝ | x + (-lo + u * (lo + hi)) • θ ∉ K} := by
  set y : ℝ → State n := fun u => x + (-lo + u * (lo + hi)) • θ with hy
  have hym : Measurable y := by fun_prop
  have hmm := measurable_member hK hmem
  set c := law member (Tape.chordPoint x θ lo hi r) S
  have hA : MeasurableSet {u : ℝ | y u ∈ K} := hK.preimage hym
  have hAS : MeasurableSet {u : ℝ | y u ∈ K ∩ S} := (hK.inter hS).preimage hym
  have hκ : Measurable fun u => if member (y u) = true then Measure.dirac (y u)
      else law member (Tape.chordPoint x θ lo hi r) :=
    Measurable.ite (hmm.comp hym (measurableSet_singleton true))
      (Measure.measurable_dirac.comp hym) measurable_const
  rw [law_chordPoint_succ, Measure.bind_apply hS hκ.aemeasurable]
  have hfun : ∀ u, (if member (y u) = true then Measure.dirac (y u)
      else law member (Tape.chordPoint x θ lo hi r)) S =
      {u : ℝ | y u ∈ K ∩ S}.indicator 1 u + {u : ℝ | y u ∈ K}ᶜ.indicator (fun _ => c) u := by
    intro u
    by_cases hu : y u ∈ K
    · have hmu : member (y u) = true := (hmem _).2 hu
      by_cases hs : y u ∈ S
      · simp [hmu, Measure.dirac_apply' _ hS, hu, hs]
      · simp [hmu, Measure.dirac_apply' _ hS, hu, hs]
    · have hmu : ¬ member (y u) = true := fun h => hu ((hmem _).1 h)
      simp [hmu, hu, c]
  simp_rw [hfun]
  rw [lintegral_add_left (measurable_one.indicator hAS), lintegral_indicator_one hAS,
    lintegral_indicator_const hA.compl]
  rfl

/-- **The recursion's bounds.**  If `f (r + 1) = p·c + (1 − p)·f r` with `f 0, c ≤ 1`, then
`f r` is within `(1 − p)^r` of `c`. -/
theorem rec_bounds {p c : ℝ≥0∞} (hp : p ≤ 1) (hc : c ≤ 1) (f : ℕ → ℝ≥0∞) (hf0 : f 0 ≤ 1)
    (hrec : ∀ r, f (r + 1) = p * c + (1 - p) * f r) :
    ∀ r, f r ≤ c + (1 - p) ^ r ∧ c ≤ f r + (1 - p) ^ r
  | 0 => by
      simp only [pow_zero]
      exact ⟨hf0.trans le_add_self, hc.trans le_add_self⟩
  | r + 1 => by
      obtain ⟨h1, h2⟩ := rec_bounds hp hc f hf0 hrec r
      have hsum : p + (1 - p) = 1 := add_tsub_cancel_of_le hp
      have hc' : c = p * c + (1 - p) * c := by rw [← add_mul, hsum, one_mul]
      constructor
      · calc f (r + 1) = p * c + (1 - p) * f r := hrec r
          _ ≤ p * c + (1 - p) * (c + (1 - p) ^ r) := by gcongr
          _ = (p * c + (1 - p) * c) + (1 - p) * (1 - p) ^ r := by rw [mul_add, add_assoc]
          _ = c + (1 - p) ^ (r + 1) := by rw [← hc', pow_succ']
      · calc c = p * c + (1 - p) * c := hc'
          _ ≤ p * c + (1 - p) * (f r + (1 - p) ^ r) := by gcongr
          _ = (p * c + (1 - p) * f r) + (1 - p) * (1 - p) ^ r := by rw [mul_add, add_assoc]
          _ = f (r + 1) + (1 - p) ^ (r + 1) := by rw [← hrec r, pow_succ']

/-- **Capped rejection is close to uniform on the chord.**  With the chord bracketed in
`(-lo, hi)` and of positive length, `r` tries land on every event `S` within `(1 − p)^r` of
the uniform law on the chord, where `p = vol(chord)/(lo + hi)` is the acceptance
probability of one try. -/
theorem chordPoint_bounds (hK : MeasurableSet K) (hmem : ∀ y, member y = true ↔ y ∈ K)
    (x θ : State n) {lo hi : ℝ} (hL : 0 < lo + hi)
    (hbr : chordSet K x θ ⊆ Ioo (-lo) hi) (hC0 : volume (chordSet K x θ) ≠ 0)
    {S : Set (State n)} (hS : MeasurableSet S) (r : ℕ) :
    let p := ENNReal.ofReal (lo + hi)⁻¹ * volume (chordSet K x θ)
    let U := ArlibCommunity.Foundations.Convex.uniformOn (volume : Measure ℝ)
      (chordSet K x θ) {t : ℝ | x + t • θ ∈ S}
    law member (Tape.chordPoint x θ lo hi r) S ≤ U + (1 - p) ^ r ∧
      U ≤ law member (Tape.chordPoint x θ lo hi r) S + (1 - p) ^ r := by
  intro p U
  have hCm := ArlibCommunity.Foundations.MarkovChainTheory.measurableSet_chordSet hK x θ
  have hTm : MeasurableSet {t : ℝ | x + t • θ ∈ S} := hS.preimage (by fun_prop)
  have hCI : chordSet K x θ ∩ Icc (-lo) hi = chordSet K x θ :=
    inter_eq_left.2 (hbr.trans Ioo_subset_Icc_self)
  have hCfin : volume (chordSet K x θ) ≠ ⊤ :=
    ((measure_mono (hbr.trans Ioo_subset_Icc_self)).trans_lt (by simp)).ne
  have hp : uniformUnit {u : ℝ | x + (-lo + u * (lo + hi)) • θ ∈ K} = p := by
    rw [uniformUnit_bracket x θ hL hK]
    exact congrArg _ (congrArg volume hCI)
  have hp' : uniformUnit {u : ℝ | x + (-lo + u * (lo + hi)) • θ ∉ K} = 1 - p := by
    rw [← hp, ← prob_compl_eq_one_sub (show MeasurableSet
      {u : ℝ | x + (-lo + u * (lo + hi)) • θ ∈ K} from hK.preimage (by fun_prop))]
    rfl
  have hpS : uniformUnit {u : ℝ | x + (-lo + u * (lo + hi)) • θ ∈ K ∩ S} = p * U := by
    rw [uniformUnit_bracket x θ hL (hK.inter hS)]
    have hset : {t : ℝ | x + t • θ ∈ K ∩ S} ∩ Icc (-lo) hi =
        {t : ℝ | x + t • θ ∈ S} ∩ chordSet K x θ := by
      rw [← hCI]; ext t
      simp only [mem_inter_iff, mem_ofPred_eq,
        ArlibCommunity.Foundations.MarkovChainTheory.mem_chordSet_iff]
      tauto
    rw [hset]
    simp only [p, U, ArlibCommunity.Foundations.Convex.uniformOn_apply _ hCm hTm]
    rw [mul_assoc, ENNReal.mul_div_cancel hC0 hCfin]
  have hp1 : p ≤ 1 := by rw [← hp]; exact prob_le_one
  have hU1 : U ≤ 1 := by
    have := ArlibCommunity.Foundations.Convex.isProbabilityMeasure_uniformOn
      (volume : Measure ℝ) hC0 hCfin
    exact prob_le_one
  refine rec_bounds hp1 hU1 (fun r => law member (Tape.chordPoint x θ lo hi r) S) ?_ ?_ r
  · show Measure.dirac x S ≤ 1
    exact prob_le_one
  · intro r
    rw [law_chordPoint_succ_apply hK hmem x θ lo hi r hS, hpS, hp', mul_comm _ (1 - p)]

end ArlibCommunity.Algorithms.HitAndRun
