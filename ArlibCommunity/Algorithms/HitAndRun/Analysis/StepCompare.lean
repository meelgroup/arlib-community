/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.StepLaw
import ArlibCommunity.Algorithms.HitAndRun.Analysis.ShortChord

/-!
# One step of the sampler against one step of lazy hit-and-run

`stepKernel_compare`: from every point `x` and on every event `S`, one step of the sampler
and one step of the lazy hit-and-run kernel give `S` masses within

`β x = ½ · (1[x ∉ K_δ] + 2^{-r})`,

where `K_δ = shrunk K c δ` and `δ = 2D/2^k` is the bisection's final gap.  Off `K_δ` this is
the trivial `½`: both steps stay put with probability `½`.  On `K_δ` every chord is longer
than `2δ`, so the bisection brackets it within twice its length, each try is accepted with
probability at least `½`, and the `r` capped tries are within `2^{-r}` of the uniform law on
the chord in every direction (`chord_bounds_of_mem_shrunk`).
-/

set_option autoImplicit false

open MeasureTheory Set ProbabilityTheory Metric
open scoped ENNReal

namespace ArlibCommunity.Algorithms.HitAndRun

open ArlibCommunity.Algorithms.HitAndRun.Model.Operations
open ArlibCommunity.Foundations.MarkovChainTheory (chordSet unifSphere hitAndRun
  hitAndRunProposal)
open TapeProgram

variable {n : ℕ}

/-- The uniform law on the chord through `x` along `θ`, on the event `S`. -/
noncomputable def chordUniform (K : Set (State n)) (x θ : State n) (S : Set (State n)) :
    ℝ≥0∞ :=
  ArlibCommunity.Foundations.Convex.uniformOn (volume : Measure ℝ) (chordSet K x θ)
    {t : ℝ | x + t • θ ∈ S}

/-- `chordUniform` is measurable in the direction. -/
theorem measurable_chordUniform {K : Set (State n)} (hK : MeasurableSet K) (x : State n)
    {S : Set (State n)} (hS : MeasurableSet S) :
    Measurable fun θ : sphere (0 : State n) 1 => chordUniform K x θ S := by
  have h := Measurable.lintegral_prod_right' (ν := (volume : Measure ℝ))
    (ArlibCommunity.Foundations.MarkovChainTheory.measurable_polarIntegrand hK hS x)
  convert h using 1
  funext θ
  have hpre : MeasurableSet {t : ℝ | x + t • (θ : State n) ∈ S} := hS.preimage (by fun_prop)
  have hC := ArlibCommunity.Foundations.MarkovChainTheory.measurableSet_chordSet hK x
    (θ : State n)
  rw [chordUniform, ArlibCommunity.Foundations.Convex.uniformOn_apply _ hC hpre,
    ENNReal.div_eq_inv_mul]
  simp only [ArlibCommunity.Foundations.MarkovChainTheory.chordDensity]
  have hset : ∀ t : ℝ,
      S.indicator (1 : State n → ℝ≥0∞) (x + t • (θ : State n)) *
        ((volume (chordSet K x (θ : State n)))⁻¹ * K.indicator 1 (x + t • (θ : State n)))
      = (volume (chordSet K x (θ : State n)))⁻¹ *
          ({t : ℝ | x + t • (θ : State n) ∈ S} ∩ chordSet K x (θ : State n)).indicator 1 t := by
    intro t
    by_cases h1 : x + t • (θ : State n) ∈ S <;> by_cases h2 : x + t • (θ : State n) ∈ K <;>
      simp [h1, h2, chordSet, Set.mem_inter_iff]
  simp_rw [hset]
  rw [lintegral_const_mul _ (measurable_one.indicator (hpre.inter hC)),
    lintegral_indicator_one (hpre.inter hC)]

/-- The diameter bound is positive: the body contains a unit ball. -/
theorem diameter_pos [NeZero n] (p : Problem n) : 0 < p.diameter := by
  have hc : p.center ∈ p.body := p.unitBall_subset (mem_closedBall_self zero_le_one)
  set e : State n := EuclideanSpace.single 0 1
  have he : ‖e‖ = 1 := by simp [e]
  have hce : p.center + e ∈ p.body := p.unitBall_subset (by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, he])
  have hd := Metric.dist_le_diam_of_mem p.bounded_body hc hce
  rw [dist_eq_norm, sub_add_cancel_left, norm_neg, he] at hd
  linarith [p.diam_le]

/-- From a point of the body, a point at distance `2D` is outside it. -/
theorem add_two_diameter_notMem [NeZero n] (p : Problem n) {x θ : State n}
    (hx : x ∈ p.body) (hθ : ‖θ‖ = 1) : x + (2 * p.diameter) • θ ∉ p.body := by
  intro h
  have hd := Metric.dist_le_diam_of_mem p.bounded_body hx h
  rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, hθ, mul_one, Real.norm_eq_abs,
    abs_of_pos (by linarith [diameter_pos p])] at hd
  linarith [p.diam_le, diameter_pos p]

/-- **Along one direction from a point of the shrunk body, the capped chord sampling is
within `2^{-r}` of the uniform law on the chord.** -/
theorem chord_bounds_of_mem_shrunk [NeZero n] (p : Problem n) (oracle : MembershipOracle p)
    (w : WalkParams) (hD : w.D = p.diameter)
    (hw : 2 * w.D / 2 ^ w.bisectionSteps ≤ 1) {x θ : State n}
    (hx : x ∈ shrunk p.body p.center (2 * w.D / 2 ^ w.bisectionSteps)) (hθ : ‖θ‖ = 1)
    {S : Set (State n)} (hS : MeasurableSet S) :
    let lo := bisectVal oracle.query x (-θ) w.bisectionSteps 0 (2 * w.D)
    let hi := bisectVal oracle.query x θ w.bisectionSteps 0 (2 * w.D)
    law oracle.query (Tape.chordPoint x θ lo hi w.rejectionTries) S ≤
        chordUniform p.body x θ S + 2⁻¹ ^ w.rejectionTries ∧
      chordUniform p.body x θ S ≤
        law oracle.query (Tape.chordPoint x θ lo hi w.rejectionTries) S +
          2⁻¹ ^ w.rejectionTries := by
  intro lo hi
  set K := p.body
  set k := w.bisectionSteps
  set δ := 2 * w.D / 2 ^ k with hδ
  have hDpos : 0 < w.D := hD ▸ diameter_pos p
  have hδ0 : 0 < δ := by positivity
  have hxK : x ∈ p.body := shrunk_subset p.convex_body p.unitBall_subset hδ0.le hw hx
  have hθ' : ‖-θ‖ = 1 := by rw [norm_neg, hθ]
  have hout : x + (2 * w.D) • θ ∉ K := hD ▸ add_two_diameter_notMem p hxK hθ
  have hout' : x + (2 * w.D) • (-θ) ∉ K := hD ▸ add_two_diameter_notMem p hxK hθ'
  have hin : x + (0 : ℝ) • θ ∈ K := by rw [zero_smul, add_zero]; exact hxK
  have hin' : x + (0 : ℝ) • (-θ) ∈ K := by rw [zero_smul, add_zero]; exact hxK
  obtain ⟨hhi1, hhi2, hhi3⟩ := bisectVal_spec oracle.correct x θ k 0 (2 * w.D) hin hout
    (by positivity)
  obtain ⟨hlo1, hlo2, hlo3⟩ := bisectVal_spec oracle.correct x (-θ) k 0 (2 * w.D) hin' hout'
    (by positivity)
  simp only [sub_zero] at hhi2 hhi3 hlo2 hlo3
  -- `δ` is the final gap `(2D - 0) / 2^k`
  change x + (hi - δ) • θ ∈ K at hhi2
  change 0 ≤ hi - δ at hhi3
  change x + (lo - δ) • (-θ) ∈ K at hlo2
  change 0 ≤ lo - δ at hlo3
  have hbr : chordSet K x θ ⊆ Ioo (-lo) hi :=
    chordSet_subset p.convex_body hxK hhi1 hlo1 (by linarith) (by linarith)
  have hinner : Icc (-(lo - δ)) (hi - δ) ⊆ chordSet K x θ :=
    Icc_subset_chordSet p.convex_body hhi2 hlo2
  have hL : 0 < lo + hi := by linarith
  have hlong : ENNReal.ofReal (2 * δ) ≤ volume (chordSet K x θ) :=
    two_mul_le_volume_chordSet p.convex_body p.unitBall_subset hδ0 hw hx hθ
  have hinnerV : ENNReal.ofReal (lo + hi - 2 * δ) ≤ volume (chordSet K x θ) := by
    calc ENNReal.ofReal (lo + hi - 2 * δ) = volume (Icc (-(lo - δ)) (hi - δ)) := by
          rw [Real.volume_Icc]; ring_nf
      _ ≤ _ := measure_mono hinner
  have hhalfV : ENNReal.ofReal ((lo + hi) / 2) ≤ volume (chordSet K x θ) := by
    rcases le_total (lo + hi - 2 * δ) (2 * δ) with h | h
    · exact (ENNReal.ofReal_le_ofReal (by linarith)).trans hlong
    · exact (ENNReal.ofReal_le_ofReal (by linarith)).trans hinnerV
  have hC0 : volume (chordSet K x θ) ≠ 0 :=
    (lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by positivity)) hlong).ne'
  have hp : 2⁻¹ ≤ ENNReal.ofReal (lo + hi)⁻¹ * volume (chordSet K x θ) := by
    calc (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal (lo + hi)⁻¹ * ENNReal.ofReal ((lo + hi) / 2) := by
          have hh : (lo + hi)⁻¹ * ((lo + hi) / 2) = 2⁻¹ := by field_simp
          rw [← ENNReal.ofReal_mul (inv_nonneg.2 hL.le), hh, ENNReal.ofReal_inv_of_pos two_pos,
            ENNReal.ofReal_ofNat]
      _ ≤ _ := by gcongr
  have hq : (1 - ENNReal.ofReal (lo + hi)⁻¹ * volume (chordSet K x θ)) ^ w.rejectionTries ≤
      2⁻¹ ^ w.rejectionTries := by
    gcongr
    calc 1 - ENNReal.ofReal (lo + hi)⁻¹ * volume (chordSet K x θ) ≤ 1 - 2⁻¹ := by gcongr
      _ = 2⁻¹ := ENNReal.one_sub_inv_two
  obtain ⟨h1, h2⟩ := chordPoint_bounds p.measurable_body oracle.correct x θ hL hbr hC0 hS
    w.rejectionTries
  exact ⟨h1.trans (add_le_add le_rfl hq), h2.trans (add_le_add le_rfl hq)⟩

/-- **The gap of one step at `x`**: `½ · (1[x ∉ K_δ] + 2^{-r})`. -/
noncomputable def stepGap (p : Problem n) (w : WalkParams) (x : State n) : ℝ≥0∞ :=
  2⁻¹ * ((shrunk p.body p.center (2 * w.D / 2 ^ w.bisectionSteps))ᶜ.indicator 1 x +
    2⁻¹ ^ w.rejectionTries)

theorem measurable_stepGap (p : Problem n) (w : WalkParams)
    (hw : 2 * w.D / 2 ^ w.bisectionSteps < 1) : Measurable (stepGap p w) :=
  ((measurable_const.indicator (measurableSet_shrunk p.measurable_body hw).compl).add
    measurable_const).const_mul _

/-- **One step of the sampler against one step of lazy hit-and-run**, at every point and on
every event: within `stepGap p w x`. -/
theorem stepKernel_compare [NeZero n] (p : Problem n) (oracle : MembershipOracle p)
    (hm : Measurable oracle.query) (w : WalkParams) (hD : w.D = p.diameter)
    (hw : 2 * w.D / 2 ^ w.bisectionSteps ≤ 1) (x : State n) {S : Set (State n)}
    (hS : MeasurableSet S) :
    stepKernel w oracle.query hm x S ≤ lazyStep p.body x S + stepGap p w x ∧
      lazyStep p.body x S ≤ stepKernel w oracle.query hm x S + stepGap p w x := by
  set c : ℝ≥0∞ := 2⁻¹ ^ w.rejectionTries
  set d := Measure.dirac x S
  set Mv := ((standardGaussian n).bind fun g => law oracle.query (Tape.move w x g)) S
  set H := hitAndRun p.body x S
  have hQ : stepKernel w oracle.query hm x S = 2⁻¹ * d + 2⁻¹ * Mv := by
    rw [stepKernel_apply, law_step_apply w x hS]
  have hP : lazyStep p.body x S = 2⁻¹ * H + 2⁻¹ * d := by
    rw [lazyStep, ArlibCommunity.Foundations.MarkovChainTheory.lazy_apply_set _ _ hS,
      ← Measure.dirac_apply' x hS]
    rfl
  have hmove : ∀ g, IsProbabilityMeasure (law oracle.query (Tape.move w x g)) := fun g =>
    isProbabilityMeasure_law _ _ ((Tape.move_meas hm w).fst.comp
      (measurable_const.prodMk measurable_id : Measurable fun t : Tape n => ((x, g), t)))
  have hMvle : Mv ≤ 1 := by
    have hmeas : Measurable fun g => law oracle.query (Tape.move w x g) :=
      measurable_law _ (Tape.move w x) ((Tape.move_meas hm w).comp
        (φ := fun g : State n => (x, g)) (by fun_prop)).fst
    calc Mv = ∫⁻ g, law oracle.query (Tape.move w x g) S ∂(standardGaussian n) :=
          Measure.bind_apply hS hmeas.aemeasurable
      _ ≤ ∫⁻ _, 1 ∂(standardGaussian n) := lintegral_mono fun g => prob_le_one
      _ = 1 := by simp
  have hHle : H ≤ 1 := prob_le_one
  have hdle : d ≤ 1 := prob_le_one
  by_cases hx : x ∈ shrunk p.body p.center (2 * w.D / 2 ^ w.bisectionSteps)
  · have hgap : stepGap p w x = 2⁻¹ * c := by
      simp [stepGap, hx, c]
    rw [hgap, hQ, hP]
    have hδ0 : 0 < 2 * w.D / 2 ^ w.bisectionSteps := by
      have := diameter_pos p; rw [← hD] at this; positivity
    have hxK : x ∈ p.body := shrunk_subset p.convex_body p.unitBall_subset hδ0.le hw hx
    -- every unit direction's chord has positive finite length
    have hunif : ∀ θ : sphere (0 : State n) 1, chordUniform p.body x θ univ = 1 := by
      intro θ
      have hθ : ‖(θ : State n)‖ = 1 := by simp
      have hlong := two_mul_le_volume_chordSet p.convex_body p.unitBall_subset hδ0 hw hx hθ
      have h0 : volume (chordSet p.body x θ) ≠ 0 :=
        (lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by positivity)) hlong).ne'
      have htop : volume (chordSet p.body x θ) ≠ ⊤ := by
        obtain ⟨R, hR⟩ := p.bounded_body.subset_closedBall x
        refine ne_top_of_le_ne_top (by simp : volume (Icc (-R) R) ≠ ⊤) (measure_mono ?_)
        intro t ht
        have hd := hR ht
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, hθ, mul_one,
          Real.norm_eq_abs] at hd
        exact abs_le.1 hd
      have := ArlibCommunity.Foundations.Convex.isProbabilityMeasure_uniformOn
        (volume : Measure ℝ) h0 htop
      simp only [chordUniform, mem_univ, ofPred_true]
      exact measure_univ
    have hH : H = ∫⁻ θ, chordUniform p.body x θ S ∂(unifSphere n) := by
      have hprop1 : hitAndRunProposal p.body x univ = 1 := by
        rw [ArlibCommunity.Foundations.MarkovChainTheory.hitAndRunProposal_apply_uniformOn
          p.measurable_body x MeasurableSet.univ]
        refine (lintegral_congr fun θ => ?_).trans (by simp : ∫⁻ _ : sphere (0 : State n) 1,
          (1 : ℝ≥0∞) ∂(unifSphere n) = 1)
        exact hunif θ
      show hitAndRun p.body x S = _
      rw [ArlibCommunity.Foundations.MarkovChainTheory.hitAndRun_apply_set p.measurable_body
        x hS, hprop1, tsub_self, zero_mul, add_zero,
        ArlibCommunity.Foundations.MarkovChainTheory.hitAndRunProposal_apply_uniformOn
          p.measurable_body x hS]
      rfl
    have hdir : ∫⁻ g, chordUniform p.body x (‖g‖⁻¹ • g) S ∂(standardGaussian n) =
        ∫⁻ θ, chordUniform p.body x θ S ∂(unifSphere n) :=
      lintegral_direction (n := n) (F := fun θ => chordUniform p.body x θ S)
        (measurable_chordUniform p.measurable_body x hS)
    have h0 : ∀ᵐ g ∂(standardGaussian n), g ≠ 0 := by
      rw [ae_iff]; simpa using standardGaussian_zero
    have hbounds : ∀ᵐ g ∂(standardGaussian n),
        law oracle.query (moveChord oracle.query w x g) S ≤ chordUniform p.body x (‖g‖⁻¹ • g) S + c ∧
        chordUniform p.body x (‖g‖⁻¹ • g) S ≤ law oracle.query (moveChord oracle.query w x g) S + c := by
      filter_upwards [h0] with g hg
      have hθ : ‖‖g‖⁻¹ • g‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hg)]
      exact chord_bounds_of_mem_shrunk p oracle w hD hw hx hθ hS
    have hMv : Mv = ∫⁻ g, law oracle.query (moveChord oracle.query w x g) S ∂(standardGaussian n) :=
      law_move_apply hm w x hS
    have hup : Mv ≤ H + c := by
      rw [hMv, hH, ← hdir]
      calc ∫⁻ g, law oracle.query (moveChord oracle.query w x g) S ∂(standardGaussian n)
          ≤ ∫⁻ g, (chordUniform p.body x (‖g‖⁻¹ • g) S + c) ∂(standardGaussian n) :=
            lintegral_mono_ae (hbounds.mono fun g h => h.1)
        _ = ∫⁻ g, chordUniform p.body x (‖g‖⁻¹ • g) S ∂(standardGaussian n) + c := by
            rw [lintegral_add_right _ measurable_const]; simp
    have hdown : H ≤ Mv + c := by
      rw [hMv, hH, ← hdir]
      calc ∫⁻ g, chordUniform p.body x (‖g‖⁻¹ • g) S ∂(standardGaussian n)
          ≤ ∫⁻ g, (law oracle.query (moveChord oracle.query w x g) S + c) ∂(standardGaussian n) :=
            lintegral_mono_ae (hbounds.mono fun g h => h.2)
        _ = ∫⁻ g, law oracle.query (moveChord oracle.query w x g) S ∂(standardGaussian n) + c := by
            rw [lintegral_add_right _ measurable_const]; simp
    constructor
    · calc 2⁻¹ * d + 2⁻¹ * Mv ≤ 2⁻¹ * d + 2⁻¹ * (H + c) := by gcongr
        _ = 2⁻¹ * H + 2⁻¹ * d + 2⁻¹ * c := by ring
    · calc 2⁻¹ * H + 2⁻¹ * d ≤ 2⁻¹ * (Mv + c) + 2⁻¹ * d := by gcongr
        _ = 2⁻¹ * d + 2⁻¹ * Mv + 2⁻¹ * c := by ring
  · have hgap : stepGap p w x = 2⁻¹ * (1 + c) := by
      simp [stepGap, hx, c]
    rw [hgap, hQ, hP]
    constructor
    · calc 2⁻¹ * d + 2⁻¹ * Mv ≤ 0 + 2⁻¹ * d + 2⁻¹ * (1 + c) := by
            rw [zero_add]; gcongr; exact hMvle.trans le_self_add
        _ ≤ 2⁻¹ * H + 2⁻¹ * d + 2⁻¹ * (1 + c) := by gcongr; exact zero_le
    · calc 2⁻¹ * H + 2⁻¹ * d ≤ 2⁻¹ * (1 + c) + 2⁻¹ * d := by
            gcongr; exact hHle.trans le_self_add
        _ ≤ 2⁻¹ * d + 2⁻¹ * Mv + 2⁻¹ * (1 + c) := by
            rw [add_comm]; exact add_le_add le_self_add le_rfl

end ArlibCommunity.Algorithms.HitAndRun
