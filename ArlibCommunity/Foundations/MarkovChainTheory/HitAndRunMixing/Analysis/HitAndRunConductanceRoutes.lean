/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Foundations.Convex.CrossRatioIsoperimetry.Analysis.ChordContinuity
import ArlibCommunity.Foundations.Convex.CrossRatioIsoperimetry.Analysis.CrossRatioIsoBridge
import ArlibCommunity.Foundations.Convex.CrossRatioIsoperimetry.Analysis.IsoConcaveWeight
import ArlibCommunity.Foundations.Convex.Localization.Analysis.LocalizationLSC
import ArlibCommunity.Foundations.Convex.Localization.Analysis.LocalizationMeasurable
import ArlibCommunity.Foundations.Convex.Localization.Analysis.LocalizationNeedleInBody
import ArlibCommunity.Foundations.Convex.CrossRatioIsoperimetry.Analysis.LovaszVempalaIso
import ArlibCommunity.Foundations.Convex.CrossRatioIsoperimetry.Analysis.WeightedIsoBook
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Analysis.HitAndRunConductance

/-!
# Routes to the hit-and-run conductance bound

Lovász–Vempala's conductance bound for hit-and-run (their Theorem 4.2), reached from the
isoperimetric results of convex geometry in several ways: through the Localization Lemma,
through the cross-ratio isoperimetry (Theorem 2.1), through Lee's weighted form, and through
the lower-semicontinuous weight.  These applications used to sit in the geometry files whose
results they consume; they live here so that convex geometry does not depend on the Markov
chain.
-/

open ArlibCommunity.Foundations.Convex ArlibCommunity.Foundations.MarkovChainTheory

open ArlibCommunity.Foundations.Convex ArlibCommunity.Foundations.MarkovChainTheory

namespace ArlibCommunity.Foundations.MarkovChainTheory

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped ENNReal _root_.Topology

variable {n : ℕ}

/-- **Theorem 4.2 of Lovász–Vempala with `hIso` restricted to lower semicontinuous weights.**

`ArlibCommunity.Foundations.MarkovChainTheory.conductance_hitAndRun_ge_of_tv` replayed with its `hIso` binder replaced by
`ArlibCommunity.Foundations.Convex.hIso_lowerSemicontinuous`'s conclusion — the same binder with `LowerSemicontinuous h`
inserted after the two set arguments, every other clause verbatim.

The replay is forced by the one-agent-per-file discipline, and it changes exactly one step.  The
paper applies `hIso` at `g x = stepRadius K (63/64) x / (48·D·√n)`, which
`ArlibCommunity.Foundations.MarkovChainTheory.stepRadius_concaveOn` makes concave on `K` and hence
(`ArlibCommunity.Foundations.MarkovChainTheory.continuousOn_stepRadius`) continuous only on `interior K` — a concave function on a closed
body may jump at the boundary, so `Continuous g` is not available.  What is available is
`1_{interior K} · g`, which is

* **lower semicontinuous** (`ArlibCommunity.Foundations.Convex.lowerSemicontinuous_indicator_of_continuousOn`),
* below `g` pointwise, so `g ≤ 1/3` and the chord bound are inherited unchanged, and
* equal to `g` almost everywhere for `uniformOn volume K`, the frontier of a convex body being
  null — so Lemma 3.4's average bound survives verbatim.

That is the whole difference; every other line is the original.

**The `hLem41` binder is demanded only on `interior K`.**  That is where the proof applies it
(`S₁`, `S₂` are cut down to the interior), and it is the only form that is *satisfiable*: for
`u ∈ K \ interior K` and `v ∈ interior K` one has `chordLow K u v = 0`
(`ArlibCommunity.Foundations.MarkovChainTheory.chordLow_eq_zero_of_notMem_interior`), so the side condition
`chordLow K u v < 0` of the paper's Lemma 4.1 fails at every boundary pair and the `∀ u ∈ K`
form cannot be discharged.  On the interior it is proved outright, at `1 − 1/8000` for
`n ≥ 1100`, by `ArlibCommunity.Foundations.MarkovChainTheory.hLem41_interior_uncond`.  The unchanged
`conductance_hitAndRun_ge_of_tv_lsc` below is derived from this theorem by `interior_subset`,
which is the machine-checked proof that the weakening loses no consumer. -/
theorem conductance_hitAndRun_ge_of_tv_lsc_interior (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hLem41 : ∀ u ∈ interior K, ∀ v ∈ interior K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      ArlibCommunity.Foundations.Convex.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - lam)))
    (hIso : ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))), LowerSemicontinuous h → (∀ x, 0 ≤ h x) →
      (∀ x ∈ K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (crossRatioDist K u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(uniformOn volume K)) *
          min (uniformOn volume K T₁) (uniformOn volume K T₂)
        ≤ uniformOn volume K ((K \ T₁) \ T₂)) :
    ENNReal.ofReal (lam / (245760 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) := by
  have hn' : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  haveI : NeZero n := ⟨hn'⟩
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnR0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR0
  have hsqsq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt (by positivity)
  obtain ⟨R, hR⟩ := hKb.subset_closedBall (0 : EuclideanSpace ℝ (Fin n))
  have hKtop : volume K ≠ ⊤ :=
    ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono hR)
  have hK0 : volume K ≠ 0 :=
    (lt_of_lt_of_le (measure_closedBall_pos volume z one_pos) (measure_mono hball)).ne'
  have hD1 : (1 : ℝ) ≤ D := le_trans (one_le_diam_of_unitBall hn hKb hball) hD
  have hD0 : (0 : ℝ) < D := by linarith
  have hnD : (0 : ℝ) < (n : ℝ) * D := by positivity
  have hnD1 : (1 : ℝ) ≤ (n : ℝ) * D := by nlinarith
  haveI : IsProbabilityMeasure (uniformOn volume K) :=
    isProbabilityMeasure_uniformOn volume hK0 hKtop
  set pi : Measure (EuclideanSpace ℝ (Fin n)) := uniformOn volume K with hpidef
  set P : Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) := hitAndRun K with hPdef
  have hrev : IsReversible P pi := isReversible_hitAndRun hKm
  have hIm : MeasurableSet (interior K) := isOpen_interior.measurableSet
  -- the frontier is null, so `interior K` carries all the mass
  have hintc : pi (interior K)ᶜ = 0 := by
    have hsub : (interior K)ᶜ ⊆ Kᶜ ∪ frontier K := by
      intro x hx
      by_cases hxK : x ∈ K
      · exact Or.inr (by rw [hKcl.frontier_eq]; exact ⟨hxK, hx⟩)
      · exact Or.inl hxK
    refine nonpos_iff_eq_zero.mp ?_
    calc pi (interior K)ᶜ ≤ pi (Kᶜ ∪ frontier K) := measure_mono hsub
      _ ≤ pi Kᶜ + pi (frontier K) := measure_union_le _ _
      _ = 0 := by
          rw [hpidef, uniformOn_compl_eq_zero volume hKm,
            uniformOn_absolutelyContinuous volume K (hKc.addHaar_frontier volume), add_zero]
  -- the walk leaves every interior point with probability one
  have hmove : ∀ x ∈ interior K, hitAndRunProposal K x Set.univ = 1 := by
    intro x hx
    obtain ⟨ε, hε, hbx⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
    exact hitAndRunProposal_univ_eq_one_of_mem_interior hKm hε (hbx.trans interior_subset) hR
  -- the weight function `h(x) = s(x)/(48·D·√n)` of §4
  set g : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => stepRadius K (63 / 64) x / (48 * D * Real.sqrt n) with hgdef
  have hgapp : ∀ x, g x = stepRadius K (63 / 64) x / (48 * D * Real.sqrt n) := fun _ => rfl
  have hcpos : (0 : ℝ) < 48 * D * Real.sqrt n := by positivity
  have hgnn : ∀ x, 0 ≤ g x := fun x =>
    div_nonneg (stepRadius_nonneg hn' hKtop (by norm_num) x) hcpos.le
  -- Lemma 3.4 gives the average weight
  have hconst : 1 / (48 * D * Real.sqrt n) * ((1 - 63 / 64) / (10 * Real.sqrt n))
      = 1 / (30720 * (n : ℝ) * D) := by
    rw [show (1 : ℝ) - 63 / 64 = 1 / 64 by norm_num, div_mul_div_comm, one_mul, div_div]
    congr 1
    linear_combination (30720 * D) * hsqsq
  have hL34 : ENNReal.ofReal ((1 - 63 / 64) / (10 * Real.sqrt n)) * volume K
      ≤ ∫⁻ x in K, ENNReal.ofReal (stepRadius K (63 / 64) x) :=
    lintegral_stepRadius_ge hn' hKc hKcl hKm hKtop (by norm_num) (by norm_num) hball
  have hpiint : (∫⁻ x, ENNReal.ofReal (g x) ∂pi)
      = ENNReal.ofReal (1 / (48 * D * Real.sqrt n)) *
          ((volume K)⁻¹ * ∫⁻ x in K, ENNReal.ofReal (stepRadius K (63 / 64) x)) := by
    have hrw : ∀ x, ENNReal.ofReal (g x)
        = ENNReal.ofReal (1 / (48 * D * Real.sqrt n))
            * ENNReal.ofReal (stepRadius K (63 / 64) x) := by
      intro x
      rw [hgapp x, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    simp only [hrw]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    rw [hpidef, uniformOn_def, lintegral_smul_measure, smul_eq_mul]
  have hinv : ENNReal.ofReal ((1 - 63 / 64) / (10 * Real.sqrt n))
      ≤ (volume K)⁻¹ * ∫⁻ x in K, ENNReal.ofReal (stepRadius K (63 / 64) x) := by
    have hcancel : (volume K)⁻¹ * (ENNReal.ofReal ((1 - 63 / 64) / (10 * Real.sqrt n)) * volume K)
        = ENNReal.ofReal ((1 - 63 / 64) / (10 * Real.sqrt n)) := by
      rw [show (volume K)⁻¹ * (ENNReal.ofReal ((1 - 63 / 64) / (10 * Real.sqrt n)) * volume K)
            = ENNReal.ofReal ((1 - 63 / 64) / (10 * Real.sqrt n)) * (volume K * (volume K)⁻¹) from
          by ring, ENNReal.mul_inv_cancel hK0 hKtop, mul_one]
    calc ENNReal.ofReal ((1 - 63 / 64) / (10 * Real.sqrt n))
        = (volume K)⁻¹ * (ENNReal.ofReal ((1 - 63 / 64) / (10 * Real.sqrt n)) * volume K) :=
          hcancel.symm
      _ ≤ _ := by gcongr
  have hint : ENNReal.ofReal (1 / (30720 * (n : ℝ) * D))
      ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂pi := by
    rw [hpiint, ← hconst, ENNReal.ofReal_mul (by positivity)]
    gcongr
  -- now the conductance
  refine le_conductance P pi fun S hSm hSpos hShalf => ?_
  have hpitop : pi S ≠ ⊤ := measure_ne_top _ _
  have hcompl : pi S + pi Sᶜ = 1 := by rw [measure_add_measure_compl hSm, measure_univ]
  have hSc : (1 : ℝ≥0∞) / 2 ≤ pi Sᶜ := by
    have h1 : (1 : ℝ≥0∞) / 2 + 1 / 2 ≤ 1 / 2 + pi Sᶜ := by
      calc (1 : ℝ≥0∞) / 2 + 1 / 2 = 1 := ENNReal.add_halves 1
        _ = pi S + pi Sᶜ := hcompl.symm
        _ ≤ 1 / 2 + pi Sᶜ := by gcongr
    exact (ENNReal.add_le_add_iff_left (by simp)).1 h1
  set eps : ℝ≥0∞ := ENNReal.ofReal (lam / 2) with hepsdef
  set S1 : Set (EuclideanSpace ℝ (Fin n)) :=
    (S ∩ interior K) ∩ {x | P x Sᶜ < eps} with hS1def
  set S2 : Set (EuclideanSpace ℝ (Fin n)) :=
    (interior K \ S) ∩ {x | P x S < eps} with hS2def
  have hS1m : MeasurableSet S1 :=
    (hSm.inter hIm).inter (measurableSet_lt (Kernel.measurable_coe P hSm.compl) measurable_const)
  have hS2m : MeasurableSet S2 :=
    (hIm.diff hSm).inter (measurableSet_lt (Kernel.measurable_coe P hSm) measurable_const)
  have hmem1 : ∀ x, x ∈ S1 ↔ ((x ∈ S ∧ x ∈ interior K) ∧ P x Sᶜ < eps) := by
    intro x; rw [hS1def]; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  have hmem2 : ∀ x, x ∈ S2 ↔ ((x ∈ interior K ∧ x ∉ S) ∧ P x S < eps) := by
    intro x; rw [hS2def]; simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_setOf_eq]
  have hS1int : ∀ x ∈ S1, x ∈ interior K := fun x hx => ((hmem1 x).1 hx).1.2
  have hS2int : ∀ x ∈ S2, x ∈ interior K := fun x hx => ((hmem2 x).1 hx).1.1
  have hS1K : S1 ⊆ K := fun x hx => interior_subset (hS1int x hx)
  have hS2K : S2 ⊆ K := fun x hx => interior_subset (hS2int x hx)
  have hdisj : Disjoint S1 S2 :=
    Set.disjoint_left.mpr fun x hx1 hx2 => ((hmem2 x).1 hx2).1.2 ((hmem1 x).1 hx1).1.1
  -- the failure of Lemma 4.1 at a pair of deep points
  have hdich : ∀ u ∈ S1, ∀ v ∈ S2,
      1 / 8 ≤ crossRatioDist K u v ∨
        (medianStep K u ≤ Real.sqrt n / 2 * dist u v ∧
          medianStep K v ≤ Real.sqrt n / 2 * dist u v) := by
    intro u hu v hv
    rcases le_or_gt (1 / 8 : ℝ) (crossRatioDist K u v) with h8 | h8
    · exact Or.inl h8
    refine Or.inr ?_
    have hsep : ¬ dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) := by
      intro hlt
      have htv := hLem41 u (hS1int u hu) v (hS2int v hv) h8 hlt
      have hu' : P u Sᶜ < eps := ((hmem1 u).1 hu).2
      have hv' : P v S < eps := ((hmem2 v).1 hv).2
      have h1 : P u S ≤ P v S + ENNReal.ofReal (1 - lam) := (htv S hSm).1
      have hA : P u S < ENNReal.ofReal (lam / 2 + (1 - lam)) := by
        calc P u S ≤ P v S + ENNReal.ofReal (1 - lam) := h1
          _ < eps + ENNReal.ofReal (1 - lam) :=
              ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hv'
          _ = ENNReal.ofReal (lam / 2 + (1 - lam)) := by
              rw [hepsdef, ← ENNReal.ofReal_add (by linarith) (by linarith)]
      have hsum : P u S + P u Sᶜ < 1 := by
        calc P u S + P u Sᶜ < ENNReal.ofReal (lam / 2 + (1 - lam)) + P u Sᶜ :=
              ENNReal.add_lt_add_right (measure_ne_top _ _) hA
          _ < ENNReal.ofReal (lam / 2 + (1 - lam)) + eps :=
              ENNReal.add_lt_add_left ENNReal.ofReal_ne_top hu'
          _ = 1 := by
              rw [hepsdef, ← ENNReal.ofReal_add (by linarith) (by linarith),
                show lam / 2 + (1 - lam) + lam / 2 = 1 by ring, ENNReal.ofReal_one]
      rw [measure_add_measure_compl hSm, measure_univ] at hsum
      exact lt_irrefl _ hsum
    rw [not_lt] at hsep
    have hcpos2 : (0 : ℝ) < Real.sqrt n / 2 := by positivity
    have hid : Real.sqrt n / 2 * (2 / Real.sqrt n) = 1 := by field_simp
    have hmax : max (medianStep K u) (medianStep K v) ≤ Real.sqrt n / 2 * dist u v := by
      calc max (medianStep K u) (medianStep K v)
          = Real.sqrt n / 2 * (2 / Real.sqrt n * max (medianStep K u) (medianStep K v)) := by
            rw [← mul_assoc, hid, one_mul]
        _ ≤ Real.sqrt n / 2 * dist u v := mul_le_mul_of_nonneg_left hsep hcpos2.le
    exact ⟨le_trans (le_max_left _ _) hmax, le_trans (le_max_right _ _) hmax⟩
  -- Theorem 2.1's hypothesis, verified
  have hcond : ∀ u ∈ S1, ∀ v ∈ S2, ∀ x ∈ K,
      (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
      g x ≤ min 1 (crossRatioDist K u v) / 3 := by
    rintro u hu v hv x hxK ⟨t, hxt⟩
    have huv : u ≠ v := by
      intro h
      exact ((hmem2 v).1 hv).1.2 (h ▸ ((hmem1 u).1 hu).1.1)
    rw [hgapp x]
    exact weight_le_of_chord hn' hKc hKcl hKm hKb hKtop (by norm_num) (by norm_num) hD hD0
      (hS1int u hu) (hS2int v hv) huv (hmove u (hS1int u hu)) (hmove v (hS2int v hv))
      (hdich u hu v hv) hxK hxt
  -- the global bound `h ≤ 1/3` of Theorem 2.1, which the paper calls clear and which is
  -- *not* a consequence of the chord bound (`ArlibCommunity.Foundations.not_hIso_two`)
  have hg13 : ∀ x ∈ K, g x ≤ 1 / 3 := by
    intro x hx
    rw [hgapp x]
    exact weight_le_third hn' hKb (by norm_num) hD hD0 hx
  -- `hIso` is available only for a lower semicontinuous weight, and `g` — being concave on `K`
  -- (`ArlibCommunity.Foundations.MarkovChainTheory.stepRadius_concaveOn`) — is continuous only on `interior K`.  Cutting `g` down to the
  -- interior repairs that: the cut weight is lower semicontinuous
  -- (`ArlibCommunity.Foundations.Convex.lowerSemicontinuous_indicator_of_continuousOn`), it lies below `g` so every upper
  -- bound is inherited, and the frontier of a convex body is null so the average is unchanged.
  have hgcont : ContinuousOn g (interior K) := by
    have hs := ArlibCommunity.Foundations.MarkovChainTheory.continuousOn_stepRadius hn' hKc hKm hKtop (show (0:ℝ) < 63 / 64 by norm_num)
    exact hs.div_const _
  have hg'nn : ∀ x, 0 ≤ (interior K).indicator g x := fun x =>
    Set.indicator_nonneg (fun y _ => hgnn y) x
  have hg'le : ∀ x, (interior K).indicator g x ≤ g x := by
    intro x
    by_cases hx : x ∈ interior K
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]; exact hgnn x
  have hg'lsc : LowerSemicontinuous ((interior K).indicator g) :=
    ArlibCommunity.Foundations.Convex.lowerSemicontinuous_indicator_of_continuousOn isOpen_interior hgcont
      (fun x _ => hgnn x)
  have hg'13 : ∀ x ∈ K, (interior K).indicator g x ≤ 1 / 3 := fun x hx =>
    le_trans (hg'le x) (hg13 x hx)
  have hg'cond : ∀ u ∈ S1, ∀ v ∈ S2, ∀ x ∈ K,
      (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
      (interior K).indicator g x ≤ min 1 (crossRatioDist K u v) / 3 := fun u hu v hv x hx hex =>
    le_trans (hg'le x) (hcond u hu v hv x hx hex)
  have hae : ∀ᵐ x ∂pi, x ∈ interior K := by
    rw [MeasureTheory.ae_iff]
    exact hintc
  have hint' : ENNReal.ofReal (1 / (30720 * (n : ℝ) * D))
      ≤ ∫⁻ x, ENNReal.ofReal ((interior K).indicator g x) ∂pi := by
    refine le_trans hint (le_of_eq (lintegral_congr_ae ?_))
    filter_upwards [hae] with x hx
    rw [Set.indicator_of_mem hx]
  have hisoS := hIso _ S1 S2 hg'lsc hg'nn hg'13 hS1m hS2m hS1K hS2K hdisj hg'cond
  have hiso2 : ENNReal.ofReal (1 / (30720 * (n : ℝ) * D)) * min (pi S1) (pi S2)
      ≤ pi ((K \ S1) \ S2) := by
    refine le_trans ?_ hisoS
    exact mul_le_mul' hint' le_rfl
  -- the three-way partition and the flow accounting
  have hSA : S \ (S1 ∪ (interior K)ᶜ) = (S ∩ interior K) \ S1 := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff]
    tauto
  have hSB : Sᶜ \ (S2 ∪ (interior K)ᶜ) = (interior K \ S) \ S2 := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_compl_iff]
    tauto
  have hA' : ∀ x ∈ S \ (S1 ∪ (interior K)ᶜ), eps ≤ 1 * P x Sᶜ := by
    rw [hSA]
    rintro x ⟨⟨hxS, hxK⟩, hxS1⟩
    rw [one_mul]
    by_contra hc
    exact hxS1 ((hmem1 x).2 ⟨⟨hxS, hxK⟩, not_le.1 hc⟩)
  have hB' : ∀ x ∈ Sᶜ \ (S2 ∪ (interior K)ᶜ), eps ≤ 1 * P x S := by
    rw [hSB]
    rintro x ⟨⟨hxK, hxS⟩, hxS2⟩
    rw [one_mul]
    by_contra hc
    exact hxS2 ((hmem2 x).2 ⟨⟨hxK, hxS⟩, not_le.1 hc⟩)
  have hflow : eps * (pi ((S ∩ interior K) \ S1) + pi ((interior K \ S) \ S2))
      ≤ 2 * (1 * flow P pi S Sᶜ) := by
    have h := mul_measure_add_measure_le_mul_flow P pi hrev hSm (hS1m.union hIm.compl)
      (hS2m.union hIm.compl) hA' hB'
    rwa [hSA, hSB] at h
  have hflow' : eps * (pi ((S ∩ interior K) \ S1) + pi ((interior K \ S) \ S2))
      ≤ 2 * flow P pi S Sᶜ := by rwa [one_mul] at hflow
  have hpart : pi ((K \ S1) \ S2)
      ≤ pi ((S ∩ interior K) \ S1) + pi ((interior K \ S) \ S2) := by
    have hsub : (K \ S1) \ S2 ⊆ (((S ∩ interior K) \ S1) ∪ ((interior K \ S) \ S2))
        ∪ (interior K)ᶜ := by
      rintro x ⟨⟨hxK, hxS1⟩, hxS2⟩
      by_cases hxI : x ∈ interior K
      · by_cases hxS : x ∈ S
        · exact Or.inl (Or.inl ⟨⟨hxS, hxI⟩, hxS1⟩)
        · exact Or.inl (Or.inr ⟨⟨hxI, hxS⟩, hxS2⟩)
      · exact Or.inr hxI
    calc pi ((K \ S1) \ S2)
        ≤ pi ((((S ∩ interior K) \ S1) ∪ ((interior K \ S) \ S2)) ∪ (interior K)ᶜ) :=
          measure_mono hsub
      _ ≤ pi (((S ∩ interior K) \ S1) ∪ ((interior K \ S) \ S2)) + pi (interior K)ᶜ :=
          measure_union_le _ _
      _ ≤ pi ((S ∩ interior K) \ S1) + pi ((interior K \ S) \ S2) + pi (interior K)ᶜ := by
          gcongr
          exact measure_union_le _ _
      _ = pi ((S ∩ interior K) \ S1) + pi ((interior K \ S) \ S2) := by rw [hintc, add_zero]
  have hcov1 : pi S ≤ pi ((S ∩ interior K) \ S1) + pi S1 := by
    have hsub : S ⊆ (((S ∩ interior K) \ S1) ∪ S1) ∪ (interior K)ᶜ := by
      intro x hx
      by_cases hxI : x ∈ interior K
      · by_cases hxS1 : x ∈ S1
        · exact Or.inl (Or.inr hxS1)
        · exact Or.inl (Or.inl ⟨⟨hx, hxI⟩, hxS1⟩)
      · exact Or.inr hxI
    calc pi S ≤ pi ((((S ∩ interior K) \ S1) ∪ S1) ∪ (interior K)ᶜ) := measure_mono hsub
      _ ≤ pi (((S ∩ interior K) \ S1) ∪ S1) + pi (interior K)ᶜ := measure_union_le _ _
      _ ≤ pi ((S ∩ interior K) \ S1) + pi S1 + pi (interior K)ᶜ := by
          gcongr
          exact measure_union_le _ _
      _ = pi ((S ∩ interior K) \ S1) + pi S1 := by rw [hintc, add_zero]
  have hcov2 : pi Sᶜ ≤ pi ((interior K \ S) \ S2) + pi S2 := by
    have hsub : Sᶜ ⊆ (((interior K \ S) \ S2) ∪ S2) ∪ (interior K)ᶜ := by
      intro x hx
      by_cases hxI : x ∈ interior K
      · by_cases hxS2 : x ∈ S2
        · exact Or.inl (Or.inr hxS2)
        · exact Or.inl (Or.inl ⟨⟨hxI, hx⟩, hxS2⟩)
      · exact Or.inr hxI
    calc pi Sᶜ ≤ pi ((((interior K \ S) \ S2) ∪ S2) ∪ (interior K)ᶜ) := measure_mono hsub
      _ ≤ pi (((interior K \ S) \ S2) ∪ S2) + pi (interior K)ᶜ := measure_union_le _ _
      _ ≤ pi ((interior K \ S) \ S2) + pi S2 + pi (interior K)ᶜ := by
          gcongr
          exact measure_union_le _ _
      _ = pi ((interior K \ S) \ S2) + pi S2 := by rw [hintc, add_zero]
  -- the arithmetic of the final constant
  have h4c : (4 : ℝ≥0∞) * ENNReal.ofReal (lam / (245760 * (n : ℝ) * D))
      = ENNReal.ofReal (4 * (lam / (245760 * (n : ℝ) * D))) := by
    rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  have hcmp1 : (4 : ℝ≥0∞) * ENNReal.ofReal (lam / (245760 * (n : ℝ) * D)) ≤ eps := by
    rw [h4c, hepsdef]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [show 4 * (lam / (245760 * (n : ℝ) * D)) = lam / (61440 * ((n : ℝ) * D)) by
      field_simp; ring]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hcmp3 : (4 : ℝ≥0∞) * ENNReal.ofReal (lam / (245760 * (n : ℝ) * D))
      ≤ eps * ENNReal.ofReal (1 / (30720 * (n : ℝ) * D)) := by
    rw [h4c, hepsdef, ← ENNReal.ofReal_mul (by linarith)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    field_simp
    ring
  -- the three branches
  have hmain : 4 * (ENNReal.ofReal (lam / (245760 * (n : ℝ) * D)) * pi S)
      ≤ 4 * flow P pi S Sᶜ := by
    by_cases hc1 : pi S ≤ 2 * pi ((S ∩ interior K) \ S1)
    · calc 4 * (ENNReal.ofReal (lam / (245760 * (n : ℝ) * D)) * pi S)
          = (4 * ENNReal.ofReal (lam / (245760 * (n : ℝ) * D))) * pi S := by ring
        _ ≤ eps * pi S := by gcongr
        _ ≤ eps * (2 * pi ((S ∩ interior K) \ S1)) := by gcongr
        _ = 2 * (eps * pi ((S ∩ interior K) \ S1)) := by ring
        _ ≤ 2 * (eps * (pi ((S ∩ interior K) \ S1) + pi ((interior K \ S) \ S2))) := by
            gcongr
            exact le_self_add
        _ ≤ 2 * (2 * flow P pi S Sᶜ) := by gcongr
        _ = 4 * flow P pi S Sᶜ := by ring
    by_cases hc2 : pi Sᶜ ≤ 2 * pi ((interior K \ S) \ S2)
    · calc 4 * (ENNReal.ofReal (lam / (245760 * (n : ℝ) * D)) * pi S)
          = (4 * ENNReal.ofReal (lam / (245760 * (n : ℝ) * D))) * pi S := by ring
        _ ≤ eps * pi S := by gcongr
        _ ≤ eps * pi Sᶜ := mul_le_mul_right (hShalf.trans hSc) eps
        _ ≤ eps * (2 * pi ((interior K \ S) \ S2)) := by gcongr
        _ = 2 * (eps * pi ((interior K \ S) \ S2)) := by ring
        _ ≤ 2 * (eps * (pi ((S ∩ interior K) \ S1) + pi ((interior K \ S) \ S2))) := by
            gcongr
            exact le_add_self
        _ ≤ 2 * (2 * flow P pi S Sᶜ) := by gcongr
        _ = 4 * flow P pi S Sᶜ := by ring
    rw [not_le] at hc1 hc2
    have h1 : pi S < 2 * pi S1 := by
      have hstep : pi S + pi S < pi S + 2 * pi S1 := by
        calc pi S + pi S = 2 * pi S := (two_mul _).symm
          _ ≤ 2 * (pi ((S ∩ interior K) \ S1) + pi S1) := by gcongr
          _ = 2 * pi ((S ∩ interior K) \ S1) + 2 * pi S1 := by ring
          _ < pi S + 2 * pi S1 :=
              ENNReal.add_lt_add_right
                (ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _)) hc1
      exact (ENNReal.add_lt_add_iff_left hpitop).1 hstep
    have h2 : pi Sᶜ < 2 * pi S2 := by
      have hstep : pi Sᶜ + pi Sᶜ < pi Sᶜ + 2 * pi S2 := by
        calc pi Sᶜ + pi Sᶜ = 2 * pi Sᶜ := (two_mul _).symm
          _ ≤ 2 * (pi ((interior K \ S) \ S2) + pi S2) := by gcongr
          _ = 2 * pi ((interior K \ S) \ S2) + 2 * pi S2 := by ring
          _ < pi Sᶜ + 2 * pi S2 :=
              ENNReal.add_lt_add_right
                (ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _)) hc2
      exact (ENNReal.add_lt_add_iff_left (measure_ne_top _ _)).1 hstep
    have h2' : pi S < 2 * pi S2 := lt_of_le_of_lt (hShalf.trans hSc) h2
    have hmin : pi S ≤ 2 * min (pi S1) (pi S2) := by
      rcases le_total (pi S1) (pi S2) with h | h
      · rw [min_eq_left h]; exact h1.le
      · rw [min_eq_right h]; exact h2'.le
    calc 4 * (ENNReal.ofReal (lam / (245760 * (n : ℝ) * D)) * pi S)
        = (4 * ENNReal.ofReal (lam / (245760 * (n : ℝ) * D))) * pi S := by ring
      _ ≤ (eps * ENNReal.ofReal (1 / (30720 * (n : ℝ) * D))) * pi S := by gcongr
      _ = eps * (ENNReal.ofReal (1 / (30720 * (n : ℝ) * D)) * pi S) := by ring
      _ ≤ eps * (ENNReal.ofReal (1 / (30720 * (n : ℝ) * D)) * (2 * min (pi S1) (pi S2))) := by
          gcongr
      _ = 2 * (eps * (ENNReal.ofReal (1 / (30720 * (n : ℝ) * D)) * min (pi S1) (pi S2))) := by
          ring
      _ ≤ 2 * (eps * pi ((K \ S1) \ S2)) := by gcongr
      _ ≤ 2 * (eps * (pi ((S ∩ interior K) \ S1) + pi ((interior K \ S) \ S2))) := by gcongr
      _ ≤ 2 * (2 * flow P pi S Sᶜ) := by gcongr
      _ = 4 * flow P pi S Sᶜ := by ring
  rw [conductanceOn_apply, ENNReal.le_div_iff_mul_le (Or.inl hSpos.ne') (Or.inl hpitop)]
  have h4ne : (4 : ℝ≥0∞) ≠ 0 := by norm_num
  have h4top : (4 : ℝ≥0∞) ≠ ⊤ := by norm_num
  exact (ENNReal.mul_le_mul_iff_right h4ne h4top).mp hmain

/-- **Theorem 4.2 in the paper's constant, at the lower semicontinuous `hIso`, with `hLem41` on
the interior.**

`ArlibCommunity.Foundations.MarkovChainTheory.conductance_hitAndRun_ge_interior` replayed on
`ArlibCommunity.Foundations.Geometry.conductance_hitAndRun_ge_of_tv_lsc_interior`; the arithmetic is the original's. -/
theorem conductance_hitAndRun_ge_lsc_interior (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
    (hLem41 : ∀ u ∈ interior K, ∀ v ∈ interior K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      ArlibCommunity.Foundations.Convex.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 500)))
    (hIso : ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))), LowerSemicontinuous h → (∀ x, 0 ≤ h x) →
      (∀ x ∈ K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (crossRatioDist K u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(uniformOn volume K)) *
          min (uniformOn volume K T₁) (uniformOn volume K T₂)
        ≤ uniformOn volume K ((K \ T₁) \ T₂)) :
    ENNReal.ofReal (1 / (2 ^ 27 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hD1 : (1 : ℝ) ≤ D := le_trans (one_le_diam_of_unitBall hn hKb hball) hD
  refine le_trans (ENNReal.ofReal_le_ofReal ?_)
    (conductance_hitAndRun_ge_of_tv_lsc_interior hn hKc hKcl hKm hKb hball hD (by norm_num)
      (by norm_num) hLem41 hIso)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **The composition: Theorem 4.2 with `hIso` discharged, `hLem41` on the interior.**

`ArlibCommunity.Foundations.Convex.hIso_lowerSemicontinuous` fed to `ArlibCommunity.Foundations.Geometry.conductance_hitAndRun_ge_lsc_interior`.  The
residual binders are exactly three, all named and all inline at the declaration: `hLem41`
(Lemma 4.1, on `interior K` — the only satisfiable form, and the one
`ArlibCommunity.Foundations.MarkovChainTheory.hLem41_interior_uncond` proves outright), `htrans` (the chord transfer,
proved by `ArlibCommunity.Foundations.Convex.htrans_of_compact`) and `hloc` (the Localization Lemma for continuous
integrands with the needle inside the body, proved by `ArlibCommunity.Foundations.Convex.hloc_needle_in_body`).  `hIso` —
the paper's Theorem 2.1, the binder three attempts have failed to discharge — is *gone*.

That the two `hIso` shapes agree is not asserted here, it is checked: this composition would not
typecheck if the binder replayed into `ArlibCommunity.Foundations.Geometry.conductance_hitAndRun_ge_of_tv_lsc_interior`
differed by a single clause from the conclusion of `ArlibCommunity.Foundations.Convex.hIso_lowerSemicontinuous`. -/
theorem conductance_hitAndRun_ge_of_transfer_of_localization_interior (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
    (hLem41 : ∀ u ∈ interior K, ∀ v ∈ interior K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      ArlibCommunity.Foundations.Convex.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 500)))
    (htrans : ∀ (g : EuclideanSpace ℝ (Fin n) → ℝ)
        (U₁ U₂ : Set (EuclideanSpace ℝ (Fin n))), Continuous g → (∀ x, 0 ≤ g x) →
      (∀ x ∈ K, g x ≤ 1 / 3) →
      MeasurableSet U₁ → MeasurableSet U₂ → U₁ ⊆ K → U₂ ⊆ K → Disjoint U₁ U₂ →
      (∀ u ∈ U₁, ∀ v ∈ U₂, ∀ x ∈ K,
        (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
        g x ≤ min 1 (crossRatioDist K u v) / 3) →
      ∀ ε : ℝ, 0 < ε → ∀ C₁ C₂ : Set (EuclideanSpace ℝ (Fin n)),
        IsCompact C₁ → IsCompact C₂ → C₁ ⊆ U₁ → C₂ ⊆ U₂ →
        C₁ ⊆ interior K → C₂ ⊆ interior K → C₁.Nonempty → C₂.Nonempty →
        ∃ ρ : ℝ, 0 < ρ ∧ ∀ u : EuclideanSpace ℝ (Fin n), Metric.infDist u C₁ < ρ →
          ∀ v : EuclideanSpace ℝ (Fin n), Metric.infDist v C₂ < ρ → ∀ x ∈ K,
            (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
            g x ≤ min 1 (crossRatioDist K u v) / 3 + ε)
    (hloc : ∀ g₁ g₂ : EuclideanSpace ℝ (Fin n) → ℝ, Continuous g₁ → Continuous g₂ →
      (∫ x in K, g₁ x) = 0 → 0 < (∫ x in K, g₂ x) →
      ∃ (p e : EuclideanSpace ℝ (Fin n)) (α β : ℝ) (D : ℝ → ℝ), α ≤ β ∧
        (∀ r ∈ Set.Icc α β, needleMap p e r ∈ K) ∧
        (∀ t ∈ Set.Icc α β, 0 ≤ D t) ∧ LogConcaveOn (Set.Icc α β) D ∧
        IntervalIntegrable D volume α β ∧
        (∫ t in Set.Icc α β, g₁ (needleMap p e t) * D t) = 0 ∧
        0 < ∫ t in Set.Icc α β, g₂ (needleMap p e t) * D t) :
    ENNReal.ofReal (1 / (2 ^ 27 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) := by
  have hK0 : volume K ≠ 0 := by
    have hpos : 0 < volume (Metric.closedBall z 1) :=
      Metric.measure_closedBall_pos volume z one_pos
    exact (lt_of_lt_of_le hpos (measure_mono hball)).ne'
  obtain ⟨R, hR⟩ := hKb.subset_closedBall (0 : EuclideanSpace ℝ (Fin n))
  have hKtop : volume K ≠ ⊤ :=
    ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono hR)
  exact conductance_hitAndRun_ge_lsc_interior hn hKc hKcl hKm hKb hball hD hLem41
    (hIso_lowerSemicontinuous hKc hKcl hKm hKb hK0 hKtop htrans hloc)

/-- **The composition with `hLem41` demanded on all of `K`** — the shape this theorem had before
`ArlibCommunity.Foundations.Geometry.conductance_hitAndRun_ge_of_transfer_of_localization_interior` was split off, kept verbatim
so that every existing consumer continues to typecheck, and derived from the interior form by
`interior_subset`. -/
theorem conductance_hitAndRun_ge_of_transfer_of_localization (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
    (hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      ArlibCommunity.Foundations.Convex.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 500)))
    (htrans : ∀ (g : EuclideanSpace ℝ (Fin n) → ℝ)
        (U₁ U₂ : Set (EuclideanSpace ℝ (Fin n))), Continuous g → (∀ x, 0 ≤ g x) →
      (∀ x ∈ K, g x ≤ 1 / 3) →
      MeasurableSet U₁ → MeasurableSet U₂ → U₁ ⊆ K → U₂ ⊆ K → Disjoint U₁ U₂ →
      (∀ u ∈ U₁, ∀ v ∈ U₂, ∀ x ∈ K,
        (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
        g x ≤ min 1 (crossRatioDist K u v) / 3) →
      ∀ ε : ℝ, 0 < ε → ∀ C₁ C₂ : Set (EuclideanSpace ℝ (Fin n)),
        IsCompact C₁ → IsCompact C₂ → C₁ ⊆ U₁ → C₂ ⊆ U₂ →
        C₁ ⊆ interior K → C₂ ⊆ interior K → C₁.Nonempty → C₂.Nonempty →
        ∃ ρ : ℝ, 0 < ρ ∧ ∀ u : EuclideanSpace ℝ (Fin n), Metric.infDist u C₁ < ρ →
          ∀ v : EuclideanSpace ℝ (Fin n), Metric.infDist v C₂ < ρ → ∀ x ∈ K,
            (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
            g x ≤ min 1 (crossRatioDist K u v) / 3 + ε)
    (hloc : ∀ g₁ g₂ : EuclideanSpace ℝ (Fin n) → ℝ, Continuous g₁ → Continuous g₂ →
      (∫ x in K, g₁ x) = 0 → 0 < (∫ x in K, g₂ x) →
      ∃ (p e : EuclideanSpace ℝ (Fin n)) (α β : ℝ) (D : ℝ → ℝ), α ≤ β ∧
        (∀ r ∈ Set.Icc α β, needleMap p e r ∈ K) ∧
        (∀ t ∈ Set.Icc α β, 0 ≤ D t) ∧ LogConcaveOn (Set.Icc α β) D ∧
        IntervalIntegrable D volume α β ∧
        (∫ t in Set.Icc α β, g₁ (needleMap p e t) * D t) = 0 ∧
        0 < ∫ t in Set.Icc α β, g₂ (needleMap p e t) * D t) :
    ENNReal.ofReal (1 / (2 ^ 27 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) :=
  conductance_hitAndRun_ge_of_transfer_of_localization_interior hn hKc hKcl hKm hKb hball hD
    (fun u hu v hv => hLem41 u (interior_subset hu) v (interior_subset hv)) htrans hloc

/-- **Lovász–Vempala Theorem 4.2 with the Localization Lemma discharged.**

`ArlibCommunity.Foundations.Geometry.conductance_hitAndRun_ge_of_transfer_of_localization` with its third binder `hloc` proved
rather than assumed, leaving `hLem41` (Lemma 4.1, owned elsewhere) and `htrans` (the chord
transfer).  The statement is that theorem's, clause for clause, with the single change that
`1 ≤ n` becomes `2 ≤ n` — the dimension restriction of
`ArlibCommunity.Foundations.Convex.exists_flat_cut_chain_collinear_compact_ge`, hence of `ArlibCommunity.Foundations.Convex.hloc_needle_in_body`.

That the discharged binder is *the* binder is not asserted, it is checked: the proof feeds
`ArlibCommunity.Foundations.Convex.hloc_needle_in_body` to the `hloc` slot verbatim, and this would not typecheck if the two
differed by a single clause.  The compactness `hloc_needle_in_body` needs is exactly the
`IsClosed K` and `Bornology.IsBounded K` the consumer already carries; no hypothesis is added. -/
theorem conductance_hitAndRun_ge_of_transfer (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
    (hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      ArlibCommunity.Foundations.Convex.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 500)))
    (htrans : ∀ (g : EuclideanSpace ℝ (Fin n) → ℝ)
        (U₁ U₂ : Set (EuclideanSpace ℝ (Fin n))), Continuous g → (∀ x, 0 ≤ g x) →
      (∀ x ∈ K, g x ≤ 1 / 3) →
      MeasurableSet U₁ → MeasurableSet U₂ → U₁ ⊆ K → U₂ ⊆ K → Disjoint U₁ U₂ →
      (∀ u ∈ U₁, ∀ v ∈ U₂, ∀ x ∈ K,
        (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
        g x ≤ min 1 (crossRatioDist K u v) / 3) →
      ∀ ε : ℝ, 0 < ε → ∀ C₁ C₂ : Set (EuclideanSpace ℝ (Fin n)),
        IsCompact C₁ → IsCompact C₂ → C₁ ⊆ U₁ → C₂ ⊆ U₂ →
        C₁ ⊆ interior K → C₂ ⊆ interior K → C₁.Nonempty → C₂.Nonempty →
        ∃ ρ : ℝ, 0 < ρ ∧ ∀ u : EuclideanSpace ℝ (Fin n), Metric.infDist u C₁ < ρ →
          ∀ v : EuclideanSpace ℝ (Fin n), Metric.infDist v C₂ < ρ → ∀ x ∈ K,
            (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
            g x ≤ min 1 (crossRatioDist K u v) / 3 + ε) :
    ENNReal.ofReal (1 / (2 ^ 27 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) :=
  conductance_hitAndRun_ge_of_transfer_of_localization (by omega) hKc hKcl hKm hKb hball hD
    hLem41 htrans (hloc_needle_in_body hn hKc hKcl hKb)

/-- **The consumer, with `htrans` discharged.**

`ArlibCommunity.Foundations.Geometry.conductance_hitAndRun_ge_of_transfer_of_localization` fed `ArlibCommunity.Foundations.Convex.htrans_of_compact`.
The residual binders are exactly two: `hLem41` (Lemma 4.1) and `hloc` (the Localization
Lemma for continuous integrands with the needle inside the body).  `htrans` is gone.

This composition is also the vacuity check on `ArlibCommunity.Foundations.Convex.htrans_of_compact`: the binder is not
retyped here, it is *applied*, so a statement that drifted from the one
`ArlibCommunity/Foundations/Convex/CrossRatioIsoperimetry/Analysis/IsoConcaveWeight.lean` asks for by a single clause would be a type error. -/
theorem conductance_hitAndRun_ge_of_localization (hn : 1 ≤ n)
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
    (hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      ArlibCommunity.Foundations.Convex.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 500)))
    (hloc : ∀ g₁ g₂ : EuclideanSpace ℝ (Fin n) → ℝ, Continuous g₁ → Continuous g₂ →
      (∫ x in K, g₁ x) = 0 → 0 < (∫ x in K, g₂ x) →
      ∃ (p e : EuclideanSpace ℝ (Fin n)) (α β : ℝ) (D : ℝ → ℝ), α ≤ β ∧
        (∀ r ∈ Set.Icc α β, needleMap p e r ∈ K) ∧
        (∀ t ∈ Set.Icc α β, 0 ≤ D t) ∧ LogConcaveOn (Set.Icc α β) D ∧
        IntervalIntegrable D volume α β ∧
        (∫ t in Set.Icc α β, g₁ (needleMap p e t) * D t) = 0 ∧
        0 < ∫ t in Set.Icc α β, g₂ (needleMap p e t) * D t) :
    ENNReal.ofReal (1 / (2 ^ 27 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) :=
  conductance_hitAndRun_ge_of_transfer_of_localization hn hKc hKcl hKm hKb hball hD hLem41
    (htrans_of_compact hKc hKcl hKb) hloc

/-- **Theorem 4.2 of Lovász–Vempala, with `hIso` replaced by Theorem 2.1's conclusion.**

Residual binders: `hLem41` and `hthm21`.  The second is the ℝ-valued, Lebesgue-normalised form
that `ArlibCommunity.Foundations.Convex.thm21_of_localization` proves from the Localization Lemma, so the moment that
localization work lands this theorem is one `exact` away from carrying only `hLem41`.

The trade is exactly `ArlibCommunity.Foundations.Convex.hIso_of_thm21` and nothing else. -/
theorem conductance_hitAndRun_ge_of_thm21 (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
    (hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      ArlibCommunity.Foundations.Convex.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 500)))
    (hthm21 : ∀ (g : EuclideanSpace ℝ (Fin n) → ℝ)
        (U₁ U₂ : Set (EuclideanSpace ℝ (Fin n))), Measurable g →
      MeasurableSet U₁ → MeasurableSet U₂ → Disjoint U₁ U₂ →
      (∀ x, 0 ≤ g x) → (∀ x ∈ K, g x ≤ 1 / 3) →
      (∀ u ∈ U₁, ∀ v ∈ U₂, ∀ x ∈ K,
        (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
        g x ≤ min 1 (crossRatioDist K u v) / 3) →
      ∀ A : ℝ, 0 ≤ A → A ≤ 1 / 2 → (volume U₁).toReal = A * (volume K).toReal →
        A * (∫ x in K, g x) ≤ (volume ((K \ U₁) \ U₂)).toReal) :
    ENNReal.ofReal (1 / (2 ^ 27 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) := by
  have hK0 : volume K ≠ 0 := by
    have hpos : 0 < volume (Metric.closedBall z 1) :=
      Metric.measure_closedBall_pos volume z one_pos
    exact (lt_of_lt_of_le hpos (measure_mono hball)).ne'
  obtain ⟨R, hR⟩ := hKb.subset_closedBall (0 : EuclideanSpace ℝ (Fin n))
  have hKtop : volume K ≠ ⊤ :=
    ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono hR)
  exact conductance_hitAndRun_ge hn hKc hKcl hKm hKb hball hD hLem41
    (hIso_of_thm21 hKb hKm hK0 hKtop hthm21)

/-- **Theorem 4.2 of Lovász–Vempala, with `hIso` replaced by the *corrected* Theorem 2.1
binder.**

`ArlibCommunity.Foundations.Geometry.conductance_hitAndRun_ge_of_thm21` rerun on `hthm21sub`.  Residual binders: `hLem41`
(owned elsewhere) and `hthm21sub`.  Unlike the original, `hthm21sub` is not refuted by
`ArlibCommunity.Foundations.Convex.not_thm21_book`, so this composition is the one a future proof of Theorem 2.1 should be
pointed at. -/
theorem conductance_hitAndRun_ge_book (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
    (hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      ArlibCommunity.Foundations.Convex.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 500)))
    (hthm21sub : ∀ (g : EuclideanSpace ℝ (Fin n) → ℝ)
        (U₁ U₂ : Set (EuclideanSpace ℝ (Fin n))), Measurable g →
      MeasurableSet U₁ → MeasurableSet U₂ → U₁ ⊆ K → U₂ ⊆ K → Disjoint U₁ U₂ →
      (∀ x, 0 ≤ g x) → (∀ x ∈ K, g x ≤ 1 / 3) →
      (∀ u ∈ U₁, ∀ v ∈ U₂, ∀ x ∈ K,
        (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
        g x ≤ min 1 (crossRatioDist K u v) / 3) →
      ∀ A : ℝ, 0 ≤ A → A ≤ 1 / 2 → (volume U₁).toReal = A * (volume K).toReal →
        A * (∫ x in K, g x) ≤ (volume ((K \ U₁) \ U₂)).toReal) :
    ENNReal.ofReal (1 / (2 ^ 27 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) := by
  have hK0 : volume K ≠ 0 := by
    have hpos : 0 < volume (Metric.closedBall z 1) :=
      Metric.measure_closedBall_pos volume z one_pos
    exact (lt_of_lt_of_le hpos (measure_mono hball)).ne'
  obtain ⟨R, hR⟩ := hKb.subset_closedBall (0 : EuclideanSpace ℝ (Fin n))
  have hKtop : volume K ≠ ⊤ :=
    ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono hR)
  exact conductance_hitAndRun_ge hn hKc hKcl hKm hKb hball hD hLem41
    (hIso_book hKb hKm hK0 hKtop hthm21sub)

/-- **The copy of the `hIso` binder used in the check really is that binder**: it is handed,
unchanged, to `ArlibCommunity.Foundations.MarkovChainTheory.conductance_hitAndRun_ge`. -/
theorem conductance_hitAndRun_ge_of_hIso_copy (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
    (hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      ArlibCommunity.Foundations.Convex.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 500)))
    (hIso : ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))), (∀ x, 0 ≤ h x) →
      (∀ x ∈ K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (crossRatioDist K u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(uniformOn volume K)) *
          min (uniformOn volume K T₁) (uniformOn volume K T₂)
        ≤ uniformOn volume K ((K \ T₁) \ T₂)) :
    ENNReal.ofReal (1 / (2 ^ 27 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) :=
  ArlibCommunity.Foundations.MarkovChainTheory.conductance_hitAndRun_ge hn hKc hKcl hKm hKb hball hD hLem41 hIso

/-- **Theorem 4.2 at the lower semicontinuous `hIso`, with `hLem41` demanded on all of `K`** —
the shape this theorem had before `ArlibCommunity.Foundations.Geometry.conductance_hitAndRun_ge_of_tv_lsc_interior` was split
off, kept verbatim so that every existing consumer continues to typecheck.

The proof *is* the claim that the split is a strengthening: a caller holding Lemma 4.1 on all of
`K` gets it on `interior K` by `interior_subset`, so nothing provable from this statement is lost
by the weaker binder.  The converse fails, and that is the point — see
`ArlibCommunity.Foundations.Geometry.conductance_hitAndRun_ge_of_tv_lsc_interior`'s docstring. -/
theorem conductance_hitAndRun_ge_of_tv_lsc (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      ArlibCommunity.Foundations.Convex.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - lam)))
    (hIso : ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))), LowerSemicontinuous h → (∀ x, 0 ≤ h x) →
      (∀ x ∈ K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (crossRatioDist K u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(uniformOn volume K)) *
          min (uniformOn volume K T₁) (uniformOn volume K T₂)
        ≤ uniformOn volume K ((K \ T₁) \ T₂)) :
    ENNReal.ofReal (lam / (245760 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) :=
  conductance_hitAndRun_ge_of_tv_lsc_interior hn hKc hKcl hKm hKb hball hD hlam0 hlam1
    (fun u hu v hv => hLem41 u (interior_subset hu) v (interior_subset hv)) hIso

/-- **Theorem 4.2 in the paper's constant at the lower semicontinuous `hIso`, with `hLem41`
demanded on all of `K`** — the shape this theorem had before
`ArlibCommunity.Foundations.Geometry.conductance_hitAndRun_ge_lsc_interior` was split off, kept verbatim so that every existing
consumer continues to typecheck, and derived from the interior form by `interior_subset`. -/
theorem conductance_hitAndRun_ge_lsc (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
    (hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      ArlibCommunity.Foundations.Convex.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 500)))
    (hIso : ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))), LowerSemicontinuous h → (∀ x, 0 ≤ h x) →
      (∀ x ∈ K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (crossRatioDist K u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(uniformOn volume K)) *
          min (uniformOn volume K T₁) (uniformOn volume K T₂)
        ≤ uniformOn volume K ((K \ T₁) \ T₂)) :
    ENNReal.ofReal (1 / (2 ^ 27 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) :=
  conductance_hitAndRun_ge_lsc_interior hn hKc hKcl hKm hKb hball hD
    (fun u hu v hv => hLem41 u (interior_subset hu) v (interior_subset hv)) hIso

/-- **The replayed conductance theorem reproves the original.**

Same statement as `ArlibCommunity.Foundations.Geometry.conductance_hitAndRun_ge_of_hIso_copy` — hence, by that theorem, the
statement of `ArlibCommunity.Foundations.MarkovChainTheory.conductance_hitAndRun_ge` — but proved through
`ArlibCommunity.Foundations.Geometry.conductance_hitAndRun_ge_lsc`, feeding it the full binder with the
`LowerSemicontinuous` clause discarded.  So the 375-line replay neither weakened the conclusion
nor strengthened any hypothesis other than the one clause it was meant to add. -/
theorem conductance_hitAndRun_ge_of_hIso_copy_via_lsc (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
    (hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      ArlibCommunity.Foundations.Convex.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 500)))
    (hIso : ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))), (∀ x, 0 ≤ h x) →
      (∀ x ∈ K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (crossRatioDist K u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(uniformOn volume K)) *
          min (uniformOn volume K T₁) (uniformOn volume K T₂)
        ≤ uniformOn volume K ((K \ T₁) \ T₂)) :
    ENNReal.ofReal (1 / (2 ^ 27 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) :=
  conductance_hitAndRun_ge_lsc hn hKc hKcl hKm hKb hball hD hLem41
    (fun h T₁ T₂ _ => hIso h T₁ T₂)

end ArlibCommunity.Foundations.MarkovChainTheory
