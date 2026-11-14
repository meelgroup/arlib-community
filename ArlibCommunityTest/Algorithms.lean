/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Using `ArlibCommunity.Algorithms`

TPA's analysis, consumed the way a downstream project consumes it: the counter's
law, its almost-sure termination, and the conversion of an additive log error
into a relative one.
-/
import ArlibCommunity.Algorithms

namespace ArlibCommunityTest.Algorithms

open ArlibCommunity.Algorithms.TPA

/-- **The headline.** On `m` independent `Uniform(0,1)` draws, the probability
that the running product still exceeds `c` drops by exactly the Poisson mass
`poissonPMF (ln(1/c)) m` when one more draw is taken — so a TPA run whose
centre-to-shell ratio is `c` contributes `Poisson(ln(1/c))` to the counter. -/
example (m : ℕ) {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    ((MeasureTheory.Measure.pi (fun _ : Fin m => unifUnit))
        {u : Fin m → ℝ | c < ∏ i, u i}).toReal
      - ((MeasureTheory.Measure.pi (fun _ : Fin (m + 1) => unifUnit))
        {u : Fin (m + 1) → ℝ | c < ∏ i, u i}).toReal
      = Arlib.Probability.poissonPMF (-Real.log c) m :=
  prob_exactly_eq_poissonPMF m hc hc1

/-- **Almost-sure termination**, in the elementary form: the probability of
performing more than `m` contractions tends to `0`. This is a statement about
`tpaTail`, the closed form, with no product measure in sight — which is the
point of routing the analysis through it. -/
example {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun m => tpaTail m c) Filter.atTop (nhds 0) :=
  tendsto_tpaTail_atTop hc

/-- **What the estimate is worth.** TPA estimates `A = ln(μ(B)/μ(B'))`, so the
guarantee it proves is additive in the log; this is the step that turns it into
the relative-error guarantee a caller wants. -/
example {A Ahat eps : ℝ} (heps : 0 < eps) (h : |Ahat - A| ≤ Real.log (1 + eps)) :
    (1 + eps)⁻¹ ≤ Real.exp Ahat / Real.exp A ∧
      Real.exp Ahat / Real.exp A ≤ 1 + eps :=
  relative_error_of_log_error heps h

end ArlibCommunityTest.Algorithms

namespace ArlibCommunityTest.HitAndRun

open MeasureTheory
open ArlibCommunity.Algorithms.HitAndRun

/-- Downstream smoke test for the fully discharged headline theorem. -/
example {n : ℕ} (hn : 21 ≤ n) (p : Problem n)
    {sigma : Measure (State n)} [IsProbabilityMeasure sigma]
    {M eps : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {S : Set (State n)} (hWarm : WarmStart p.body sigma M eps S)
    {m : ℕ} (hm : deadline n p.diameter M eps ≤ (m : ℝ)) :
    ArlibCommunity.Foundations.Convex.TVLe (run p.body sigma m) (target p.body) (ENNReal.ofReal eps) :=
  hitAndRun_mixes hn p hM heps0 heps1 hWarm hm

end ArlibCommunityTest.HitAndRun

namespace ArlibCommunityTest.KV97

open MeasureTheory
open ArlibCommunity.Algorithms.KV97

/-- Kannan–Vempala, Theorem 2: given a sampler whose density is within `1 ± ε` of
uniform at every point of the inflated polytope, every lattice point of the
polytope is returned with probability within a stated factor of `1 / V`. -/
example {n : ℕ} {ι : Type*} [Fintype ι] (p : Problem n ι)
    {sampler : Measure (State n)} {V ε : ℝ} (hV : 0 < V) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hs : AlmostUniformSampler sampler p.inflatedBody V ε)
    {x : LatticePoint n} (hx : toState x ∈ p.body) :
    (1 - ε) * (1 - Real.exp (-p.c ^ 2 / 2)) / V ≤ (output sampler {x}).toReal ∧
      (output sampler {x}).toReal ≤ (1 + ε) / V :=
  latticePoint_probability p hV hε0 hε1 hs hx

end ArlibCommunityTest.KV97

namespace ArlibCommunityTest.CV18

open ArlibCommunity.Algorithms.CV18

/-- The older compact interface: one base run is accurate given a radial
truncation bound and a mixing bound as hypotheses. Theorem 1.1 below discharges
both. -/
example (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I)
    (htrunc : FigureOneRadialTruncationBound q I)
    (hmixing : FigureOnePostInitialMixingBound q I oracle) :
    3 / 4 ≤
      outcomeProbability
        (volumeAlgorithmLaw
          (fun q => baseVolumeCooling figureOnePrimitives
            explicitVolumeCoolingSchedule q) q I oracle)
        (accurateOutcome q I) :=
  figureOne_base_accuracy_of_truncation_and_mixing q I oracle htrunc hmixing

/-- The headline: the concrete program `cv18Program`, defined under `Model/`,
meets the Theorem 1.1 accuracy and membership-query guarantee. -/
example : VolumeGuarantee cv18Program queryRate :=
  cv18TheoremOneOne

end ArlibCommunityTest.CV18
