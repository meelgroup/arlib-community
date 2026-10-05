# CV18 analysis

This directory contains the end-to-end formalization of Cousins and
Vempala's accelerated Gaussian-cooling volume algorithm [CV18].

The executable membership-oracle program, continuous semantics, cooling
schedule, query accounting, restricted-Gaussian stationarity, warm starts,
fixed-rate and terminal moment bounds, ideal-product calculation, initial
coupling, and median amplification are formalized.

The strongest assembled result is the premise-free theorem
`volumeTheorem_finalScheduled`.  It contains both the advertised accuracy
conclusion and the explicit membership-query bound for the executable
scheduled program.  Its chronological reset-reference witness is the
unconditional theorem `globalResetReferenceExists`.

`FigureOneRadialTruncationBound` is now proved from `WellRounded` by
`figureOneRadialTruncationBound`.  Thus radial truncation is no longer an
assumption of the assembled theorem.

`FigureOneSharpAcceleratedMoments`, the phase-sensitive accelerated
localization estimate, is now proved unconditionally in
`VolumeProofSharpMoments.lean`. Its compact-convex localization dependency is
vendored under `ArlibCommunity/External/Kr25`; the adapter covers the exact
first-hit schedule, including the terminally clipped accelerated step.

The final recurrence constructs the accepted initial reference, performs the
Gaussian equation-(6) resets, preserves the complete old-coordinate law and
Lemma 7.17(c) facts, appends the terminal reset, and feeds the resulting global
witness to the query-cap and amplification assembly.  The final axiom audit is
`propext`, `Classical.choice`, and `Quot.sound`; there is no `sorryAx`.

The discussion below records the dependency audit and intermediate gaps that
guided the formalization.  Those gaps are now closed by the final scheduled
assembly.

## Vempala optimization-book cross-check

The local optimization-book source is useful background but does not discharge
the remaining walk obligation. `annealing_volume.tex`, Lemma
`lem:chebychev_ratio`, proves the classical fixed-rate logconcave-power ratio
bound. The accelerated `O*(n^3)` CV theorem is then only stated and cited.
`ball_walk.tex` develops warm-start conductance-to-mixing and states Gaussian
restricted isoperimetry, but does not specialize the whole chain to CV18's
truncated Gaussian Metropolis program or its dependent product failure event.
The radial truncation proof now uses an explicit dyadic localization tail with
the correspondingly enlarged terminal-radius constant.

## Existing formal overlap in arlib-community

The HitAndRun background is closer to the missing mixing proof than the book
text alone. `SharpIsoperimetryConcave.lean` proves a Gaussian-restricted
isoperimetric inequality, while `BallWalk.lean`, `BallWalkConductance.lean`,
`Warmness.lean`, and `ConductanceToTV.lean` provide a kernel, reversibility,
lazy conductance, warm-start, and total-variation chain.

They do not yet prove `FigureOnePostInitialMixingBound`: the ball-walk modules
treat an unweighted uniform target, whereas CV18 executes a Gaussian-weighted
Metropolis step and needs the speedy/average-local-conductance analysis. The
existing conductance module also documents a weaker overlap estimate and only
an exponentially small unconditional local-conductance witness. These modules
are reusable infrastructure, not a drop-in discharge of the remaining
dependent-program obligation.

## Exact sampling mismatch to resolve

The paper's Figure 1 requests a fixed number of **proper** steps and, at phase
variance `sigma2`, targets `K ∩ 4 * sqrt(sigma2 * n) Bₙ`.  Its proof then
converts the expected number of raw ball-walk proposals into an executable
cutoff/restart procedure.  The current executable Lean program instead runs a
fixed number of raw proposals against the single terminal truncation
`truncatedBody q I`.

Consequently neither the optimization-book warm-start theorem nor the paper's
speedy-walk conductance theorem has the conclusion required by the current
kernel.  An unconditional proof must do one of the following, together with
the sequential TV composition already formalized here:

1. formalize phase truncation, proper-step execution, and the global
   cutoff/restart argument from CV18; or
2. prove a new exceptional-set/s-conductance theorem directly for the current
   fixed-terminal-truncation, fixed-raw-step kernel.

Importing a speedy-walk mixing theorem alone is insufficient: its stationary
law is proportional to local conductance times the Gaussian density, not the
target truncated Gaussian, and it does not identify a fixed raw-step law with
the required sample law.

## Proper-step bridge progress

`VolumeProofProperStep.lean` now supplies the first operational part of option
1.  The speedy-walk and holding-time developments have been ported into this
CV18 tree without imports from the stale workspace.  In addition, the new
`geometricCostKernel` constructs the joint law of the number of raw trials and
the next proper state.  The following are proved:

- the exact geometric cost/state rectangle probabilities;
- the returned-state marginal is exactly the requested next-state kernel;
- the expected trials-through-success cost is exactly the reciprocal of the
  success probability, hence exactly `1 / ell K delta x` for the ball walk;
- the costed kernel is Markov whenever the success probability is pointwise
  nonzero; and
- specializing the success probability to `ell K delta` makes the returned
  state exactly one `speedyWalk K delta` step.

The Gaussian Metropolis and speedy-Gaussian kernels have now also been ported.
`gaussianProperStepWithCost` specializes the same construction to CV18's
actual proper step: the proposal must land in the body, while a failed
Metropolis test remains a self-loop inside the returned speedy-Gaussian step.
The file proves that its state marginal is exactly
`speedyMetropolisGaussian`, that its expected raw-proposal cost is exactly
`1 / ell K delta x`, and the exact mixture identity expressing one ordinary
Gaussian Metropolis step as a proper speedy step or an improper self-loop.

The iterated bridge is now also formalized.  A totalized cost kernel handles
zero-local-conductance ambient states without the false assumption that
`ell > 0` everywhere, and agrees with the genuine geometric waiting law at
every non-stuck state.  `accumulatedCostStep_pow_snd` proves generically that,
after any `t` cost-accumulating steps, forgetting the cost gives exactly the
`t`-fold state-kernel iterate.  Its Gaussian specialization identifies the
state marginal with the `t`-fold `speedyMetropolisGaussian` kernel.

The raw-trajectory side is now formalized as well.  A Boolean-marked Gaussian
Metropolis chain exposes whether each actual proposal landed in the body;
forgetting the mark recovers the ordinary Gaussian Metropolis chain at every
deterministic time.  Stopping at the first `true` mark gives exactly one speedy
Gaussian step, and the first-proper waiting time has the exact geometric tail
and mean `1 / ell`.  Independent stopped trajectories are then restarted for
`t` proper steps.  Their output law is exactly the `t`-step speedy Gaussian
law, while their expected total proposal count is bounded by the explicit sum
of per-state exit-time integrals along the speedy marginals.

The warm-start and cutoff algebra is now proved for the correct proper-proposal
cost.  The `ell` factor in the speedy stationary density cancels `1 / ell`
exactly, and `mul_lintegral_properProposalTotalCost_le` bounds the honest
trajectory's expected total raw-proposal cost.  Markov's inequality then gives
`mul_mul_measure_properProposalTotalCost_ge_le`, the cutoff/restart failure
bound.  Both theorems depend only on the paper's weighted
average-local-conductance lower bound `lambda` and the phase warm-start bound;
no extra Metropolis-acceptance penalty is needed because a rejected
Metropolis test is still a proper proposal.

`VolumeProofAverageConductance.lean` proves an unconditional version of
the weighted average-local-conductance estimate at the smaller step size
`delta ≤ 1/(2n)`.  The proof uses the homothetic core
`(1 - 1/(2n)) • K`: convexity and the unit-ball inclusion make every proposal
from the core proper, while Gaussian scaling and Bernoulli's inequality show
that the core retains at least half the Gaussian mass.  Consequently Lean now
proves `lambda = 1/2`, discharges both normalization guards for a finite-volume
body, and derives concrete expected-cost and cutoff theorems for the restarted
proper-proposal execution.

`VolumeProofAverageConductanceLV.lean` proves the corresponding estimate at
CV18's advertised Figure-1 step. It follows the layer-cake mechanism of
Lovász--Vempala Lemma 6.3, but applies the KLS convex-body escape estimate
directly to the rejected-proposal probability. Splitting Gaussian level sets
at radius `min{sigma,1}/4` bounds the rejected mass by
`(1/4 + 20 * delta * sqrt(n) / min{sigma,1})` times the total mass. Thus the
paper condition `delta <= min{sigma,1}/(4096*sqrt(n))` gives weighted average
local conductance at least `1/2`. The file specializes this theorem to
`figureOneProposalRadius` on `truncatedBody` and derives the nonzero
normalization, expected raw-proposal cost, and Markov-cutoff bounds. Its only
geometric input is the already formalized sharp-order KLS escape estimate.

The speedy-Gaussian conductance and mixing chain is now also ported and proved
without a stale-directory import.  In particular,
`conductance_speedyMetropolisGaussian_ge_uncond` gives the paper-shaped
conductance lower bound
`delta * log 2 / (640 * sigma * sqrt n)`, and
`mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit` converts it to the
explicit warm-start mixing count for the lazy speedy Metropolis-Gaussian walk.
The axiom audits of these capstones contain only Lean's standard `propext`,
choice, and quotient axioms.

`VolumeProofKernelBridge.lean` now removes the two one-step representation
mismatches between the executable walk and the abstract Metropolis library.
It proves that the normalized closed proposal ball used by the program is the
same measure as the normalized open ball used by `metropolisGaussian` (the
boundary sphere is Lebesgue-null), including after translation to the current
state.  It also proves that the program's body-filtered coin threshold is
exactly one half of `metropolisAccept`.  Thus the implementation's explicit
half-acceptance is the same laziness represented abstractly by `lazy`.
`truncatedMetropolisKernel_eq_lazy_metropolisGaussian` assembles these facts
into the exact kernel identity
`truncatedMetropolisKernel = lazy (metropolisGaussian truncatedBody delta sigma2)`.
The remaining mismatch is therefore no longer geometric, pointwise, or
one-step semantic.

`VolumeProofLazyProperClock.lean` now closes the lazy trajectory-level clock.
It exposes a Boolean proper-proposal mark while proving that forgetting the
mark recovers the ordinary lazy Metropolis law at every deterministic raw
time. Stopping at the first proper mark gives exactly one lazy-speedy step;
restarting this stopped experiment gives exactly the iterated lazy-speedy
output law. The realized wait has mean `1 / ell`, and the advertised LV
average-conductance theorem yields both the warm-start total-cost estimate and
its Markov cutoff bound. The module also specializes the deterministic-time
projection to `truncatedMetropolisKernel`, so this is now an exact bridge to
the executable Figure-1 transition rather than a parallel abstract chain.

`VolumeProofLazyProperProgram.lean` adds the corresponding bounded
membership-oracle program. Its marked step records body membership before the
Metropolis coin, so a coin rejection remains a proper proposal. Erasing the
mark is proved equal to the existing Figure-1 step at the program-syntax level.
Its full joint estimate law is also proved equal to
`lazyProperProposalGaussianAux`: body-hit probability is exactly `ell`, the
false slice is exactly the improper self-loop, and the true slice retains the
lazy Metropolis rejection behavior.
`cappedProperMetropolisBallWalk` then runs until a requested number of proper
marks or returns `none` at a raw-proposal cap, with a proved worst-case query
bound equal to that cap. This supplies the operational cutoff/restart primitive
that the paper describes but the previous fixed-raw-endpoint program lacked.
Its full finite semantics is now identified as well:
`cappedProperMetropolisBallWalk_semantics` proves, for every cap and requested
proper-step count, that the executable `Option`-valued output law is exactly
the recursively stopped abstract marked-kernel law. The same induction proves
the measurability facts needed to compose this program with later phases.

`VolumeProofLazyProperFailure.lean` closes the global raw-counter argument for
that finite program. It constructs a Bellman potential for the number of raw
proposals still needed, proves a direct Markov inequality for the recursive
failure mass, and bounds its expectation from a warm start by the stationary
`1 / ell` integral. At the Figure-1 proposal radius this gives the executable
paper-shaped inequality
`(1/2) * rawCap * Pr[none] <= properSteps * M`. Thus the cap failure estimate
now applies to the membership-oracle program itself, not only to a separately
constructed stopped trajectory.

`VolumeProofSpeedyToTarget.lean` formalizes the exact measure-theoretic core of
CV18's speedy-to-ball rejection map.  A speedy-stationary draw lands in
`(1 - 1/(2n)) K` with probability at least one half; on that core `ell = 1`, so
conditioning removes the speedy weight exactly.  Scaling the accepted point
back to `K` changes the Gaussian variance from `sigma2` to
`sigma2 / (1 - 1/(2n))^2`.  A second, pointwise-valid rejection probability is
proved to change that scaled law exactly into the desired restricted Gaussian.
On the paper's phase radius, Lean also proves that this second acceptance
probability is at least `exp (-8)`. Thus the paper's underspecified
distributional identity and both loops' constant success probabilities no
longer remain assumptions.

The second loop in fact admits a stronger bound that resolves one concern
about the current executable's fixed terminal truncation.  Homothetic Gaussian
scaling proves its *average* acceptance probability is at least `1/2` on any
convex body containing the origin, without an outer-radius assumption.
Therefore the current larger body does not by itself make the target rejection
expensive; phase-radius truncation is needed elsewhere in the mixing argument,
not for this rejection-cost bound.

The TV effect of rejection is now formalized as well. Common measurable
acceptance weighting cannot increase setwise TV error, and normalizing an
accepted subprobability law amplifies error by at most `2/p` when both
acceptance masses are at least `p`. In the CV18 use case, an exact acceptance
mass of `1/2` and incoming error at most `1/4` force approximate acceptance at
least `1/4`, yielding a complete `8 * epsilon` rejection-stage bound. Thus
neither rejection identity nor rejection stability remains implicit.

`VolumeProofPhaseMixing.lean` closes a tight constant mismatch between the
ported conductance theorem and the paper. The previous theorem required outer
radius `2 * sigma * sqrt n`, while Figure 1 truncates at
`4 * sigma * sqrt n`. At the larger endpoint the Metropolis floor is
`exp (-65/128)`, just above `3/5`; a certified fifth-order Taylor remainder
proves this margin. The module consequently proves the same speedy-walk
conductance and warm-start TV mixing rate on the full paper radius, defines
the phase-truncated body, discharges its convexity, measurability, positive
volume, and radius obligations, and packages the resulting phase mixing
theorem. This theorem currently covers `n >= 21`, matching the available
sharp overlap theorem.

The final scheduled construction now composes these ingredients through the
chronological history-preserving reset recurrence.  The Gaussian and terminal
phase errors sum exactly to `figureOneScheduledGlobalOuterStepError`; the
completed recurrence proves `globalResetReferenceExists`, and
`volumeTheorem_finalScheduled` gives the unconditional end-to-end CV18
Theorem 1.1 statement with the advertised scheduled complexity rate.
