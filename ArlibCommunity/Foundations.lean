/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel, Uddalok Sarkar
-/
/-
# ArlibCommunity.Foundations

Results that the algorithm analyses under `ArlibCommunity.Algorithms` build on but that are not
specific to any one algorithm: convex geometry, and Markov chains on a general measurable space.

Each major theorem is laid out like an algorithm entry, so that its statement can be audited
without reading its proof:

* `<Area>/<Theorem>/Model/Theorem.lean` states the theorem;
* `<Area>/<Theorem>/Model/Prelude.lean` (when present) defines what only that statement needs;
* `<Area>/Prelude.lean` defines what several statements share;
* `<Area>/<Theorem>/Analysis/` holds the proof, and `<Area>/Basic/` the lemmas shared by proofs.

Every `Model/Theorem.lean` ends with `#foundationsModelClosure` (`Foundations/Meta/ModelClosure.lean`),
which fails the build if the statement reaches a definition — or a proof inside a definition —
outside `Model/` and the area preludes.  `Convex` does not depend on `MarkovChainTheory`.

## Convex (`ArlibCommunity.Foundations.Convex`)

| Theorem | Surface statement |
| --- | --- |
| `PrekopaLeindler` | the Prékopa–Leindler inequality on `ℝⁿ` |
| `BrunnMinkowski` | the sharp Brunn–Minkowski inequality, and Brunn's slice theorem |
| `Localization` | the Localization Lemma of Kannan–Lovász–Simonovits |
| `ConvexIsoperimetry` | three-set isoperimetry for a convex body |
| `CrossRatioIsoperimetry` | Lovász–Vempala's weighted cross-ratio isoperimetry |
| `GaussianIsoperimetry` | Cousins–Vempala's isoperimetry for Gaussian-restricted log-concave densities |
| `BoundaryLayer` | KLS97 Corollary 4.6 at the sharp order `√n` |

## Markov chain theory (`ArlibCommunity.Foundations.MarkovChainTheory`)

| Theorem | Surface statement |
| --- | --- |
| `Cheeger` | Cheeger's inequality `Φ²/2 ≤ gap ≤ 2Φ` |
| `ConductanceMixing` | the Lovász–Simonovits decay `√M (1 − φ²/2)^t` |
| `PointwiseMixing` | pointwise mixing from uniform minorisation; TV does not imply it |
| `HitAndRunMixing` | hit-and-run's conductance and mixing (Lovász–Vempala Theorems 4.2 and 1.1) |
| `BallWalkMixing` | mixing of the lazy ball walk on a polytope |
| `GaussianWalkConductance` | conductance of the Metropolis–Gaussian and speedy walks |

The walk theorems are stated for any Markov kernel whose step at every point is the walk's
explicit one-step law (defined in `Model/Prelude.lean`); each folder also proves that such a
kernel exists.
-/

import ArlibCommunity.Foundations.Convex.Basic.CrossRatio
import ArlibCommunity.Foundations.Convex.Basic.CrossRatioOneDim
import ArlibCommunity.Foundations.Convex.Basic.GaussianWeight
import ArlibCommunity.Foundations.Convex.Basic.IntervalReduction
import ArlibCommunity.Foundations.Convex.Basic.Isoperimetry
import ArlibCommunity.Foundations.Convex.Basic.LogConcave
import ArlibCommunity.Foundations.Convex.Basic.LogisticIso
import ArlibCommunity.Foundations.Convex.Basic.OneDimIsoperimetry
import ArlibCommunity.Foundations.Convex.Basic.Polytope
import ArlibCommunity.Foundations.Convex.Basic.Rejection
import ArlibCommunity.Foundations.Convex.Basic.TV
import ArlibCommunity.Foundations.Convex.Basic.UniformOn
import ArlibCommunity.Foundations.Convex.BoundaryLayer.Analysis.KLS97Sharp
import ArlibCommunity.Foundations.Convex.BoundaryLayer.Model.Theorem
import ArlibCommunity.Foundations.Convex.BrunnMinkowski.Analysis.BrunnSharp
import ArlibCommunity.Foundations.Convex.BrunnMinkowski.Model.Prelude
import ArlibCommunity.Foundations.Convex.BrunnMinkowski.Model.Theorem
import ArlibCommunity.Foundations.Convex.ConvexIsoperimetry.Analysis.DyerFrieze
import ArlibCommunity.Foundations.Convex.ConvexIsoperimetry.Analysis.IsoBall
import ArlibCommunity.Foundations.Convex.ConvexIsoperimetry.Model.Theorem
import ArlibCommunity.Foundations.Convex.CrossRatioIsoperimetry.Analysis.BrascampLieb1D
import ArlibCommunity.Foundations.Convex.CrossRatioIsoperimetry.Analysis.ChordContinuity
import ArlibCommunity.Foundations.Convex.CrossRatioIsoperimetry.Analysis.CrossRatioIsoBridge
import ArlibCommunity.Foundations.Convex.CrossRatioIsoperimetry.Analysis.IsoConcaveWeight
import ArlibCommunity.Foundations.Convex.CrossRatioIsoperimetry.Analysis.LovaszVempalaIso
import ArlibCommunity.Foundations.Convex.CrossRatioIsoperimetry.Analysis.WeightedIsoBook
import ArlibCommunity.Foundations.Convex.CrossRatioIsoperimetry.Model.Theorem
import ArlibCommunity.Foundations.Convex.GaussianIsoperimetry.Analysis.ConcaveProfileIso
import ArlibCommunity.Foundations.Convex.GaussianIsoperimetry.Analysis.CoolingVariance
import ArlibCommunity.Foundations.Convex.GaussianIsoperimetry.Analysis.IndicatorVariance
import ArlibCommunity.Foundations.Convex.GaussianIsoperimetry.Analysis.IsoEnlargeContinuous
import ArlibCommunity.Foundations.Convex.GaussianIsoperimetry.Analysis.IsoEnlargeMeasurable
import ArlibCommunity.Foundations.Convex.GaussianIsoperimetry.Analysis.IsoEnlargeSlack
import ArlibCommunity.Foundations.Convex.GaussianIsoperimetry.Analysis.IsoIndicator
import ArlibCommunity.Foundations.Convex.GaussianIsoperimetry.Analysis.IsoInnerRegular
import ArlibCommunity.Foundations.Convex.GaussianIsoperimetry.Analysis.IsoMeasurableUncond
import ArlibCommunity.Foundations.Convex.GaussianIsoperimetry.Analysis.IsoOpenClosed
import ArlibCommunity.Foundations.Convex.GaussianIsoperimetry.Analysis.IsoWeighted
import ArlibCommunity.Foundations.Convex.GaussianIsoperimetry.Analysis.KLS97Lemma38
import ArlibCommunity.Foundations.Convex.GaussianIsoperimetry.Analysis.OneDimSharp
import ArlibCommunity.Foundations.Convex.GaussianIsoperimetry.Analysis.SharpIsoperimetry
import ArlibCommunity.Foundations.Convex.GaussianIsoperimetry.Analysis.SharpIsoperimetryConcave
import ArlibCommunity.Foundations.Convex.GaussianIsoperimetry.Analysis.Unblock
import ArlibCommunity.Foundations.Convex.GaussianIsoperimetry.Analysis.ZLogconcave
import ArlibCommunity.Foundations.Convex.GaussianIsoperimetry.Model.Theorem
import ArlibCommunity.Foundations.Convex.Localization.Analysis.ConcaveSelection
import ArlibCommunity.Foundations.Convex.Localization.Analysis.HamSandwich
import ArlibCommunity.Foundations.Convex.Localization.Analysis.HlocFromLocalization
import ArlibCommunity.Foundations.Convex.Localization.Analysis.Localization
import ArlibCommunity.Foundations.Convex.Localization.Analysis.LocalizationAffine
import ArlibCommunity.Foundations.Convex.Localization.Analysis.LocalizationAssembly
import ArlibCommunity.Foundations.Convex.Localization.Analysis.LocalizationClosed
import ArlibCommunity.Foundations.Convex.Localization.Analysis.LocalizationLSC
import ArlibCommunity.Foundations.Convex.Localization.Analysis.LocalizationLemma
import ArlibCommunity.Foundations.Convex.Localization.Analysis.LocalizationLimit
import ArlibCommunity.Foundations.Convex.Localization.Analysis.LocalizationMeasurable
import ArlibCommunity.Foundations.Convex.Localization.Analysis.LocalizationNeedleInBody
import ArlibCommunity.Foundations.Convex.Localization.Analysis.LocalizationTransport
import ArlibCommunity.Foundations.Convex.Localization.Analysis.LocalizationTransverse
import ArlibCommunity.Foundations.Convex.Localization.Analysis.NeedleLimit
import ArlibCommunity.Foundations.Convex.Localization.Analysis.NeedleProfile
import ArlibCommunity.Foundations.Convex.Localization.Analysis.NeedleSlab
import ArlibCommunity.Foundations.Convex.Localization.Analysis.NeedleSlabAffine
import ArlibCommunity.Foundations.Convex.Localization.Analysis.NeedleSlabChain
import ArlibCommunity.Foundations.Convex.Localization.Analysis.OddMap
import ArlibCommunity.Foundations.Convex.Localization.Analysis.ProductLocalization
import ArlibCommunity.Foundations.Convex.Localization.Model.Theorem
import ArlibCommunity.Foundations.Convex.PrekopaLeindler.Analysis.PrekopaLeindler
import ArlibCommunity.Foundations.Convex.PrekopaLeindler.Analysis.PrekopaLeindlerN
import ArlibCommunity.Foundations.Convex.PrekopaLeindler.Model.Theorem
import ArlibCommunity.Foundations.Convex.Prelude
import ArlibCommunity.Foundations.MarkovChainTheory.BallWalkMixing.Analysis.BallWalk
import ArlibCommunity.Foundations.MarkovChainTheory.BallWalkMixing.Analysis.BallWalkConductance
import ArlibCommunity.Foundations.MarkovChainTheory.BallWalkMixing.Analysis.ConvexBodyMixing
import ArlibCommunity.Foundations.MarkovChainTheory.BallWalkMixing.Analysis.UnitBallMixing
import ArlibCommunity.Foundations.MarkovChainTheory.BallWalkMixing.Model.Prelude
import ArlibCommunity.Foundations.MarkovChainTheory.BallWalkMixing.Model.Theorem
import ArlibCommunity.Foundations.MarkovChainTheory.Basic.Conductance
import ArlibCommunity.Foundations.MarkovChainTheory.Basic.MixingFromConductance
import ArlibCommunity.Foundations.MarkovChainTheory.Basic.Warmness
import ArlibCommunity.Foundations.MarkovChainTheory.Cheeger.Analysis.Cheeger
import ArlibCommunity.Foundations.MarkovChainTheory.Cheeger.Model.Prelude
import ArlibCommunity.Foundations.MarkovChainTheory.Cheeger.Model.Theorem
import ArlibCommunity.Foundations.MarkovChainTheory.ConductanceMixing.Analysis.L2Mixing
import ArlibCommunity.Foundations.MarkovChainTheory.ConductanceMixing.Model.Prelude
import ArlibCommunity.Foundations.MarkovChainTheory.ConductanceMixing.Model.Theorem
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Analysis.EllGaussianFacts
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Analysis.EllLogConcave
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Analysis.EllMollifier
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Analysis.HoldingTime
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Analysis.LensHalfspace
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Analysis.LensMin
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Analysis.LensSharp
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Analysis.MarkedTimeChange
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Analysis.MetropolisConductance
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Analysis.MetropolisConductanceSharp
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Analysis.MetropolisGaussian
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Analysis.MetropolisIsoperimetry
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Analysis.MetropolisOverlapSqrt
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Analysis.OverlapPerPair
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Analysis.OverlapSqrt
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Analysis.SpeedyConductanceSharp
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Analysis.SpeedyGaussian
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Analysis.SpeedyGaussianConductance
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Analysis.SpeedyGaussianUncond
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Analysis.SpeedyOverlap
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Analysis.SpeedyWalk
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Analysis.StarPolar
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Analysis.TimeChange
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Analysis.TrajTransfer
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Analysis.WastedSteps
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Model.Prelude
import ArlibCommunity.Foundations.MarkovChainTheory.GaussianWalkConductance.Model.Theorem
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Analysis.ChordCompare
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Analysis.ConductanceToTV
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Analysis.HitAndRun
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Analysis.HitAndRunConductance
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Analysis.HitAndRunConductanceParam
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Analysis.HitAndRunConductanceRoutes
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Analysis.HitAndRunConductanceUncond
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Analysis.HitAndRunLem41Discharge
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Analysis.HitAndRunMixing
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Analysis.HitAndRunMixingUncond
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Analysis.HitAndRunOverlap
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Analysis.HitAndRunStep
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Analysis.HitAndRunUncond
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Analysis.PolytopeChord
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Analysis.PolytopeHitAndRunExecution
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Analysis.SphereCap
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Analysis.SphereCoord
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Analysis.StepLength
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Model.Prelude
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Model.Theorem
import ArlibCommunity.Foundations.MarkovChainTheory.PointwiseMixing.Analysis.PointwiseMixing
import ArlibCommunity.Foundations.MarkovChainTheory.PointwiseMixing.Analysis.PointwiseRoute
import ArlibCommunity.Foundations.MarkovChainTheory.PointwiseMixing.Model.Prelude
import ArlibCommunity.Foundations.MarkovChainTheory.PointwiseMixing.Model.Theorem
import ArlibCommunity.Foundations.MarkovChainTheory.Prelude
import ArlibCommunity.Foundations.Meta.ModelClosure
