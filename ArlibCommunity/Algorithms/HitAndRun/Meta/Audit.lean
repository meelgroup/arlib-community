/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
The whole-development checks, invoked where the whole development is in scope.

The import list below is every module of `HitAndRun/Analysis/` and `HitAndRun/Model/`, so
the surplus report sees every declaration.  Regenerate it when a module is added.
-/
import ArlibCommunity.Algorithms.HitAndRun.Meta.ModelClosure
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Accuracy
import ArlibCommunity.Algorithms.HitAndRun.Analysis.AuditCheck
import ArlibCommunity.Algorithms.HitAndRun.Analysis.ChordPoint
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Coupling
import ArlibCommunity.Algorithms.HitAndRun.Analysis.GaussianDirection
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Kernel
import ArlibCommunity.Algorithms.HitAndRun.Analysis.KernelTheorem
import ArlibCommunity.Algorithms.HitAndRun.Analysis.PseudocodeProof
import ArlibCommunity.Algorithms.HitAndRun.Analysis.QueryCount
import ArlibCommunity.Algorithms.HitAndRun.Analysis.ShortChord
import ArlibCommunity.Algorithms.HitAndRun.Analysis.StepCompare
import ArlibCommunity.Algorithms.HitAndRun.Analysis.StepLaw
import ArlibCommunity.Algorithms.HitAndRun.Analysis.TapeAlgorithm
import ArlibCommunity.Algorithms.HitAndRun.Analysis.TapeLaw
import ArlibCommunity.Algorithms.HitAndRun.Analysis.TapeMeasurability
import ArlibCommunity.Algorithms.HitAndRun.Analysis.TapeProgram
import ArlibCommunity.Algorithms.HitAndRun.Analysis.TheoremProof
import ArlibCommunity.Algorithms.HitAndRun.Analysis.WalkLaw
import ArlibCommunity.Algorithms.HitAndRun.Model.Operations
import ArlibCommunity.Algorithms.HitAndRun.Model.Prelude
import ArlibCommunity.Algorithms.HitAndRun.Model.ProblemSetting
import ArlibCommunity.Algorithms.HitAndRun.Model.Program
import ArlibCommunity.Algorithms.HitAndRun.Model.Run
import ArlibCommunity.Algorithms.HitAndRun.Model.Theorem

namespace ArlibCommunity.Algorithms.HitAndRun.Meta

-- The `*_ofTape` lemmas are the analysis's only view of the sealed oracle: they unfold
-- the private fields, so they must live in `Operations.lean` beside them.
#surplusIn ArlibCommunity.Algorithms.HitAndRun.Model from
  ArlibCommunity.Algorithms.HitAndRun.hitAndRun_correct
  ArlibCommunity.Algorithms.HitAndRun.hitAndRun_queries
  ArlibCommunity.Algorithms.HitAndRun.Model.Operations.ask_ofTape
  ArlibCommunity.Algorithms.HitAndRun.Model.Operations.drawGaussian_ofTape
  ArlibCommunity.Algorithms.HitAndRun.Model.Operations.drawUnit_ofTape

end ArlibCommunity.Algorithms.HitAndRun.Meta
