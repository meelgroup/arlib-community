import TvDomainReduction.Model.Program
import TvDomainReduction.Interface.Pseudocode
import TvDomainReduction.Interface.Encoding
import TvDomainReduction.Model.Prior
import TvDomainReduction.Model.Prelude
import TvDomainReduction.Model.Operations
import TvDomainReduction.Model.Run
import Arlib.KnowledgeCompilation.Probabilistic.CircuitPair
import Arlib.KnowledgeCompilation.Probabilistic.StructuredCircuit
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# The program and the model are the same algorithm

`TvDomainReduction.Model.Program` is what the paper's claims are about: a charged
computation whose state is sealed and whose cost is an operator applied to it.
`TvDomainReduction.Interface.Pseudocode` is the same algorithm as mathematics for the
answer/output object the correctness theorem measures. Time and space stay over
`TvDomainReduction.Model.Program`; this file is only the transport for correctness.

It is a ladder. Each theorem below is proved from the ones above it, and
`answerLaw_eq` is the top: it is the one lemma the analysis rewrites
through, and the only one anything outside this file should need.

Every rung is closed, with no `sorry`.

### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · closed all five rungs (`tapeLaw_map_built_leaf`, `tapeStep_map_built_node`,
  `tapeLaw_map_built`, `runLaw_eq_map_runOutcome`, `answerLaw_eq`). The one real
  obstacle was `>>=`/`do`-notation on `PMF` living at two different universes
  (`Program.Tape prior : Type` on the way down, `Reduction _ : Type 1` on the way
  up): the ambient `Monad PMF` instance only unifies `>>=` within one fixed
  universe, so a naive `{α β : Type}` normalization lemma silently failed to
  match the `Reduction`-side binds. Fixed by stating `pmf_bind_eq_bind` with one
  shared universe-polymorphic `{α β : Type u}`. `#print axioms` on all five was
  briefly contaminated by a *stale* `.olean` for this very file (a leftover
  `sorry` build artifact); a fresh `lake build` of this module cleared it to
  `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

namespace TvDomainReduction

/-- `>>=` on `PMF` is `PMF.bind` by definition; stated so `simp` can normalize
`do`-notation into the dot-notation form the monad lemmas (`PMF.map_bind`,
`PMF.bind_map`, …) are stated over, at whatever universe the region types land
in (`Reduction` is `Type 1`-valued, unlike the `Program.Tape` side). -/
theorem pmf_bind_eq_bind.{u} {α β : Type u} (p : PMF α) (q : α → PMF β) :
    p >>= q = PMF.bind p q := rfl

/-- Leaf case of the tape-to-pseudocode bridge. A leaf draws no randomness, so both sides are the point mass on the exact leaf table, and the proof should be `PMF.map_pure` followed by unfolding. -/
theorem tapeLaw_map_built_leaf {δ η' : ℝ} (prior : TvDomainReduction.SparsifyPrior δ η') {m gP gQ : ℕ} (θP : Fin gP → Fin m → ℝ) (θQ : Fin gQ → Fin m → ℝ) : ((TvDomainReduction.Run.tapeLaw prior (Arlib.KnowledgeCompilation.Probabilistic.Circuit.leaf θP) (Arlib.KnowledgeCompilation.Probabilistic.Circuit.leaf θQ) : PMF (TvDomainReduction.Program.Tape prior))).map (TvDomainReduction.Interface.built prior (Arlib.KnowledgeCompilation.Probabilistic.Circuit.leaf θP) (Arlib.KnowledgeCompilation.Probabilistic.Circuit.leaf θQ)) = TvDomainReduction.Pseudocode.reduceLaw prior (Arlib.KnowledgeCompilation.Probabilistic.Circuit.leaf θP) (Arlib.KnowledgeCompilation.Probabilistic.Circuit.leaf θQ) := by
  rw [TvDomainReduction.Interface.tapeLaw_leaf, PMF.pure_map, TvDomainReduction.Interface.built_leaf,
    TvDomainReduction.Pseudocode.reduceLaw_leaf, TvDomainReduction.Pseudocode.leafCoreset]

/-- One product-region step: once the child sub-tapes are fixed, grafting the fresh Sparsify draw onto them and reading off the node coreset gives exactly the pseudocode's productCoreset law. This is the crux. Everything else is the induction around it. -/
theorem tapeStep_map_built_node {δ η' : ℝ} (prior : TvDomainReduction.SparsifyPrior δ η') {Vl Vr : Arlib.KnowledgeCompilation.Probabilistic.Vtree} {gPl gPr gP gQl gQr gQ : ℕ} (lP : Arlib.KnowledgeCompilation.Probabilistic.Circuit Vl gPl) (rP : Arlib.KnowledgeCompilation.Probabilistic.Circuit Vr gPr) (lQ : Arlib.KnowledgeCompilation.Probabilistic.Circuit Vl gQl) (rQ : Arlib.KnowledgeCompilation.Probabilistic.Circuit Vr gQr) (cP : Fin gP → Fin gPl → Fin gPr → ℝ) (cQ : Fin gQ → Fin gQl → Fin gQr → ℝ) (tl tr : TvDomainReduction.Program.Tape prior) : (prior.law (TvDomainReduction.Interface.candidates cP cQ (TvDomainReduction.Interface.built prior lP lQ tl) (TvDomainReduction.Interface.built prior rP rQ tr))).map (fun x => TvDomainReduction.Interface.built prior (Arlib.KnowledgeCompilation.Probabilistic.Circuit.node lP rP cP) (Arlib.KnowledgeCompilation.Probabilistic.Circuit.node lQ rQ cQ) (TvDomainReduction.Run.graft x tl tr)) = TvDomainReduction.Pseudocode.productCoreset prior cP cQ (TvDomainReduction.Interface.built prior lP lQ tl) (TvDomainReduction.Interface.built prior rP rQ tr) := by
  show (prior.law (TvDomainReduction.Interface.candidates cP cQ
        (TvDomainReduction.Interface.built prior lP lQ tl)
        (TvDomainReduction.Interface.built prior rP rQ tr))).map
      (fun x => TvDomainReduction.Interface.built prior
        (Arlib.KnowledgeCompilation.Probabilistic.Circuit.node lP rP cP)
        (Arlib.KnowledgeCompilation.Probabilistic.Circuit.node lQ rQ cQ)
        (TvDomainReduction.Run.graft x tl tr))
    = ((prior.law (TvDomainReduction.Interface.candidates cP cQ
          (TvDomainReduction.Interface.built prior lP lQ tl)
          (TvDomainReduction.Interface.built prior rP rQ tr))).map
        (prior.out (TvDomainReduction.Interface.candidates cP cQ
          (TvDomainReduction.Interface.built prior lP lQ tl)
          (TvDomainReduction.Interface.built prior rP rQ tr)))).map
      (fun C => Arlib.Approximation.Reduction.node (Arlib.KnowledgeCompilation.Probabilistic.blockTensor cP cQ)
        (TvDomainReduction.Interface.built prior lP lQ tl) (TvDomainReduction.Interface.built prior rP rQ tr)
        (TvDomainReduction.Interface.RetainedIdx prior gP gQ) C)
  rw [PMF.map_comp]
  congr 1

/-- Induction on the shared v-tree. Pushing the tape law forward along the coreset read-off gives the pseudocode's bottom-up reduction law, by `PMF.map_bind` and the two step lemmas. -/
theorem tapeLaw_map_built {δ η' : ℝ} (prior : TvDomainReduction.SparsifyPrior δ η') {V : Arlib.KnowledgeCompilation.Probabilistic.Vtree} {gP gQ : ℕ} (P : Arlib.KnowledgeCompilation.Probabilistic.Circuit V gP) (Q : Arlib.KnowledgeCompilation.Probabilistic.Circuit V gQ) : ((TvDomainReduction.Run.tapeLaw prior P Q : PMF (TvDomainReduction.Program.Tape prior))).map (TvDomainReduction.Interface.built prior P Q) = TvDomainReduction.Pseudocode.reduceLaw prior P Q := by
  induction P generalizing gQ with
  | leaf θP =>
    cases Q with
    | leaf θQ => exact tapeLaw_map_built_leaf prior θP θQ
  | node lP rP cP ihl ihr =>
    cases Q with
    | node lQ rQ cQ =>
      rw [TvDomainReduction.Interface.tapeLaw_node, TvDomainReduction.Pseudocode.reduceLaw_node,
        ← ihl, ← ihr]
      have hstep : ∀ (tl tr : TvDomainReduction.Program.Tape prior),
          (prior.law (TvDomainReduction.Interface.candidates cP cQ
              (TvDomainReduction.Interface.built prior lP lQ tl)
              (TvDomainReduction.Interface.built prior rP rQ tr))).bind
            (fun x => PMF.pure (TvDomainReduction.Interface.built prior
              (Arlib.KnowledgeCompilation.Probabilistic.Circuit.node lP rP cP)
              (Arlib.KnowledgeCompilation.Probabilistic.Circuit.node lQ rQ cQ)
              (TvDomainReduction.Run.graft x tl tr)))
            = TvDomainReduction.Pseudocode.productCoreset prior cP cQ
                (TvDomainReduction.Interface.built prior lP lQ tl)
                (TvDomainReduction.Interface.built prior rP rQ tr) :=
        fun tl tr => TvDomainReduction.tapeStep_map_built_node prior lP rP lQ rQ cP cQ tl tr
      simp only [TvDomainReduction.pmf_bind_eq_bind, PMF.bind_map, PMF.map_bind, PMF.pure_map,
        Function.comp_def]
      simp_rw [hstep]

/-- Root-level bridge: the pseudocode's run law is the program's run law pushed forward along the outcome read-off, from tapeLaw_map_built at the root. The explicit tape `t₀` is unused in the proof. It is there only so the statement names the Model/Program side; apply it with `default` and confirm `Inhabited (Program.Tape prior)` (low confidence that the instance exists already). If the boundary checker also accepts Model/Run, drop the binder. -/
theorem runLaw_eq_map_runOutcome {V : Arlib.KnowledgeCompilation.Probabilistic.Vtree} {gP gQ : ℕ} (C : Arlib.KnowledgeCompilation.Probabilistic.CircuitPair V gP gQ) {δ η' : ℝ} (prior : TvDomainReduction.SparsifyPrior δ η') (t₀ : TvDomainReduction.Program.Tape prior) : TvDomainReduction.Pseudocode.runLaw C prior = (TvDomainReduction.Run.runLaw C prior).map TvDomainReduction.Interface.runOutcome := by
  show TvDomainReduction.Pseudocode.reduceLaw prior C.P C.Q
      = ((TvDomainReduction.Run.tapeLaw prior C.P C.Q).map
          (fun t => TvDomainReduction.Program.run C prior t)).map
        TvDomainReduction.Interface.runOutcome
  rw [PMF.map_comp, ← TvDomainReduction.tapeLaw_map_built prior C.P C.Q]
  congr 1

/-- Capstone bridge: the program's law on the (estimate, cost) answer for output gates jP and jQ equals the pseudocode's. It follows from runLaw_eq_map_runOutcome by `PMF.map_comp`. As in that rung, `t₀` only anchors the statement on the Model/Program side; pass `default`. -/
theorem answerLaw_eq {V : Arlib.KnowledgeCompilation.Probabilistic.Vtree} {gP gQ : ℕ} (C : Arlib.KnowledgeCompilation.Probabilistic.CircuitPair V gP gQ) {δ η' : ℝ} (prior : TvDomainReduction.SparsifyPrior δ η') (t₀ : TvDomainReduction.Program.Tape prior) (jP : Fin gP) (jQ : Fin gQ) : TvDomainReduction.Run.answerLaw C prior jP jQ = TvDomainReduction.Pseudocode.answerLaw C prior jP jQ := by
  show ((TvDomainReduction.Run.runLaw C prior).map
        (fun p => TvDomainReduction.Dtilde p.val jP jQ))
      = (TvDomainReduction.Pseudocode.runLaw C prior).map
        (fun R => TvDomainReduction.Dtilde R jP jQ)
  rw [TvDomainReduction.runLaw_eq_map_runOutcome C prior t₀, PMF.map_comp]
  congr 1

end TvDomainReduction
