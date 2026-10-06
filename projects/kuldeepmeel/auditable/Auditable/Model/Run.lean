import Auditable.Model.Program
import Auditable.Meta.ModelClosure

/-!
# Where the randomness comes from: nowhere

Both `AFCounter` (Algorithm algo:pigeons) and `CountAuditor` (Algorithm
algo:lonely-audit) are deterministic. The paper draws hash functions at random
only inside the existence proofs used for completeness (lm:holesexist,
lm:stockexist: "`h_i ←R H(n, m, 2)`"); the algorithms receive their hashes from
exact oracles that return witnesses (`Model/Operations.lean`). So there is no
tape, no tape length to match against the input, and no output distribution.

Accordingly this file declares nothing. The theorem states every claim on the
single run of the charged programs of `Model/Program.lean`, reading its value with
`Charged.val` and its tally with `Charged.cost`; nothing in it is dressed as a
probability-1 event. The closure checks below confirm that the two programs
the theorem mentions unfold only into `Model/` and the admitted cost library.
-/

#modelClosure Auditable.Program.afCounter
#modelClosure Auditable.Program.countAuditor

/-! `EqualCellsCounter` (Algorithm algo:smallcells) is deterministic too: the
`h ←R H(n, m, n)` of thm:intermediate's proof is drawn only inside the existence
argument, and the program receives its hash from the exact oracle `cellsOracle`.
No tape. -/

#modelClosure Auditable.Program.equalCellsCounter

/-! `Stock` (Algorithm algo:stock) is deterministic too: the `h_i ←R H(n, m, 2)` of
lm:stockexist's proof is drawn only inside that existence argument, and the program
receives its hashes from the exact oracle `stockOracle`. No tape. -/

#modelClosure Auditable.Program.stockCounter
