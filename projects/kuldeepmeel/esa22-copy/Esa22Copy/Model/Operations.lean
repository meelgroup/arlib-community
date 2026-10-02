import Arlib.Computation.Std

/-!
# Operations: the currency Algorithm 1 is charged in

**Arlib already has every primitive the paper uses**, so this file is an alias
layer over arlib's standard currency and declares no operation of its own.

Every line of Algorithm 1 (F0-Estimator, esa22-final.tex:422-445) is one of
arlib's sealed-carrier operations:

| paper line | arlib operation | opcode |
|---|---|---|
| 3: `X ← X \ {aᵢ}` | `Roster.erase` | `StdOp.roster .erase` |
| 4: with probability `p`, … | `Sampler.accept` on a `Block` | `StdOp.rand .accept` |
| 4: … `X ← X ∪ {aᵢ}` | `Roster.insert` | `StdOp.roster .insert` |
| 5, 8: `if \|X\| = thresh` | `Roster.cardEq` | `StdOp.roster .cardEq` |
| 6: throw away each element w.p. ½ | `Roster.filterErase` + `Coins.flip` | `.roster .erase`, `.rand .flip` |
| 7: `p ← p/2` | `Sampler.halve` | `StdOp.rand .halve` |
| 8: `Output ⊥` (and halting) | `Slot.fill`, `Slot.isEmpty` | `StdOp.slot .fill`, `.slot .test` |
| 11: `Output \|X\|/p` | `Roster.size`, `Sampler.inflate` | `.roster .size`, `.rand .inflate` |

**Storage.**  One storage kind, `Arlib.Computation.Cell.cell`: every element of
the sample `X` (a `Roster`) occupies one cell, through arlib's
`stdRosterCells`.  The sampler, the coins and the ⊥ register report no cells, so
the peak in this kind is the peak of `|X|` — exactly what the paper's space claim
counts (esa22-final.tex:507).  Bits are `cells · ⌈log₂ n⌉`, a conversion outside
the program; the level of `p` and the loop counter are not counted, as in the
paper.

No running-time claim is made by the paper, so no rate is exported.
-/

set_option autoImplicit false

namespace Esa22Copy.Model

namespace Operations

/-- The work currency: arlib's standard operations on rosters, randomness and
the answer register. -/
abbrev Op : Type := Arlib.Computation.StdOp

/-- The storage currency: one kind, a cell of the sample `X`. -/
abbrev Cell : Type := Arlib.Computation.Cell

end Operations

end Esa22Copy.Model
