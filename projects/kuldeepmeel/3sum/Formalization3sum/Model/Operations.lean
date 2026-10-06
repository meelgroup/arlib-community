import Arlib.Computation.Std

/-!
# Charged word operations for the sparse product

Correspondence ledger:
* 01-intro.tex:88–90, “operations on O(log N)-bit integers” ->
  `Operations.Op` and `Operations.rate`. A charge is one arithmetic, comparison,
  allocation, load, or store instruction of Arlib's word RAM.
* 04-general.tex:269–283, 328–335, shared encodings and box tries ->
  compositions of `Operations.Op` charges in `Program`. Traversing a string or
  trie of length `L` needs charges for its individual word and memory operations;
  there is no unit-cost whole-string or whole-trie operation here.
* 02-matrix.tex:3, bounded word size -> a proof obligation for `Program` and
  `Analysis`. The paper does not prescribe an instruction-level trie or signed
  integer representation. This file adopts Arlib's word-RAM instruction set as
  a statement decision; realizing the paper's arithmetic and O(L) access claims
  with bounded words remains a model gap to be certified downstream.
* 04-general.tex:263–335, preprocessing and querying -> composite program
  steps, intentionally omitted from the operation type. Their costs must be
  obtained by composing primitive charges, including reading requested positions
  and writing their answers.

`Arlib.Computation.StdOp` counts sealed roster, random, and answer-register calls.
The paper's arithmetic and indexed memory accesses are instead the primitive
instructions of `Arlib.Computation.Op`. No matrix multiplication, encoding, box,
or query is admitted as one operation.
-/

set_option autoImplicit false

namespace Formalization3sum.Model.Operations

/-- The paper's charged primitive is an Arlib word-RAM instruction. -/
abbrev Op : Type := Arlib.Computation.Op

/-- Storage is counted in machine words. -/
abbrev Cell : Type := Arlib.Computation.Cell

/-- The unit-cost word RAM: each primitive instruction costs one operation. -/
abbrev rate : Arlib.Computation.Rate Op := Arlib.Computation.Rate.unit Op

end Formalization3sum.Model.Operations
