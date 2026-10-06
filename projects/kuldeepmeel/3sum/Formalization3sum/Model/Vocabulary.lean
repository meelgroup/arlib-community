import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt

/-!
# Sparse thin integer matrix product: vocabulary

Correspondence ledger: 01-intro.tex:88–90 gives `Input`, `magnitudeBound`, and
`wantedValue`, which uses Mathlib's matrix multiplication. 02-matrix.tex:101–125 gives `Term`; 04-general.tex:202–228 gives
`BoxSymbol`. The bounded word RAM and the algorithm's charges are specified in
`Operations` and `Program`, not here. The exponent witnessing `N^{O(1)}` is an
explicit uniform natural number; this is a statement decision.
-/

set_option autoImplicit false

namespace Formalization3sum.Model

/-! ## Vocabulary -/

/-- Integer inputs and distinct requested positions. -/
structure Input (N D : ℕ) where
  X : Matrix (Fin N) (Fin D) ℤ
  Y : Matrix (Fin D) (Fin N) ℤ
  W : Finset (Fin N × Fin N)

/-- The uniform polynomial magnitude condition for an input family. -/
def magnitudeBound {N D : ℕ} (B : ℕ) (a : Input N D) : Prop :=
  (∀ i k, Int.natAbs (a.X i k) ≤ N ^ B) ∧
  (∀ k j, Int.natAbs (a.Y k j) ≤ N ^ B)

/-- One of the ten Schönhage terms. -/
inductive Term where
  | P0
  | P (i j : Fin 3)
  deriving DecidableEq, Inhabited

/-- An output level is inner or carries two outer digits. -/
inductive OutputSymbol where
  | z0
  | zij (i j : Fin 3)
  deriving DecidableEq, Inhabited

/-- A box level is fixed to a term or ranges over all ten terms. -/
inductive BoxSymbol where
  | star
  | term (τ : Term)
  deriving DecidableEq, Inhabited

/-- The fixed branch pads the shared dimension to a power of four. -/
def paddedExponent (D : ℕ) : ℕ := Nat.clog 4 D

/-- The fixed-branch recursion depth `L = 21m`. -/
def fixedDepth (D : ℕ) : ℕ := 21 * paddedExponent D

/-- The fixed-branch switching order `t = ⌈m/9⌉`. -/
def fixedThreshold (D : ℕ) : ℕ := (paddedExponent D + 8) / 9

/-- The tile's combinatorial dimensions. -/
def blockRows (L m : ℕ) : ℕ := 3 ^ (L - m)
def innerSets (L m : ℕ) : ℕ := Nat.choose L m
def bandBlocks (L m : ℕ) : ℕ := Nat.sqrt (innerSets L m)

/-! ## The quantity -/

/-- The exact product entry requested at a position. -/
abbrev wantedValue {N D : ℕ} (a : Input N D) (p : Fin N × Fin N) : ℤ :=
  (a.X * a.Y) p.1 p.2

end Formalization3sum.Model
