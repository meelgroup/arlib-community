import Auditable.Model.Prelude

/-!
# lem:holes: a hit cell set forces many solutions

If the `m + 1` hashes `hs` hit every cell of `{0,1}^m` with a solution of `G`
(`holesWith G m hs`), then `2^m ≤ (m + 1) · |sol G|`, i.e. `|sol G| ≥ 2^m / (m + 1)`.
-/

set_option autoImplicit false

namespace Auditable.Analysis

open Auditable

/-- PAPER: finalaudit.tex:53-62 (lem:holes, "If `φ_holes^{F'}(m) = 1`, then
`|sol F'| ≥ 2^m / (m + 1)`"), stated without division: `2^m ≤ (m + 1) · |sol G|`.
Proof as in the paper: each cell `α` is sent to a solution `z` and an index `i` with
`hᵢ(z) = α`; the pair `(i, z)` determines `α`. -/
theorem holes_necessary {N : ℕ} (G : CNF N) (m : ℕ) (hs : Fin (m + 1) → AffHash N m)
    (h : holesWith G m hs) : 2 ^ m ≤ (m + 1) * solCount G := by
  choose z hz i hi using h
  let f : (Fin m → Bool) → Fin (m + 1) × {σ // σ ∈ sol G} := fun α =>
    (i α, ⟨z α, by simp [sol, hz α]⟩)
  have hf : Function.Injective f := by
    intro α β hαβ
    simp only [f, Prod.mk.injEq] at hαβ
    have hzz : z α = z β := congrArg Subtype.val hαβ.2
    rw [← hi α, ← hi β, hαβ.1, hzz]
  have := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_prod, solCount] using this

end Auditable.Analysis
