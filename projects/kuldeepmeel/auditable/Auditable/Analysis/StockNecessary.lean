import Auditable.Model.Prelude

/-!
# cl:stockup: isolating hashes bound the solution count

If every solution of `G` is the only solution in its cell under one of the `m` hashes
`hs` (`stockWith G m hs`, the isolation semantics), then `|sol G| ≤ m · 2^m`.
-/

set_option autoImplicit false

namespace Auditable.Analysis

open Auditable

/-- PAPER: stock.tex:20-30 (cl:stockup, "If `φ^F_stock(m) = 1`, then `|sol F| ≤ m · 2^m`").
Proof as in the paper: a solution `z` is sent to `(i, hᵢ(z))` for an isolating index `i`;
this map is injective on `sol G`. -/
theorem stock_necessary {N : ℕ} (G : CNF N) (m : ℕ) (hs : Fin m → AffHash N m)
    (h : stockWith G m hs) : solCount G ≤ m * 2 ^ m := by
  have h' : ∀ z : {σ // σ ∈ sol G}, ∃ i, ∀ z₂ : Assignment N, G.eval z₂ = true →
      z₂ ≠ z.1 → (hs i).apply z₂ ≠ (hs i).apply z.1 := fun z =>
    h z.1 (by simpa [sol] using z.2)
  choose i hi using h'
  let f : {σ // σ ∈ sol G} → Fin m × (Fin m → Bool) := fun z => (i z, (hs (i z)).apply z.1)
  have hf : Function.Injective f := by
    intro a b hab
    simp only [f, Prod.mk.injEq] at hab
    by_contra hne
    have hb : G.eval b.1 = true := by simpa [sol] using b.2
    exact hi a b.1 hb (fun e => hne (Subtype.ext e.symm)) (by rw [hab.2, hab.1])
  have := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_prod, solCount] using this

end Auditable.Analysis
