/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Foundations.Convex.PrekopaLeindler.Analysis.PrekopaLeindlerN
import ArlibCommunity.Foundations.Meta.ModelClosure

/-!
# The Prékopa–Leindler inequality

For `0 < λ < 1` and integrable nonnegative `f, g, h` on `ℝⁿ` with `f(x)^λ g(y)^{1-λ} ≤ h(λx + (1-λ)y)`, the integrals satisfy `(∫f)^λ (∫g)^{1-λ} ≤ ∫h`.

The statements below mention only definitions from this theorem's `Model/` directory and the
area preludes; `#foundationsModelClosure` checks this.  Proofs are in `Analysis/`.
-/

open ArlibCommunity.Foundations.Convex

namespace ArlibCommunity.Foundations.Convex.PrekopaLeindler

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **The Prékopa–Leindler inequality on `ℝⁿ`.** -/
theorem prekopa_leindler {n : ℕ} {lam : ℝ} {f g h : (Fin n → ℝ) → ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hfm : Measurable f) (hgm : Measurable g) (hhm : Measurable h)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfi : Integrable f) (hgi : Integrable g) (hhi : Integrable h)
    (hyp : ∀ x y, f x ^ lam * g y ^ (1 - lam) ≤ h (lam • x + (1 - lam) • y)) :
    (∫ x, f x) ^ lam * (∫ x, g x) ^ (1 - lam) ≤ ∫ x, h x :=
  prekopa_leindler_pi hlam0 hlam1 hfm hgm hhm hf hg hfi hgi hhi hyp

#foundationsModelClosure prekopa_leindler
#print axioms prekopa_leindler

end ArlibCommunity.Foundations.Convex.PrekopaLeindler
