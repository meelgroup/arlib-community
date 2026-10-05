import TvDomainReduction.Interface.Pseudocode

/-!
# The union bound over the `L` sparsification steps (main.tex:926)

Under the pseudocode's bottom-up law `Pseudocode.reduceLaw`, the event that *some*
product region failed to be a `(1 ± δ)` embedding of its candidate set — the
complement of arlib's `Reduction.Sparsifies δ` — has probability at most
`L · η'`, where `L = Region.steps` is the number of product regions.

The proof is an induction on the shared v-tree.  At a product region the law is
`bind` of the two children's laws with one `productCoreset` call, and the bound
is assembled by `toOuterMeasure_bind_le`: off the children's failure events the
region's own call fails only on `prior.bad`, whose mass `SparsifyPrior.bad_prob`
bounds by `η'` *for every candidate set*, hence conditionally on the history.
-/

set_option autoImplicit false

namespace TvDomainReduction.Analysis

open Arlib.Approximation
open Arlib.KnowledgeCompilation.Probabilistic

/-- INTERNAL: a `PMF` puts mass at most `1` on any set. -/
theorem toOuterMeasure_le_one {α : Type*} (p : PMF α) (s : Set α) : p.toOuterMeasure s ≤ 1 :=
  (MeasureTheory.measure_mono (Set.subset_univ s)).trans
    ((p.toOuterMeasure_apply_eq_one_iff _).2 (Set.subset_univ _)).le

/-- INTERNAL: the one-step form of a union bound for a `bind`: if the
continuation puts mass at most `c` on `s` from every point outside `A`, the
composite puts mass at most `P(A) + c` on `s`.
TEXLINE: main.tex:926 -/
theorem toOuterMeasure_bind_le {α β : Type*} (p : PMF α) (f : α → PMF β) (s : Set β)
    (A : Set α) (c : ENNReal) (hf : ∀ a, a ∉ A → (f a).toOuterMeasure s ≤ c) :
    (p.bind f).toOuterMeasure s ≤ p.toOuterMeasure A + c := by
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply]
  calc ∑' a, p a * (f a).toOuterMeasure s
      ≤ ∑' a, (A.indicator p a + p a * c) := by
        refine ENNReal.tsum_le_tsum fun a => ?_
        by_cases ha : a ∈ A
        · rw [Set.indicator_of_mem ha]
          calc p a * (f a).toOuterMeasure s ≤ p a * 1 :=
                mul_le_mul_right (toOuterMeasure_le_one (f a) s) _
            _ = p a := mul_one _
            _ ≤ p a + p a * c := le_self_add
        · rw [Set.indicator_of_notMem ha, zero_add]
          exact mul_le_mul_right (hf a ha) _
    _ = ∑' a, A.indicator p a + c := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- PAPER: main.tex:926 — "By the union bound over the `L` product-region
sparsification steps, all sparsification steps succeed with probability at least
`1 - Lη'`."  Here in its failure form: under the bottom-up law, the event that
some product region's stored set is not a `(1 ± δ)` embedding of its candidate set
has probability at most `steps · η'`. -/
theorem reduceLaw_not_sparsifies_le {δ η' : ℝ} (prior : TvDomainReduction.SparsifyPrior δ η') :
    ∀ {V : Vtree} {gP gQ : ℕ} (P : Circuit V gP) (Q : Circuit V gQ),
      (Pseudocode.reduceLaw prior P Q).toOuterMeasure {R | ¬ R.Sparsifies δ}
        ≤ ((pairRegion P Q).steps : ENNReal) * ENNReal.ofReal η' := by
  intro V gP gQ P
  revert gQ
  induction P with
  | leaf θP =>
      intro gQ Q
      cases Q with
      | leaf θQ =>
          rw [Pseudocode.reduceLaw_leaf, PMF.toOuterMeasure_pure_apply, if_neg]
          · exact zero_le
          · exact fun h => h trivial
  | @node Vl Vr gPl gPr gP lP rP cP ihl ihr =>
      intro gQ Q
      cases Q with
      | @node _ _ gQl gQr _ lQ rQ cQ =>
          rw [Pseudocode.reduceLaw_node]
          refine (toOuterMeasure_bind_le _ _ _ {Rl | ¬ Rl.Sparsifies δ}
            ((pairRegion rP rQ).steps * ENNReal.ofReal η' + ENNReal.ofReal η') ?_).trans ?_
          · intro Rl hRl
            simp only [Set.mem_ofPred_eq, not_not] at hRl
            refine (toOuterMeasure_bind_le _ _ _ {Rr | ¬ Rr.Sparsifies δ}
              (ENNReal.ofReal η') ?_).trans (add_le_add (ihr rQ) le_rfl)
            intro Rr hRr
            simp only [Set.mem_ofPred_eq, not_not] at hRr
            rw [Pseudocode.productCoreset, Pseudocode.sparsify]
            refine (le_of_eq (PMF.toOuterMeasure_map_apply ..)).trans ?_
            rw [PMF.toOuterMeasure_map_apply]
            refine (MeasureTheory.measure_mono ?_).trans
              (prior.bad_prob (Interface.candidates cP cQ Rl Rr))
            intro x hx
            by_contra hbad
            apply hx
            exact ⟨hRl, hRr, prior.embeds_of_not_bad _ x hbad⟩
          · refine (add_le_add (ihl lQ) le_rfl).trans (le_of_eq ?_)
            show _ = (((pairRegion lP lQ).steps + (pairRegion rP rQ).steps + 1 : ℕ) : ENNReal) * _
            push_cast
            ring

end TvDomainReduction.Analysis
