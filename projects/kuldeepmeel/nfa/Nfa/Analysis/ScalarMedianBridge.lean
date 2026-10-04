import Nfa.Interface.Encoding
import Arlib.Probability.Median

/-!
# The program's median is the pseudocode's median

`Nfa.Model.Operations.Scalar.median` takes entry `⌊k/2⌋` of the merge-sorted list of
its `k` arguments; the pseudocode reads `Arlib.Probability.medianOf`, the value at
sorted position `⌊k/2⌋` via `Tuple.sort`.  `scalarMedian_real_eq_medianOf` says the
two agree on a list `(List.range n).map y`, read as reals.  Both bridges that take a
median — eAS.5 line:median (`estimateAndSample_bridge`) and countNFA.14
(`countNFA_bridge`) — rewrite through it.
-/

set_option autoImplicit false

namespace Nfa.Analysis

/-- The program's order-statistic median of the scalars `y 0, …, y (n-1)`, read as a
real, is `Arlib.Probability.medianOf` of the same values.

INTERNAL: representation bridge between `Scalar.median` (merge sort over `ℚ`) and
`medianOf` (`Tuple.sort` over `ℝ`); both are the `⌊n/2⌋`-th order statistic.
TEXLINE: algorithm.tex:64-84 -/
theorem scalarMedian_real_eq_medianOf (n : ℕ) (y : ℕ → Nfa.Model.Operations.Scalar) :
    Nfa.Interface.real (Nfa.Model.Operations.Scalar.median ((List.range n).map y)).val
      = Arlib.Probability.medianOf (fun b : Fin n => Nfa.Interface.real (y b)) := by
  set v : Fin n → ℝ := fun b => Nfa.Interface.real (y b) with hv
  set M : List ℚ := ((List.range n).map y |>.map Nfa.Model.Operations.Scalar.get).mergeSort
    (fun a b => decide (a ≤ b)) with hM
  -- the merge-sorted list, cast to `ℝ`, is `v ∘ Tuple.sort v` written out
  have hsorted : (M.map (fun x : ℚ => (x : ℝ))) = List.ofFn (v ∘ Tuple.sort v) := by
    refine List.Perm.eq_of_pairwise' (r := (· ≤ ·)) ?_ ?_ ?_
    · have h := List.pairwise_mergeSort (le := fun a b : ℚ => decide (a ≤ b))
        (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; exact le_trans hab hbc)
        (fun a b => by simpa using le_total a b)
        ((List.range n).map y |>.map Nfa.Model.Operations.Scalar.get)
      rw [List.pairwise_map]
      exact h.imp fun hab => by simpa using hab
    · exact (Tuple.monotone_sort v).sortedLE_ofFn.pairwise
    · refine ((List.mergeSort_perm _ _).map _).trans ?_
      refine List.Perm.trans ?_ ((Tuple.sort v).ofFn_comp_perm v).symm
      rw [List.map_map, List.map_map]
      apply List.Perm.of_eq
      apply List.ext_getElem (by simp)
      intro k h1 h2
      simp [hv, Nfa.Interface.real]
  have hlen : M.length = n := by simp [hM, List.length_mergeSort]
  unfold Arlib.Probability.medianOf
  split_ifs with hn
  · have hk : n / 2 < M.length := by rw [hlen]; exact Nat.div_lt_self hn one_lt_two
    have := congrArg (fun l => l[n / 2]?) hsorted
    simp only [List.getElem?_map, List.getElem?_ofFn, List.getElem?_eq_getElem hk] at this
    rw [Nfa.Interface.real, Nfa.Interface.get_val_median, List.length_map, List.length_range]
    rw [List.getD_eq_getElem?_getD, ← hM, List.getElem?_eq_getElem hk]
    simp only [Option.getD_some]
    simpa [Fin.ofNat, Nat.div_lt_self hn one_lt_two] using this
  · have : n = 0 := by omega
    subst this
    simp [Nfa.Interface.real, Nfa.Interface.get_val_median]

end Nfa.Analysis
