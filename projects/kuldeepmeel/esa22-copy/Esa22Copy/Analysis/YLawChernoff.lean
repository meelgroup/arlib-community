import Esa22Copy.Analysis.Alg2
import Esa22Copy.Analysis.BernSubset
import Arlib.Probability.Chernoff
import Arlib.Probability.BinomialCount

/-!
# Chernoff tails for Algorithm 3's `|Y_{k,m}|`

By Claim cl:loop (esa22-final.tex:615-672) every distinct item of the stream is
in `Y_k` independently with probability `2^{-k}`, so `|Y_{k,m}|` is
`Binomial(F0, 2^{-k})` with mean `μ = F0 · 2^{-k}` (esa22-final.tex:690).  The
two tails the accuracy proof uses:

* `yLaw_card_ge_le` — upper tail at `thresh ≥ 2μ`: `Pr[|Y| ≥ thresh] ≤ e^{-thresh/6}`.
  (The paper writes `2e^{-9·thresh/20}` from `E|Y| ≤ thresh/4`, esa22-final.tex:732,
  but with `ℓ = ⌊log₂(4F0/thresh)⌋` the mean is in `[thresh/4, thresh/2)`; with
  `t = thresh/μ - 1 ≥ 1`, `t²μ/(2+t) ≥ (thresh/2)·(1/3)`.)
* `yLaw_card_dev_le` — two-sided: `Pr[|Y| ∉ [(1-ε)μ, (1+ε)μ]] ≤ 2e^{-ε²μ/3}`.

## How it is proved

1. Claim cl:loop as a law equality, `yLaw_eq_bs` (`BernSubset.lean`):
   `yLaw k A = bs k A.toFinset`.
2. `bs_eq_prodSpace` transports every event of `bs` to arlib's `prodSpace` over
   `Fin n → Bool` (i.i.d. coins), via `Arlib.Probability.Pr_prodSpace_filter_eq_pow`;
   then `Arlib.Probability.chernoff_upper` / `chernoff_two_sided` apply with
   `s = S`, success set `{true}`, `indicMean = |S| · 2^{-k}` (`indicMean_coin`).
-/

set_option autoImplicit false

noncomputable section

namespace Esa22Copy.Analysis.Alg2

open Arlib.Probability

variable {n : ℕ}

/-- The coordinate law of the coins: `true` w.p. `r`.
INTERNAL: arlib's `prodSpace` presentation of `bs`. -/
def coinMass (r : ℝ) : Fin n → Bool → ℝ := fun _ b => if b then r else 1 - r

/-- INTERNAL: `prodSpace` side condition. -/
theorem coinMass_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∀ j b, 0 ≤ coinMass (n := n) r j b := by
  intro j b; cases b <;> simp [coinMass] <;> linarith

/-- INTERNAL: `prodSpace` side condition. -/
theorem coinMass_sum (r : ℝ) : ∀ j, ∑ b, coinMass (n := n) r j b = 1 := by
  intro j; simp [coinMass]

/-- **`bs` is arlib's i.i.d. coin product**, read through `ω ↦ {j ∈ S | ω j}`: every event of
the Bernoulli subset has the same probability in `prodSpace`.
INTERNAL: the transport to `Arlib.Probability.chernoff_*`. -/
theorem bs_eq_prodSpace (d : ℕ) (S : Finset (Fin n)) (G : Finset (Finset (Fin n))) :
    (bs d S).toOuterMeasure (G : Set (Finset (Fin n))) =
      ENNReal.ofReal ((prodSpace (coinMass (half d)) (coinMass_nonneg (half_nonneg d) (half_le_one d))
        (coinMass_sum (half d))).toFinProb.Pr
          (Finset.univ.filter fun ω => S.filter (fun j => ω j = true) ∈ G)) := by
  set P := (prodSpace (coinMass (n := n) (half d)) (coinMass_nonneg (half_nonneg d) (half_le_one d))
        (coinMass_sum (half d))).toFinProb
  have hfib : ∀ U : Finset (Fin n), P.Pr (Finset.univ.filter fun ω => S.filter (fun j => ω j = true) = U)
      = bsMass (half d) S U := by
    intro U
    by_cases hU : U ⊆ S
    · rw [Pr_prodSpace_filter_eq_pow _ _ _ (fun b => b = true) hU (r := half d)]
      · simp [bsMass, hU]
      · intro j _
        rw [show (Finset.univ.filter fun b : Bool => b = true) = {true} by decide]
        simp [coinMass]
    · have : (Finset.univ.filter fun ω : P.Ω => S.filter (fun j => ω j = true) = U) = ∅ := by
        ext ω; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false]
        intro e; exact hU (e ▸ Finset.filter_subset _ _)
      rw [this]; simp [FinProb.Pr, bsMass, hU]
  rw [PMF.toOuterMeasure_apply_finset]
  simp only [bs_apply]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun U _ => bsMass_nonneg (half_nonneg d) (half_le_one d) S U)]
  congr 1
  rw [FinProb.Pr]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun ω : P.Ω => S.filter (fun j => ω j = true))
    (t := G) (fun ω hω => (Finset.mem_filter.1 hω).2)]
  refine Finset.sum_congr rfl fun U hU => ?_
  rw [← hfib U, FinProb.Pr]
  congr 1
  ext ω; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => ⟨h ▸ hU, h⟩, fun h => h.2⟩


theorem indicMean_coin (d : ℕ) (S : Finset (Fin n)) :
    indicMean (coinMass (n := n) (half d)) S (fun _ => ({true} : Finset Bool)) = S.card * half d := by
  simp [indicMean, coinMass]

/-- **Upper tail of `|Y_{k,m}|`** at a threshold at least twice its mean.
PAPER: esa22-final.tex:730-733 -/
theorem yLaw_card_ge_le (k thr : ℕ) (A : List (Fin n)) (hthr : 0 < thr)
    (hμ : 2 * ((A.toFinset.card : ℝ) * (2⁻¹ : ℝ) ^ k) ≤ thr) :
    (yLaw k A).toOuterMeasure {U | thr ≤ U.card}
      ≤ ENNReal.ofReal (Real.exp (-(thr : ℝ) / 6)) := by
  set S := A.toFinset
  have hset : {U : Finset (Fin n) | thr ≤ U.card} =
      ((Finset.univ.filter fun U : Finset (Fin n) => thr ≤ U.card : Finset _) : Set _) := by
    ext U; simp
  rw [yLaw_eq_bs, hset, bs_eq_prodSpace]
  apply ENNReal.ofReal_le_ofReal
  set h0 := coinMass_nonneg (n := n) (half_nonneg k) (half_le_one k)
  set h1 := coinMass_sum (n := n) (half k)
  set m := indicMean (coinMass (n := n) (half k)) S (fun _ => ({true} : Finset Bool)) with hm
  have hmv : m = S.card * half k := indicMean_coin k S
  have hmle : 2 * m ≤ thr := by rw [hmv]; exact hμ
  have hcount : ∀ ω : Fin n → Bool, (S.filter fun j => ω j = true).card =
      indicCount S (fun _ => ({true} : Finset Bool)) ω := by
    intro ω; simp [indicCount]
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ m by rw [hmv]; exact mul_nonneg (by positivity) (half_nonneg k))
    with hm0 | hm0
  · -- `μ = 0`: `S = ∅`, the count is `0 < thresh`
    have hS : S = ∅ := by
      rw [hmv] at hm0
      have : (S.card : ℝ) = 0 := by
        rcases mul_eq_zero.1 hm0.symm with h | h
        · exact h
        · exact absurd h (by unfold half; positivity)
      exact Finset.card_eq_zero.1 (by exact_mod_cast this)
    have : (Finset.univ.filter fun ω : Fin n → Bool =>
        S.filter (fun j => ω j = true) ∈ Finset.univ.filter fun U : Finset (Fin n) => thr ≤ U.card)
        = ∅ := by
      ext ω; simp [hS, Nat.pos_iff_ne_zero.1 hthr]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this ⊢
    rw [show (Finset.univ.filter fun ω : Fin n → Bool => thr ≤ (S.filter fun j => ω j = true).card)
      = ∅ by simpa using this]
    simp [FinProb.Pr]; positivity
  · set t : ℝ := thr / m - 1 with ht
    have hthrm : (thr : ℝ) = (1 + t) * m := by rw [ht]; field_simp; ring
    have ht1 : 1 ≤ t := by
      rw [ht, le_sub_iff_add_le, le_div_iff₀ hm0]; linarith
    have hev : (Finset.univ.filter fun ω : Fin n → Bool =>
        S.filter (fun j => ω j = true) ∈ Finset.univ.filter fun U : Finset (Fin n) => thr ≤ U.card)
        = Finset.univ.filter fun ω => (1 + t) * m ≤
            (indicCount S (fun _ => ({true} : Finset Bool)) ω : ℝ) := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← hcount, ← hthrm]
      exact_mod_cast Iff.rfl
    have hch := chernoff_upper (coinMass (n := n) (half k)) h0 h1 S
      (fun _ => ({true} : Finset Bool)) (t := t) (by linarith)
    rw [hev]
    refine hch.trans (Real.exp_le_exp.2 ?_)
    rw [← hm, div_le_div_iff₀ (by linarith) (by norm_num), neg_mul, neg_mul, neg_le_neg_iff,
      hthrm]
    nlinarith [mul_nonneg (mul_nonneg hm0.le (by linarith : (0:ℝ) ≤ 5 * t + 2))
      (by linarith : (0:ℝ) ≤ t - 1)]

/-- **Two-sided tail of `|Y_{k,m}|`** around its mean `μ = F0 · 2^{-k}`.
PAPER: esa22-final.tex:749-760 -/
theorem yLaw_card_dev_le (k : ℕ) (A : List (Fin n)) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (yLaw k A).toOuterMeasure
        {U | (U.card : ℝ) ∉ Set.Icc ((1 - ε) * ((A.toFinset.card : ℝ) * (2⁻¹ : ℝ) ^ k))
          ((1 + ε) * ((A.toFinset.card : ℝ) * (2⁻¹ : ℝ) ^ k))}
      ≤ ENNReal.ofReal (2 * Real.exp (-(ε ^ 2 * ((A.toFinset.card : ℝ) * (2⁻¹ : ℝ) ^ k)) / 3)) := by
  set S := A.toFinset
  set μ : ℝ := (S.card : ℝ) * (2⁻¹ : ℝ) ^ k
  have hset : {U : Finset (Fin n) | (U.card : ℝ) ∉ Set.Icc ((1 - ε) * μ) ((1 + ε) * μ)} =
      ((Finset.univ.filter fun U : Finset (Fin n) =>
        (U.card : ℝ) ∉ Set.Icc ((1 - ε) * μ) ((1 + ε) * μ) : Finset _) : Set _) := by
    ext U; simp
  rw [yLaw_eq_bs, hset, bs_eq_prodSpace]
  apply ENNReal.ofReal_le_ofReal
  set h0 := coinMass_nonneg (n := n) (half_nonneg k) (half_le_one k)
  set h1 := coinMass_sum (n := n) (half k)
  have hmv : indicMean (coinMass (n := n) (half k)) S (fun _ => ({true} : Finset Bool)) = μ :=
    indicMean_coin k S
  have hcount : ∀ ω : Fin n → Bool, (S.filter fun j => ω j = true).card =
      indicCount S (fun _ => ({true} : Finset Bool)) ω := by
    intro ω; simp [indicCount]
  have hev : (Finset.univ.filter fun ω : Fin n → Bool =>
      S.filter (fun j => ω j = true) ∈ Finset.univ.filter fun U : Finset (Fin n) =>
        (U.card : ℝ) ∉ Set.Icc ((1 - ε) * μ) ((1 + ε) * μ))
      = Finset.univ.filter fun ω => ε * μ <
          |(indicCount S (fun _ => ({true} : Finset Bool)) ω : ℝ) - μ| := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hcount, Set.mem_Icc, not_and_or,
      not_le, lt_abs]
    constructor
    · rintro (h | h)
      · right; linarith
      · left; linarith
    · rintro (h | h)
      · right; linarith
      · left; linarith
  have hch := chernoff_two_sided (coinMass (n := n) (half k)) h0 h1 S
    (fun _ => ({true} : Finset Bool)) hε0 hε1
  rw [hmv] at hch
  rw [hev]
  exact hch

end Esa22Copy.Analysis.Alg2

end
