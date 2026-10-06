import Auditable.Model.Prior
import Auditable.Analysis.BrMomentBound
import Arlib.Probability.EvenMoment
import Arlib.Probability.FinProbProd
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic

/-!
# The Bellare–Rompel tail bound for `t`-wise independent indicators

prelim.tex:132-143 states, citing [BR1994] and without proof: for an even `t ≥ 4`
and `t`-wise independent random variables `Z₁, …, Z_k` with values in `[0, 1]`,
`Z = ∑ Zᵢ`, `μ = E[Z]`, and every `ε > 0`,
`Pr[|Z − μ| ≥ ε μ] ≤ 8 · ((t μ + t²) / (ε² μ²))^{t/2}`.
The proof of thm:intermediate (bgp.tex:178-187) uses it as "Proposition 2.2".

It is stated here in the form that proof needs, which is a special case:
the variables are indicators `Z i : Ω → Bool` with a common mean `p` on a finite
probability space `Ω` with the uniform distribution, so probabilities are counts
divided by `|Ω|`. For indicators, `t`-wise independence with mean `p` is exactly:
every set `T` of at most `t` indices is all-`true` on a `p ^ |T|` fraction of `Ω`
(the joint law of `t` indicators is fixed by its all-ones probabilities on subsets,
by inclusion–exclusion). `μ = |I| · p` is required to be positive, which the cited
statement assumes implicitly (its right-hand side divides by `μ`).

The paper does not prove the proposition, but it is proved here rather than assumed,
by the moment method. The proof shows the stronger bound with constant `1` in place of
`8` and does not use `t ≥ 4`:

* The indicators are moved onto arlib's uniform space `unifFinProb Ω` as a
  `KWiseIndep` `IsIndicatorFamily`. arlib's moment recursion
  `Arlib.Probability.Ex_centre_sum_pow_insert` and the per-index estimate
  `Arlib.Probability.abs_Ex_centre_pow_le` then give, by induction on the index set,
  `|E[(X − μ)^n]| ≤ brBd p |I| n` for every `n ≤ t` (the step is `brBd_step`).
* `brBd_le` (in `BrMomentBound.lean`) bounds the majorant:
  `brBd p k (2s) ≤ (2s · kp + (2s)²)^s`, so `E[(X − μ)^t] ≤ (tμ + t²)^{t/2}`.
* Markov's inequality for the even power `t` finishes the proof.

arlib's packaged bound `Arlib.Probability.Ex_sum_sub_mean_pow_le_bellareRompel` has base
`e · (3sμ + 4s²)` at `t = 2s`. That is too weak for the constant `8`, so it is not used.
-/

set_option autoImplicit false

namespace Auditable.Analysis

open Arlib.Probability

/-- **Bellare–Rompel tail bound** (indicator, uniform-space form): for an even `t ≥ 4`
and `t`-wise independent indicators `Z i`, `i ∈ I`, of common mean `p` on a finite
uniform space `Ω`, with `X = #{i ∈ I | Z i}` and `μ = |I| p > 0`,
`#{ω | |X ω − μ| ≥ ε μ} ≤ |Ω| · 8 · ((t μ + t²) / (ε² μ²))^{t/2}`.

PAPER: prelim.tex:132-143 (Proposition, used as "Proposition 2.2" at bgp.tex:178-187).
BORROWED: Bellare and Rompel, "Randomness-efficient oblivious sampling", FOCS 1994
(Lemma 2.3), cited in the paper as [BR1994]. The proof is given here, so it is not
carried in `Prior`; see the module docstring for the route. -/
theorem bellareRompel_tail (hprior : Prior) {Ω ι : Type} [Fintype Ω] (I : Finset ι)
    (Z : ι → Ω → Bool) (p : ℝ) (t : ℕ) (ht : 4 ≤ t) (htev : Even t)
    (hind : ∀ T ⊆ I, T.card ≤ t →
      ((Finset.univ.filter fun ω => ∀ i ∈ T, Z i ω = true).card : ℝ) =
        Fintype.card Ω * p ^ T.card)
    (hμ : 0 < (I.card : ℝ) * p) (ε : ℝ) (hε : 0 < ε) :
    ((Finset.univ.filter fun ω =>
        ε * (I.card * p) ≤ |((I.filter fun i => Z i ω = true).card : ℝ) - I.card * p|).card : ℝ)
      ≤ Fintype.card Ω *
        (8 * ((t * (I.card * p) + t ^ 2) / (ε ^ 2 * (I.card * p) ^ 2)) ^ (t / 2)) := by
  classical
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · simp [Finset.univ_eq_empty]
  set N : ℝ := (Fintype.card Ω : ℝ) with hN
  have hN0 : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  have hp0 : 0 < p := by
    refine lt_of_not_ge fun h => ?_
    have : (I.card : ℝ) * p ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    linarith
  -- `hind` as a sum of products of `0/1` indicators.
  have hcount : ∀ T ⊆ I, T.card ≤ t →
      ∑ ω, ∏ i ∈ T, (if Z i ω = true then (1 : ℝ) else 0) = N * p ^ T.card := by
    intro T hT hTc
    simp_rw [Finset.prod_boole, Finset.sum_boole]
    rw [← hind T hT hTc]
  have hp1 : p ≤ 1 := by
    obtain ⟨i, hi⟩ : I.Nonempty := by
      rw [← Finset.card_pos]
      refine Nat.pos_of_ne_zero fun h => ?_
      rw [h] at hμ
      simp at hμ
    have h1 := hcount {i} (by simpa using hi) (by simp; omega)
    have h2 : ∑ ω, ∏ j ∈ ({i} : Finset ι), (if Z j ω = true then (1 : ℝ) else 0) ≤ N := by
      rw [hN, ← Finset.card_univ, Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_le_sum fun ω _ => ?_
      simp only [Finset.prod_singleton]
      split_ifs <;> norm_num
    simp only [Finset.card_singleton, pow_one] at h1
    nlinarith
  -- The uniform space and the `0/1` indicators, in arlib's `FinProb` vocabulary.
  let P : FinProb := unifFinProb Ω
  let W : I → P.Ω → ℝ := fun i ω => if Z i.1 ω = true then 1 else 0
  have hEx : ∀ X : Ω → ℝ, P.Ex X = (∑ ω, X ω) / N := fun X => Ex_unifFinProb X
  have hprodW : ∀ (u : Finset I), u.card ≤ t →
      ∑ ω : Ω, ∏ i ∈ u, W i ω = N * p ^ u.card := by
    intro u hu
    have := hcount (u.map (Function.Embedding.subtype _)) (by
        intro x hx
        obtain ⟨y, _, rfl⟩ := Finset.mem_map.1 hx
        exact y.2) (by simpa using hu)
    rw [Finset.card_map] at this
    rw [← this]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Finset.prod_map]
    rfl
  have hmean : ∀ i : I, P.Ex (W i) = p := by
    intro i
    rw [hEx]
    have := hprodW {i} (by simp; omega)
    simp only [Finset.prod_singleton, Finset.card_singleton, pow_one] at this
    rw [this]
    field_simp
  have hZW : IsIndicatorFamily W := by
    intro i ω
    by_cases h : Z i.1 ω = true <;> simp [W, h]
  have hindW : KWiseIndep P t W := by
    intro u hu
    show P.Ex (fun ω => ∏ i ∈ u, W i ω) = ∏ i ∈ u, P.Ex (W i)
    rw [hEx, hprodW u hu, Finset.prod_congr rfl fun i _ => hmean i, Finset.prod_const]
    field_simp
  -- Per-index centred moments: `|E[(Zₐ - p)^j]| ≤ g(j)`.
  have hG : ∀ (a : I) (j : ℕ), |P.Ex (fun ω => centre W a ω ^ j)| ≤ brG p j := by
    intro a j
    rcases Nat.lt_or_ge j 2 with hj | hj
    · obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
      · have : (fun ω => centre W a ω ^ 0) = fun _ : P.Ω => (1 : ℝ) := by funext ω; simp
        rw [this, P.Ex_const]
        simp [brG]
      · have : (fun ω => centre W a ω ^ 1) = centre W a := funext fun ω => pow_one _
        rw [this, Ex_centre W a]
        simp [brG]
    · refine (abs_Ex_centre_pow_le hZW a hj).trans ?_
      rw [Ex_centre_sq hZW a, hmean a, brG, if_neg (by omega), if_neg (by omega)]
      nlinarith
  have hG0 : ∀ j, 0 ≤ brG p j := by
    intro j
    unfold brG
    split_ifs <;> linarith
  -- The moment induction over the index set, against the majorant `brBd`.
  have hmom : ∀ (u : Finset I) (n : ℕ), n ≤ t →
      |P.Ex (fun ω => (∑ i ∈ u, centre W i ω) ^ n)| ≤ brBd p u.card n := by
    intro u
    induction u using Finset.induction_on with
    | empty =>
      intro n _
      simp only [Finset.sum_empty, Finset.card_empty, brBd_zero]
      rw [P.Ex_const, abs_of_nonneg (pow_nonneg le_rfl n)]
    | @insert a u ha ih =>
      intro n hn
      rw [Ex_centre_sum_pow_insert hindW hZW ha hn, Finset.card_insert_of_notMem ha]
      refine (Finset.abs_sum_le_sum_abs _ _).trans
        (le_trans (Finset.sum_le_sum fun j hj => ?_) (brBd_step p hp0.le u.card n))
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n.choose j : ℝ))]
      have hjn : j ≤ n := by rw [Finset.mem_range] at hj; omega
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (hG a j) (ih (n - j) (by omega)) (abs_nonneg _) (hG0 j)) (by positivity)
  -- The centred sum over all of `I` is the deviation `X - μ` of the goal.
  obtain ⟨s, hs⟩ := htev
  set μ : ℝ := (I.card : ℝ) * p with hμdef
  set S : Ω → ℝ := fun ω => ((I.filter fun i => Z i ω = true).card : ℝ) - μ with hSdef
  have hS : ∀ ω, ∑ i ∈ (Finset.univ : Finset I), centre W i ω = S ω := by
    intro ω
    simp only [centre_apply, hmean, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_coe, nsmul_eq_mul, hSdef, hμdef]
    congr 1
    rw [Finset.sum_coe_sort I (fun i => if Z i ω = true then (1 : ℝ) else 0), Finset.sum_boole]
  set B : ℝ := ((t : ℝ) * μ + (t : ℝ) ^ 2) ^ s with hBdef
  have hmomS : ∑ ω, S ω ^ t ≤ N * B := by
    have h1 := hmom Finset.univ t le_rfl
    rw [Finset.card_univ, Fintype.card_coe] at h1
    have h2 := brBd_le p hp0.le I.card s
    rw [show s + s = 2 * s from by ring] at hs
    rw [hs] at h1
    have h3 : P.Ex (fun ω => (∑ i ∈ (Finset.univ : Finset I), centre W i ω) ^ (2 * s)) ≤ B := by
      refine (le_abs_self _).trans (h1.trans (h2.trans (le_of_eq ?_)))
      rw [hBdef, hs, hμdef]
      push_cast
      ring
    simp only [hS] at h3
    rw [hEx, div_le_iff₀ hN0] at h3
    rw [hs]
    linarith
  have htev' : Even t := ⟨s, hs⟩
  -- Markov's inequality for the even power `t`.
  have hεμ : 0 < ε * μ := mul_pos hε hμ
  have hmarkov : ((Finset.univ.filter fun ω => ε * μ ≤ |S ω|).card : ℝ) * (ε * μ) ^ t ≤
      ∑ ω, S ω ^ t := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    calc ∑ _ω ∈ Finset.univ.filter (fun ω => ε * μ ≤ |S ω|), (ε * μ) ^ t
        ≤ ∑ ω ∈ Finset.univ.filter (fun ω => ε * μ ≤ |S ω|), S ω ^ t := by
          refine Finset.sum_le_sum fun ω hω => ?_
          rw [Finset.mem_filter] at hω
          exact (pow_le_pow_left₀ hεμ.le hω.2 t).trans_eq (htev'.pow_abs _)
      _ ≤ ∑ ω, S ω ^ t :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun ω _ _ => htev'.pow_nonneg _
  have hD : 0 < (ε * μ) ^ t := pow_pos hεμ t
  have hE2 : (ε ^ 2 * μ ^ 2) ^ (t / 2) = (ε * μ) ^ t := by
    rw [show t / 2 = s from by omega, hs]
    ring
  have hB0 : 0 ≤ B := by positivity
  rw [div_pow, hE2]
  have hA : ((Finset.univ.filter fun ω => ε * μ ≤ |S ω|).card : ℝ) ≤ N * B / (ε * μ) ^ t := by
    rw [le_div_iff₀ hD]
    linarith
  have hfin : N * B / (ε * μ) ^ t ≤ N * (8 * (B / (ε * μ) ^ t)) := by
    have : 0 ≤ N * B / (ε * μ) ^ t := by positivity
    rw [mul_div_assoc] at this ⊢
    nlinarith
  rw [show t / 2 = s from by omega]
  exact hA.trans hfin

end Auditable.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · proved · moment method via arlib `Ex_centre_sum_pow_insert` + `brBd_le`; constant 1, no `t ≥ 4`; no `Prior` field needed
* r1 · stated · `bellareRompel_tail` as the cited [BR1994] bound; proposed as a `Prior` field
-/
