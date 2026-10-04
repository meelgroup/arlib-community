import Nfa.Analysis.TimeBudget
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# From the step budget to the theorem's bound

`countBound m n W P` (see `Nfa.Analysis.TimeBudget`) is `m` times a bound on the
steps of `countNFA`.  At the paper's parameters `P = params A n ε δ`
(algorithm.tex:92), with `W = max 1 (MM m) = MM m` and `m² ≤ MM m`, it is at most
`m · C · n² · MM(m) · log(16(n+1)m) · ε⁻² · (1−ε)⁻¹ · ⌈8 ln(1/δ)⌉` for one absolute
constant `C`.  The ingredients: `β ≤ 64n/(ε²(1−ε)) + 1`,
`γ ≤ 5 log(16|Q^u|) + 1` with `|Q^u| ≤ (n+1)m`, `θ ≤ 16α(1+ε)|Q^u| + 1`,
`log(16(n+1)m) ≥ 1 − 1/32` (from `log x ≥ 1 − 1/x`), and `m ≤ m² ≤ MM m`;
`countBound_poly` then bounds every monomial, giving `C = 10⁶`.
-/

set_option autoImplicit false

namespace Nfa.Analysis

/-- INTERNAL: the polynomial estimate behind `countBound_le_target`, over real stand-ins
for `m, n, MM m, ε⁻²(1−ε)⁻¹, log(16(n+1)m), α, γ, θ, μ`: each monomial of
`countBound` is at most a constant times `μ · m · n² · MM m · L · K`.
TEXLINE: analysis.tex:67-68 -/
theorem countBound_poly (x y w K L a g t u : ℝ) (hmR : 1 ≤ x) (hnR : 1 ≤ y) (hW2 : x ^ 2 ≤ w)
    (hmW : x ≤ w) (hK1 : 1 ≤ K) (hL1 : 1 / 2 ≤ L) (hγ : g ≤ 7 * L)
    (hα : a ≤ 455 * y * K * L) (hθ : t ≤ 64 * a * y * x + 1) (hμ : 1 ≤ u)
    (ha0 : 0 ≤ a) (hg0 : 0 ≤ g) (ht0 : 0 ≤ t) :
    x * (2 * y * x ^ 2 + x) +
        u * (x * (6 + 2 * a + (y + 1) * x * a) +
              y * (2 * x + 2 * w * x + x ^ 2 * (4 * x + (3 * (a + g) + 2 * a + 12) + 1)) +
            (14 * x ^ 2 + 2 * w + x * (x + 2)) * (t + a) + x) + x ≤
      1000000 * u * (x * (y ^ 2 * w * L * K)) := by
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hw1 : 1 ≤ w := hmR.trans hmW
  have hw0 : 0 ≤ w := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hyK : 1 ≤ y * K := one_le_mul_of_one_le_of_one_le hnR hK1
  obtain ⟨N, hNdef⟩ : ∃ N, N = y * K * L := ⟨_, rfl⟩
  obtain ⟨V, hVdef⟩ : ∃ V, V = y ^ 2 * w * L * K := ⟨_, rfl⟩
  have hVN : V = y * w * N := by rw [hVdef, hNdef]; ring
  have hLN : L ≤ N := by rw [hNdef]; exact le_mul_of_one_le_left hL0 hyK
  have hN : 1 ≤ 2 * N := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hyw : 1 ≤ y * w := one_le_mul_of_one_le_of_one_le hnR hw1
  have hNV : N ≤ V := by rw [hVN]; exact le_mul_of_one_le_left hN0 hyw
  have hV1 : 1 ≤ 2 * V := by linarith
  have hV0 : 0 ≤ V := by linarith
  have hywV : y * w ≤ 2 * V := by
    have := le_mul_of_one_le_right (by linarith : (0 : ℝ) ≤ y * w) hN
    rw [hVN]; linarith
  have hwy : w ≤ y * w := le_mul_of_one_le_left hw0 hnR
  have hyw' : y ≤ y * w := le_mul_of_one_le_right hy0 hw1
  have hwV : w ≤ 2 * V := by linarith
  have hyV : y ≤ 2 * V := by linarith
  have hx2w : x ^ 2 ≤ x * w := by
    have := mul_le_mul_of_nonneg_left hmW hx0
    nlinarith
  have hx3 : x ^ 3 ≤ x * w := by
    have := mul_le_mul_of_nonneg_left hW2 hx0
    calc x ^ 3 = x * x ^ 2 := by ring
      _ ≤ x * w := this
  have haN : a ≤ 455 * N := by rw [hNdef]; linarith
  have hxV : 0 ≤ x * V := mul_nonneg hx0 hV0
  -- the pieces of one core run
  have p1 : x * (6 + 2 * a + (y + 1) * x * a) ≤ 1832 * (x * V) := by
    have q1 : x * 6 ≤ x * (12 * V) := mul_le_mul_of_nonneg_left (by linarith) hx0
    have q2 : x * (2 * a) ≤ x * (910 * V) := mul_le_mul_of_nonneg_left (by linarith) hx0
    have q3 : (y + 1) * x * x * a ≤ 910 * (x * V) := by
      calc (y + 1) * x * x * a ≤ (2 * y) * x * w * (455 * N) := by gcongr; linarith
        _ = 910 * (x * (y * w * N)) := by ring
        _ = 910 * (x * V) := by rw [hVN]
    calc x * (6 + 2 * a + (y + 1) * x * a)
        = x * 6 + x * (2 * a) + (y + 1) * x * x * a := by ring
      _ ≤ x * (12 * V) + x * (910 * V) + 910 * (x * V) := add_le_add (add_le_add q1 q2) q3
      _ = 1832 * (x * V) := by ring
  have p2 : y * (2 * x + 2 * w * x + x ^ 2 * (4 * x + (3 * (a + g) + 2 * a + 12) + 1)) ≤
      2338 * (x * V) := by
    have q1 : y * (2 * x) ≤ 4 * (x * V) := by
      have := mul_le_mul_of_nonneg_left hyV hx0
      calc y * (2 * x) = 2 * (x * y) := by ring
        _ ≤ 2 * (x * (2 * V)) := by linarith
        _ = 4 * (x * V) := by ring
    have q2 : y * (2 * w * x) ≤ 4 * (x * V) := by
      have := mul_le_mul_of_nonneg_left hywV hx0
      calc y * (2 * w * x) = 2 * (x * (y * w)) := by ring
        _ ≤ 2 * (x * (2 * V)) := by linarith
        _ = 4 * (x * V) := by ring
    have q3 : y * (x ^ 2 * (4 * x)) ≤ 8 * (x * V) := by
      have h1 := mul_le_mul_of_nonneg_left hx3 hy0
      have h2 := mul_le_mul_of_nonneg_left hywV hx0
      calc y * (x ^ 2 * (4 * x)) = 4 * (y * x ^ 3) := by ring
        _ ≤ 4 * (y * (x * w)) := by linarith
        _ = 4 * (x * (y * w)) := by ring
        _ ≤ 4 * (x * (2 * V)) := by linarith
        _ = 8 * (x * V) := by ring
    have hF : 5 * a + 3 * g + 13 ≤ 2322 * N := by linarith
    have q4 : y * (x ^ 2 * (5 * a + 3 * g + 13)) ≤ 2322 * (x * V) := by
      calc y * (x ^ 2 * (5 * a + 3 * g + 13)) ≤ y * ((x * w) * (2322 * N)) := by
            gcongr
        _ = 2322 * (x * (y * w * N)) := by ring
        _ = 2322 * (x * V) := by rw [hVN]
    calc y * (2 * x + 2 * w * x + x ^ 2 * (4 * x + (3 * (a + g) + 2 * a + 12) + 1))
        = y * (2 * x) + y * (2 * w * x) + y * (x ^ 2 * (4 * x)) +
            y * (x ^ 2 * (5 * a + 3 * g + 13)) := by ring
      _ ≤ 4 * (x * V) + 4 * (x * V) + 8 * (x * V) + 2322 * (x * V) :=
          add_le_add (add_le_add (add_le_add q1 q2) q3) q4
      _ = 2338 * (x * V) := by ring
  have p3 : (14 * x ^ 2 + 2 * w + x * (x + 2)) * (t + a) ≤ 561963 * (x * V) := by
    have hc : 14 * x ^ 2 + 2 * w + x * (x + 2) ≤ 19 * w := by
      have : x * 2 ≤ w * 2 := by linarith
      have : x ^ 2 ≤ w := hW2
      nlinarith
    have hta : t + a ≤ 29120 * (N * y * x) + 1 + 455 * N := by
      have h1 : 64 * a * y * x ≤ 64 * (455 * N) * y * x := by gcongr
      linarith
    have e1 : w * (N * y * x) = x * V := by rw [hVN]; ring
    have e2 : w * N ≤ x * V := by
      have : w * N ≤ y * w * N := by
        have := mul_le_mul_of_nonneg_right hwy hN0; linarith
      have h2 : V ≤ x * V := le_mul_of_one_le_left hV0 hmR
      rw [← hVN] at this; linarith
    have e3 : w ≤ 2 * (x * V) := by
      have h2 : V ≤ x * V := le_mul_of_one_le_left hV0 hmR
      linarith
    have hta0 : 0 ≤ t + a := by linarith
    calc (14 * x ^ 2 + 2 * w + x * (x + 2)) * (t + a)
        ≤ (19 * w) * (t + a) := mul_le_mul_of_nonneg_right hc hta0
      _ ≤ (19 * w) * (29120 * (N * y * x) + 1 + 455 * N) :=
          mul_le_mul_of_nonneg_left hta (by linarith)
      _ = 19 * (29120 * (w * (N * y * x)) + w + 455 * (w * N)) := by ring
      _ ≤ 19 * (29120 * (x * V) + 2 * (x * V) + 455 * (x * V)) := by
          rw [e1]; linarith
      _ = 561963 * (x * V) := by ring
  have p4 : x ≤ 2 * (x * V) := by
    have := mul_le_mul_of_nonneg_left hV1 hx0; linarith
  have hinner : x * (6 + 2 * a + (y + 1) * x * a) +
        y * (2 * x + 2 * w * x + x ^ 2 * (4 * x + (3 * (a + g) + 2 * a + 12) + 1)) +
        (14 * x ^ 2 + 2 * w + x * (x + 2)) * (t + a) + x ≤ 566135 * (x * V) := by
    linarith
  have hT1 : x * (2 * y * x ^ 2 + x) ≤ 6 * (x * V) := by
    have h1 := mul_le_mul_of_nonneg_left hx3 hy0
    have h2 := mul_le_mul_of_nonneg_left hywV hx0
    have h3 := mul_le_mul_of_nonneg_left hmW hx0
    have h4 : x * w ≤ x * (2 * V) := mul_le_mul_of_nonneg_left hwV hx0
    calc x * (2 * y * x ^ 2 + x) = 2 * (y * x ^ 3) + x * x := by ring
      _ ≤ 2 * (y * (x * w)) + x * w := by linarith
      _ = 2 * (x * (y * w)) + x * w := by ring
      _ ≤ 2 * (x * (2 * V)) + x * (2 * V) := by linarith
      _ = 6 * (x * V) := by ring
  have hu := mul_le_mul_of_nonneg_left hinner (by linarith : (0 : ℝ) ≤ u)
  have hux : x * V ≤ u * (x * V) := le_mul_of_one_le_left hxV hμ
  rw [← hVdef]
  calc x * (2 * y * x ^ 2 + x) +
        u * (x * (6 + 2 * a + (y + 1) * x * a) +
          y * (2 * x + 2 * w * x + x ^ 2 * (4 * x + (3 * (a + g) + 2 * a + 12) + 1)) +
          (14 * x ^ 2 + 2 * w + x * (x + 2)) * (t + a) + x) + x
      ≤ 6 * (x * V) + u * (566135 * (x * V)) + 2 * (x * V) := by linarith
    _ ≤ 1000000 * u * (x * V) := by nlinarith

/-- INTERNAL: **the arithmetic of the running-time bound**: at the paper's
parameters, the natural-number budget `countBound` is at most `m` times the
theorem's bound, for one absolute constant `C`.
TEXLINE: analysis.tex:67-68 -/
theorem countBound_le_target : ∃ C : ℝ, ∀ (Q : Type) [Fintype Q] (A : PaperNFA Q)
    (n : ℕ) (ε δ : ℝ) (MM : ℕ → ℕ), 1 ≤ n → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
    (∀ m, m ^ 2 ≤ MM m) → (∀ m, MM m ≤ m ^ 3) →
    (countBound (Fintype.card Q) n (max 1 (MM (Fintype.card Q))) (params A n ε δ) : ℝ) ≤
      (Fintype.card Q : ℝ) *
        (C * (n : ℝ) ^ 2 * (MM (Fintype.card Q) : ℝ) *
          Real.log (16 * ((n : ℝ) + 1) * (Fintype.card Q : ℝ)) *
          (ε ^ 2)⁻¹ * (1 - ε)⁻¹ * (⌈8 * Real.log (1 / δ)⌉₊ : ℝ)) := by
  -- K = ε⁻²(1−ε)⁻¹ ≥ 1, L = log(16(n+1)m) ≥ 31/32 (from `log x ≥ 1 − 1/x`), W = MM m ≥ m²:
  -- β ≤ 65nK, γ ≤ 7L, α ≤ 455nKL, θ ≤ 64αnm + 1, and `countBound_poly` does the rest.
  refine ⟨1000000, ?_⟩
  intro Q _ A n ε δ MM hn hε0 hε1 hδ0 hδ1 hlo _hhi
  have hm : 1 ≤ Fintype.card Q := Fintype.card_pos_iff.2 ⟨A.qI⟩
  have hW : max 1 (MM (Fintype.card Q)) = MM (Fintype.card Q) :=
    max_eq_right ((Nat.one_le_pow _ _ hm).trans (hlo _))
  rw [hW]
  set m := Fintype.card Q with hmdef
  set P := params A n ε δ with hP
  -- the real quantities
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hW2 : (m : ℝ) ^ 2 ≤ MM m := by exact_mod_cast hlo m
  have hmW : (m : ℝ) ≤ MM m := by nlinarith
  set K := (ε ^ 2)⁻¹ * (1 - ε)⁻¹ with hK
  have hK1 : 1 ≤ K := by
    have h1 : 1 ≤ (ε ^ 2)⁻¹ := one_le_inv₀ (by positivity) |>.2 (by nlinarith)
    have h2 : 1 ≤ (1 - ε)⁻¹ := one_le_inv₀ (by linarith) |>.2 (by linarith)
    nlinarith
  set L := Real.log (16 * ((n : ℝ) + 1) * (m : ℝ)) with hL
  have hx : (32 : ℝ) ≤ 16 * ((n : ℝ) + 1) * (m : ℝ) := by nlinarith
  have hL1 : (1 : ℝ) / 2 ≤ L := by
    have hxpos : (0 : ℝ) < 16 * ((n : ℝ) + 1) * (m : ℝ) := by linarith
    have := Real.log_le_sub_one_of_pos (inv_pos.2 hxpos)
    rw [Real.log_inv] at this
    have hinv : (16 * ((n : ℝ) + 1) * (m : ℝ))⁻¹ ≤ 1 / 32 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hx
    linarith
  -- |Q^u| ≤ (n+1) m
  have hQu : (A.unrolledCard n : ℝ) ≤ ((n : ℝ) + 1) * m := by
    have : A.unrolledCard n ≤ (n + 1) * m := by
      unfold PaperNFA.unrolledCard
      calc ∑ ℓ ∈ Finset.range (n + 1), (A.layer ℓ).ncard
          ≤ ∑ ℓ ∈ Finset.range (n + 1), m := by
            refine Finset.sum_le_sum fun ℓ _ => ?_
            have := Set.ncard_le_card (A.layer ℓ)
            rwa [Nat.card_eq_fintype_card] at this
        _ = (n + 1) * m := by simp
    exact_mod_cast this
  -- the parameters
  have hβ : (P.β : ℝ) ≤ 65 * n * K := by
    have h0 : (0 : ℝ) ≤ 64 * (n : ℝ) / (ε ^ 2 * (1 - ε)) := by
      have : 0 < 1 - ε := by linarith
      positivity
    have h1 := Nat.ceil_lt_add_one h0
    have h2 : 64 * (n : ℝ) / (ε ^ 2 * (1 - ε)) = 64 * n * K := by
      rw [hK, div_eq_mul_inv, mul_inv]
    have h3 : (1 : ℝ) ≤ n * K := by nlinarith
    show ((⌈64 * (n : ℝ) / (ε ^ 2 * (1 - ε))⌉₊ : ℕ) : ℝ) ≤ 65 * n * K
    linarith
  have hγ : (P.γ : ℝ) ≤ 7 * L := by
    show ((⌈5 * Real.log (16 * (A.unrolledCard n : ℝ))⌉₊ : ℕ) : ℝ) ≤ 7 * L
    have hlog : Real.log (16 * (A.unrolledCard n : ℝ)) ≤ L := by
      rcases Nat.eq_zero_or_pos (A.unrolledCard n) with h | h
      · rw [h]; simp; linarith
      · apply Real.log_le_log (by positivity)
        nlinarith
    have hlog0 : 0 ≤ Real.log (16 * (A.unrolledCard n : ℝ)) := by
      rcases Nat.eq_zero_or_pos (A.unrolledCard n) with h | h
      · rw [h]; simp
      · apply Real.log_nonneg
        have : (1 : ℝ) ≤ A.unrolledCard n := by exact_mod_cast h
        linarith
    have h1 := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 5 * Real.log (16 * (A.unrolledCard n : ℝ)) by
      linarith)
    linarith
  have hαβγ : (P.α : ℝ) = P.β * P.γ := by
    show ((P.β * P.γ : ℕ) : ℝ) = _
    push_cast; ring
  have hα : (P.α : ℝ) ≤ 455 * n * K * L := by
    rw [hαβγ]
    have := mul_le_mul hβ hγ (Nat.cast_nonneg _) (by positivity)
    linarith
  have hθ : (P.θ : ℝ) ≤ 64 * P.α * n * m + 1 := by
    show ((⌈16 * ((P.β * P.γ : ℕ) : ℝ) * (1 + ε) * (A.unrolledCard n : ℝ)⌉₊ : ℕ) : ℝ) ≤ _
    have hαc : ((P.β * P.γ : ℕ) : ℝ) = P.α := rfl
    rw [hαc]
    have h0 : (0 : ℝ) ≤ 16 * (P.α : ℝ) * (1 + ε) * (A.unrolledCard n : ℝ) := by positivity
    have h1 := Nat.ceil_lt_add_one h0
    have h2 : 16 * (P.α : ℝ) * (1 + ε) * (A.unrolledCard n : ℝ) ≤ 64 * P.α * n * m := by
      have ha : (0 : ℝ) ≤ P.α := Nat.cast_nonneg _
      have e1 : (1 + ε) ≤ 2 := by linarith
      have e2 : ((n : ℝ) + 1) * m ≤ 2 * n * m := by nlinarith
      calc 16 * (P.α : ℝ) * (1 + ε) * (A.unrolledCard n : ℝ)
          ≤ 16 * (P.α : ℝ) * 2 * (((n : ℝ) + 1) * m) := by gcongr
        _ ≤ 16 * (P.α : ℝ) * 2 * (2 * n * m) := by gcongr
        _ = 64 * P.α * n * m := by ring
    linarith
  have hμ : (1 : ℝ) ≤ P.μ := by
    show (1 : ℝ) ≤ ((⌈8 * Real.log (1 / δ)⌉₊ : ℕ) : ℝ)
    have : 0 < Real.log (1 / δ) := Real.log_pos (by rw [one_div]; exact one_lt_inv₀ hδ0 |>.2 hδ1)
    exact_mod_cast Nat.one_le_ceil_iff.2 (by linarith)
  show (countBound m n (MM m) P : ℝ) ≤ m * (1000000 * n ^ 2 * MM m * L * (ε ^ 2)⁻¹ * (1 - ε)⁻¹ * P.μ)
  have hRHS : (m : ℝ) * (1000000 * n ^ 2 * MM m * L * (ε ^ 2)⁻¹ * (1 - ε)⁻¹ * P.μ) =
      1000000 * P.μ * (m * ((n : ℝ) ^ 2 * MM m * L * K)) := by rw [hK]; ring
  rw [hRHS]
  unfold countBound coreBound layerFixed sampleCoef cacheCoef totalCap easFixed
  push_cast
  rw [show 3 * (P.γ : ℝ) * (P.β + 1) = 3 * (P.α + P.γ) by rw [hαβγ]; ring]
  -- abstract the reals
  have ha0 : (0 : ℝ) ≤ P.α := Nat.cast_nonneg _
  have hg0 : (0 : ℝ) ≤ P.γ := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ P.θ := Nat.cast_nonneg _
  generalize (P.α : ℝ) = a at hα hθ ha0 ⊢
  generalize (P.β : ℝ) = b at hβ ⊢
  generalize (P.γ : ℝ) = g at hγ hg0 ⊢
  generalize (P.θ : ℝ) = t at hθ ht0 ⊢
  generalize (P.μ : ℝ) = u at hμ ⊢
  generalize (MM m : ℝ) = w at hW2 hmW ⊢
  generalize (m : ℝ) = x at hmR hW2 hmW hθ ⊢
  generalize (n : ℝ) = y at hnR hβ hα hθ ⊢
  clear_value K L
  exact countBound_poly x y w K L a g t u hmR hnR hW2 hmW hK1 hL1 hγ hα hθ hμ ha0 hg0 ht0

end Nfa.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `countBound_le_target` with `C = 10⁶`; `L ≥ 31/32` from `Real.log_le_sub_one_of_pos` (no `ExponentialBounds` import)
-/
