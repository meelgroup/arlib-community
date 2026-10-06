import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic

/-!
# The moment bound behind the Bellare–Rompel tail bound

Pure arithmetic: a two-parameter majorant `brBd p k n` for the `n`-th central moment of a
sum of `k` independent Bernoulli(`p`) indicators, its one-step recursion in `k`
(`brBd_step`), and its closed-form bound at even `n = 2 s`
(`brBd_le`): `brBd p k (2 s) ≤ ((2 s) (k p) + (2 s)²)^s`.

`brBd p k n = ∑_r C(k, r) p^r U(n, r)` where `U(n, r) = n^{\underline{2r}} r^{n-2r} / 2^r`
bounds the number of maps `Fin n → Fin r` all of whose fibres have size `≥ 2`
(choose the two smallest points of each fibre, then place the rest).
-/

set_option autoImplicit false

namespace Auditable.Analysis

open Finset

/-- `U(n, r) = n^{\underline{2r}} · r^{n - 2r} / 2^r`.

INTERNAL: majorant for the number of maps `Fin n → Fin r` with all fibres of size `≥ 2`.
TEXLINE: prelim.tex:132-143 -/
noncomputable def brU (n r : ℕ) : ℝ :=
  ((n.descFactorial (2 * r) * r ^ (n - 2 * r) : ℕ) : ℝ) / 2 ^ r

/-- The majorant `∑_{r ≤ k} C(k, r) p^r U(n, r)` of the `n`-th central moment of a sum of
`k` (`n`-wise) independent Bernoulli(`p`) indicators.

INTERNAL: moment majorant for the proof of the Bellare–Rompel bound.
TEXLINE: prelim.tex:132-143 -/
noncomputable def brBd (p : ℝ) (k n : ℕ) : ℝ :=
  ∑ r ∈ range (k + 1), (k.choose r : ℝ) * p ^ r * brU n r

/-- The bound on `|E[(Z - p)^m]|` for a Bernoulli(`p`) indicator `Z`: `1`, `0`, then `p`.

INTERNAL: weight in the moment recursion.
TEXLINE: prelim.tex:132-143 -/
noncomputable def brG (p : ℝ) (m : ℕ) : ℝ :=
  if m = 0 then 1 else if m = 1 then 0 else p

/-- `2 · ∑_{m ≥ 2} C(L, m) r^{L - m} ≤ L (L - 1) (r + 1)^{L - 2}` (summed over any range
`m ≤ n` with `L ≤ n`).

INTERNAL: tail of the binomial expansion of `(r + 1)^L`. -/
theorem brTail_le (L r n : ℕ) (hL : L ≤ n) :
    2 * ∑ m ∈ range (n + 1), (if 2 ≤ m then L.choose m * r ^ (L - m) else 0) ≤
      L * (L - 1) * (r + 1) ^ (L - 2) := by
  have hsub : ∑ m ∈ range (n + 1), (if 2 ≤ m then L.choose m * r ^ (L - m) else 0) =
      ∑ m ∈ range (L + 1), (if 2 ≤ m then L.choose m * r ^ (L - m) else 0) := by
    symm
    apply Finset.sum_subset (Finset.range_subset_range.2 (by omega))
    intro m hm hm'
    simp only [Finset.mem_range, not_lt] at hm hm'
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  rw [hsub]
  obtain hL2 | ⟨L', rfl⟩ : L < 2 ∨ ∃ L', L = L' + 2 := by
    rcases Nat.lt_or_ge L 2 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨L - 2, by omega⟩
  · rw [Finset.sum_eq_zero]
    · simp
    intro m hm
    simp only [Finset.mem_range] at hm
    rw [if_neg (by omega)]
  · rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [show ¬ (2 ≤ 0) from by omega, show ¬ (2 ≤ 0 + 1) from by omega, if_false,
      add_zero, show ∀ j, 2 ≤ j + 1 + 1 from fun j => by omega, if_true]
    have hpow : (1 + r) ^ L' = ∑ j ∈ range (L' + 1), 1 ^ j * r ^ (L' - j) * L'.choose j :=
      add_pow 1 r L'
    simp only [one_pow, one_mul] at hpow
    rw [show L' + 2 - 2 = L' from by omega, show L' + 2 - 1 = L' + 1 from by omega,
      add_comm r 1, hpow, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    rw [show L' + 2 - (j + 1 + 1) = L' - j from by omega]
    have h1 := Nat.add_one_mul_choose_eq (L' + 1) (j + 1)
    have h2 := Nat.add_one_mul_choose_eq L' j
    have key : 2 * (L' + 2).choose (j + 2) ≤ (L' + 2) * (L' + 1) * L'.choose j := by
      have : (L' + 2) * (L' + 1) * L'.choose j = (L' + 1 + 1).choose (j + 1 + 1) *
          ((j + 1 + 1) * (j + 1)) := by
        calc (L' + 2) * (L' + 1) * L'.choose j = (L' + 2) * ((L' + 1) * L'.choose j) := by ring
          _ = (L' + 2) * ((L' + 1).choose (j + 1) * (j + 1)) := by rw [h2]
          _ = ((L' + 1 + 1) * (L' + 1).choose (j + 1)) * (j + 1) := by ring
          _ = _ := by rw [h1]; ring
      rw [this]
      have : 2 ≤ (j + 1 + 1) * (j + 1) := by nlinarith
      calc 2 * (L' + 2).choose (j + 2) = (L' + 1 + 1).choose (j + 1 + 1) * 2 := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ this
    calc 2 * ((L' + 2).choose (j + 1 + 1) * r ^ (L' - j))
        = (2 * (L' + 2).choose (j + 2)) * r ^ (L' - j) := by ring
      _ ≤ ((L' + 2) * (L' + 1) * L'.choose j) * r ^ (L' - j) := Nat.mul_le_mul_right _ key
      _ = _ := by ring

/-- `(2s)^{\underline{2r}} ≤ 2^r · s^{\underline{r}} · (2s)^r` for `r ≤ s`.

INTERNAL: pairs the factors of the falling factorial. -/
theorem brDesc_le (s r : ℕ) (hr : r ≤ s) :
    (2 * s).descFactorial (2 * r) ≤ 2 ^ r * s.descFactorial r * (2 * s) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have ih := ih (by omega)
    obtain ⟨d, rfl⟩ : ∃ d, s = r + 1 + d := ⟨s - (r + 1), by omega⟩
    rw [show 2 * (r + 1) = 2 * r + 1 + 1 from by ring, Nat.descFactorial_succ,
      Nat.descFactorial_succ, Nat.descFactorial_succ,
      show 2 * (r + 1 + d) - (2 * r + 1) = 2 * d + 1 from by omega,
      show 2 * (r + 1 + d) - 2 * r = 2 * d + 2 from by omega,
      show r + 1 + d - r = d + 1 from by omega]
    calc (2 * d + 1) * ((2 * d + 2) * (2 * (r + 1 + d)).descFactorial (2 * r))
        ≤ (2 * d + 1) * ((2 * d + 2) *
            (2 ^ r * (r + 1 + d).descFactorial r * (2 * (r + 1 + d)) ^ r)) := by gcongr
      _ ≤ 2 ^ (r + 1) * ((d + 1) * (r + 1 + d).descFactorial r) * (2 * (r + 1 + d)) ^ (r + 1) := by
        rw [pow_succ, pow_succ]
        have : 2 * d + 1 ≤ 2 * (r + 1 + d) := by omega
        calc (2 * d + 1) * ((2 * d + 2) *
              (2 ^ r * (r + 1 + d).descFactorial r * (2 * (r + 1 + d)) ^ r))
            = (2 * d + 1) * (2 ^ r * 2 * (d + 1) * (r + 1 + d).descFactorial r *
                (2 * (r + 1 + d)) ^ r) := by ring
          _ ≤ (2 * (r + 1 + d)) * (2 ^ r * 2 * (d + 1) * (r + 1 + d).descFactorial r *
                (2 * (r + 1 + d)) ^ r) := Nat.mul_le_mul_right _ this
          _ = _ := by ring

/-- `C(n, m) · (n - m)^{\underline{j}} = n^{\underline{j}} · C(n - j, m)`.

INTERNAL: both sides count ordered `j`-tuples plus an `m`-set, disjoint, in `[n]`. -/
theorem brChoose_desc (n m j : ℕ) :
    n.choose m * (n - m).descFactorial j = n.descFactorial j * (n - j).choose m := by
  by_cases h : m + j ≤ n
  · rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
    have h1 := Nat.choose_mul (n := n) (k := m + j) (s := m) (by omega)
    have h2 := Nat.choose_mul (n := n) (k := m + j) (s := j) (by omega)
    rw [show m + j - m = j from by omega] at h1
    rw [show m + j - j = m from by omega] at h2
    have h3 : (m + j).choose m = (m + j).choose j := Nat.choose_symm_add
    calc n.choose m * (j.factorial * (n - m).choose j)
        = j.factorial * (n.choose m * (n - m).choose j) := by ring
      _ = j.factorial * (n.choose (m + j) * (m + j).choose m) := by rw [h1]
      _ = j.factorial * (n.choose (m + j) * (m + j).choose j) := by rw [h3]
      _ = j.factorial * (n.choose j * (n - j).choose m) := by rw [h2]
      _ = _ := by ring
  · rcases Nat.lt_or_ge n m with hm | hm
    · rw [Nat.choose_eq_zero_of_lt hm, Nat.choose_eq_zero_of_lt (by omega)]; simp
    · rw [Nat.descFactorial_eq_zero_iff_lt.2 (by omega : n - m < j)]
      rcases Nat.lt_or_ge n j with hj | hj
      · rw [Nat.descFactorial_eq_zero_iff_lt.2 hj]; simp
      · rw [Nat.choose_eq_zero_of_lt (by omega : n - j < m)]; simp

/-- The natural-number core of `brU_step`:
`2 ∑_{m ≥ 2} C(n, m) (n-m)^{\underline{2r}} r^{n-m-2r} ≤ n^{\underline{2r+2}} (r+1)^{n-2r-2}`.

INTERNAL: one more fibre of size `≥ 2`. -/
theorem brNat_step (n r : ℕ) :
    2 * ∑ m ∈ range (n + 1), (if 2 ≤ m then
        n.choose m * ((n - m).descFactorial (2 * r) * r ^ (n - m - 2 * r)) else 0) ≤
      n.descFactorial (2 * (r + 1)) * (r + 1) ^ (n - 2 * (r + 1)) := by
  set L := n - 2 * r with hL
  have hterm : ∀ m, (if 2 ≤ m then
        n.choose m * ((n - m).descFactorial (2 * r) * r ^ (n - m - 2 * r)) else 0) =
      n.descFactorial (2 * r) * (if 2 ≤ m then L.choose m * r ^ (L - m) else 0) := by
    intro m
    split_ifs
    · rw [← mul_assoc, brChoose_desc, mul_assoc, show n - m - 2 * r = L - m from by omega]
    · simp
  simp_rw [hterm, ← Finset.mul_sum]
  have htail := brTail_le L r n (by omega)
  rw [show 2 * (r + 1) = 2 * r + 1 + 1 from by ring, Nat.descFactorial_succ,
    Nat.descFactorial_succ, show n - (2 * r + 1 + 1) = L - 2 from by omega,
    show n - (2 * r + 1) = L - 1 from by omega, show n - 2 * r = L from rfl]
  calc 2 * (n.descFactorial (2 * r) *
        ∑ m ∈ range (n + 1), (if 2 ≤ m then L.choose m * r ^ (L - m) else 0))
      = n.descFactorial (2 * r) *
        (2 * ∑ m ∈ range (n + 1), (if 2 ≤ m then L.choose m * r ^ (L - m) else 0)) := by ring
    _ ≤ n.descFactorial (2 * r) * (L * (L - 1) * (r + 1) ^ (L - 2)) :=
        Nat.mul_le_mul_left _ htail
    _ = _ := by ring

/-- One step of the majorant at a fixed number `r` of fibres:
`∑_m C(n, m) g(m) U(n - m, r) ≤ U(n, r) + p U(n, r + 1)`.

INTERNAL: the `m = 0` term is `U(n, r)`, `m = 1` vanishes, `m ≥ 2` opens a new fibre. -/
theorem brU_step (p : ℝ) (hp : 0 ≤ p) (n r : ℕ) :
    ∑ m ∈ range (n + 1), (n.choose m : ℝ) * (brG p m * brU (n - m) r) ≤
      brU n r + p * brU n (r + 1) := by
  have hle : ∀ m ∈ range (n + 1), (n.choose m : ℝ) * (brG p m * brU (n - m) r) ≤
      (if 0 = m then brU n r else 0) +
        p * (((if 2 ≤ m then n.choose m * ((n - m).descFactorial (2 * r) *
          r ^ (n - m - 2 * r)) else 0 : ℕ) : ℝ) / 2 ^ r) := by
    intro m _
    rcases Nat.lt_or_ge m 2 with hm | hm
    · obtain rfl | rfl : m = 0 ∨ m = 1 := by omega
      · simp [brG]
      · simp [brG]
    · rw [if_neg (by omega), if_pos hm, brG, if_neg (by omega), if_neg (by omega), brU]
      push_cast
      ring_nf
      exact le_refl _
  refine (Finset.sum_le_sum hle).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos (by simp), ← Finset.mul_sum,
    ← Finset.sum_div, ← Nat.cast_sum]
  have hnat := brNat_step n r
  have h2 : (0 : ℝ) < 2 ^ r := by positivity
  unfold brU
  refine add_le_add_right (mul_le_mul_of_nonneg_left ?_ hp) _
  rw [pow_succ, div_le_div_iff₀ h2 (by positivity)]
  have : (2 : ℝ) * ((∑ m ∈ range (n + 1), (if 2 ≤ m then n.choose m * ((n - m).descFactorial
      (2 * r) * r ^ (n - m - 2 * r)) else 0) : ℕ) : ℝ) ≤
      ((n.descFactorial (2 * (r + 1)) * (r + 1) ^ (n - 2 * (r + 1)) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  nlinarith

/-- `brBd p 0 n = 0^n`: the empty sum has every moment `0` except the zeroth.

INTERNAL: base case of the moment induction. -/
theorem brBd_zero (p : ℝ) (n : ℕ) : brBd p 0 n = 0 ^ n := by
  simp [brBd, brU]

/-- Pascal's rule for the majorant.

INTERNAL: `C(k+1, r) = C(k, r) + C(k, r-1)`. -/
theorem brBd_succ (p : ℝ) (k n : ℕ) :
    brBd p (k + 1) n =
      brBd p k n + ∑ r ∈ range (k + 1), (k.choose r : ℝ) * (p * p ^ r * brU n (r + 1)) := by
  unfold brBd
  rw [Finset.sum_range_succ' _ (k + 1)]
  simp_rw [Nat.choose_succ_succ', Nat.cast_add, add_mul, Finset.sum_add_distrib]
  have h1 : ∑ r ∈ range (k + 1), (k.choose (r + 1) : ℝ) * p ^ (r + 1) * brU n (r + 1) +
      ((k + 1).choose 0 : ℝ) * p ^ 0 * brU n 0 =
      ∑ r ∈ range (k + 1), (k.choose r : ℝ) * p ^ r * brU n r := by
    rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (by omega : k < k + 1),
      Finset.sum_range_succ' _ k]
    simp
  rw [← h1]
  have h2 : ∑ r ∈ range (k + 1), (k.choose r : ℝ) * p ^ (r + 1) * brU n (r + 1) =
      ∑ r ∈ range (k + 1), (k.choose r : ℝ) * (p * p ^ r * brU n (r + 1)) :=
    Finset.sum_congr rfl fun r _ => by ring
  rw [← h2]
  ring

/-- **The moment recursion for the majorant**: adjoining one more indicator,
`∑_m C(n, m) g(m) brBd(k, n - m) ≤ brBd(k + 1, n)`.

INTERNAL: what the induction step of the moment bound consumes.
TEXLINE: prelim.tex:132-143 -/
theorem brBd_step (p : ℝ) (hp : 0 ≤ p) (k n : ℕ) :
    ∑ m ∈ range (n + 1), (n.choose m : ℝ) * (brG p m * brBd p k (n - m)) ≤
      brBd p (k + 1) n := by
  have hswap : ∑ m ∈ range (n + 1), (n.choose m : ℝ) * (brG p m * brBd p k (n - m)) =
      ∑ r ∈ range (k + 1), (k.choose r : ℝ) * p ^ r *
        ∑ m ∈ range (n + 1), (n.choose m : ℝ) * (brG p m * brU (n - m) r) := by
    unfold brBd
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun m _ => by ring
  rw [hswap, brBd_succ]
  calc ∑ r ∈ range (k + 1), (k.choose r : ℝ) * p ^ r *
        ∑ m ∈ range (n + 1), (n.choose m : ℝ) * (brG p m * brU (n - m) r)
      ≤ ∑ r ∈ range (k + 1), (k.choose r : ℝ) * p ^ r * (brU n r + p * brU n (r + 1)) :=
        Finset.sum_le_sum fun r _ =>
          mul_le_mul_of_nonneg_left (brU_step p hp n r) (by positivity)
    _ = _ := by
        unfold brBd
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun r _ => by ring

/-- **The closed-form moment bound**: `brBd p k (2 s) ≤ ((2 s) (k p) + (2 s)²)^s`.

INTERNAL: termwise, `C(k, r) p^r ≤ (k p)^r / r!` and
`(2s)^{\underline{2r}} / (2^r r!) ≤ C(s, r) (2s)^r`, then the binomial theorem.
TEXLINE: prelim.tex:132-143 -/
theorem brBd_le (p : ℝ) (hp : 0 ≤ p) (k s : ℕ) :
    brBd p k (2 * s) ≤ ((2 * s : ℝ) * (k * p) + (2 * s : ℝ) ^ 2) ^ s := by
  set X : ℝ := (2 * s : ℝ) * (k * p) with hX
  set Y : ℝ := (2 * s : ℝ) ^ 2 with hY
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have hterm : ∀ r, (k.choose r : ℝ) * p ^ r * brU (2 * s) r ≤
      X ^ r * Y ^ (s - r) * (s.choose r : ℝ) := by
    intro r
    rcases Nat.lt_or_ge s r with hr | hr
    · have : brU (2 * s) r = 0 := by
        rw [brU, Nat.descFactorial_eq_zero_iff_lt.2 (by omega)]; simp
      rw [this, mul_zero]
      positivity
    · have hC : (k.choose r : ℝ) ≤ (k : ℝ) ^ r / r.factorial := Nat.choose_le_pow_div r k
      have hD : ((2 * s).descFactorial (2 * r) : ℝ) ≤
          2 ^ r * (r.factorial * s.choose r) * (2 * s : ℝ) ^ r := by
        have := brDesc_le s r hr
        rw [Nat.descFactorial_eq_factorial_mul_choose s r] at this
        exact_mod_cast this
      have hR : (r : ℝ) ^ (2 * s - 2 * r) ≤ (2 * s : ℝ) ^ (2 * s - 2 * r) :=
        pow_le_pow_left₀ (by positivity) (by exact_mod_cast (by omega : r ≤ 2 * s)) _
      have hf : (0 : ℝ) < r.factorial := by exact_mod_cast r.factorial_pos
      have h2r : (0 : ℝ) < 2 ^ r := by positivity
      rw [brU]
      push_cast
      calc (k.choose r : ℝ) * p ^ r *
            (((2 * s).descFactorial (2 * r) : ℝ) * (r : ℝ) ^ (2 * s - 2 * r) / 2 ^ r)
          ≤ ((k : ℝ) ^ r / r.factorial) * p ^ r *
            ((2 ^ r * (r.factorial * s.choose r) * (2 * s : ℝ) ^ r) *
              (2 * s : ℝ) ^ (2 * s - 2 * r) / 2 ^ r) := by gcongr
        _ = X ^ r * Y ^ (s - r) * (s.choose r : ℝ) := by
          rw [hX, hY, ← pow_mul, show 2 * (s - r) = 2 * s - 2 * r from by omega]
          field_simp
          ring
  have hsum : ∑ r ∈ range (k + 1), X ^ r * Y ^ (s - r) * (s.choose r : ℝ) ≤
      ∑ r ∈ range (s + 1), X ^ r * Y ^ (s - r) * (s.choose r : ℝ) := by
    calc ∑ r ∈ range (k + 1), X ^ r * Y ^ (s - r) * (s.choose r : ℝ)
        ≤ ∑ r ∈ range (k + s + 1), X ^ r * Y ^ (s - r) * (s.choose r : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
            fun r _ _ => by positivity
      _ = _ := by
          symm
          apply Finset.sum_subset (Finset.range_subset_range.2 (by omega))
          intro r _ hr
          simp only [Finset.mem_range, not_lt] at hr
          rw [Nat.choose_eq_zero_of_lt (by omega)]
          simp
  calc brBd p k (2 * s) ≤ ∑ r ∈ range (k + 1), X ^ r * Y ^ (s - r) * (s.choose r : ℝ) :=
        Finset.sum_le_sum fun r _ => hterm r
    _ ≤ _ := hsum
    _ = (X + Y) ^ s := (add_pow X Y s).symm

end Auditable.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · proved · created for `bellareRompel_tail`; `brBd_step`, `brBd_le` closed, no `sorry`
-/
