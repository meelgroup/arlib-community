/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.CrossRatio
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.HitAndRun

/-!
# Comparing the two chords of a convex body through a common point

This file supplies the two geometric inputs that Lovász's proof of *Lemma 8* of
*Hit-and-run mixes fast* (= Lemma 4.1 of Lovász–Vempala, *Hit-and-Run from a Corner*)
consumes and that `Arlib/MarkovChains/Continuous/HitAndRunOverlap.lean` currently threads as
unproved hypotheses of its capstone:

* the **chord comparison** `ℓ(v,x)·|x − u| ≤ 2·|x − v|·ℓ(u,x)` (`hchord` there), and
* the **mass of the short-step piece** `P_u{x : chordLow K u x < −3} ≤ 1/3` (`hA3` there),
  together with its measurability (`hA3m`).

## The chord comparison is chord-parameter algebra, not projective geometry

Lovász proves the comparison by Menelaus' theorem applied to the triangle `u v x`.  No
Menelaus theorem is needed, and none exists in Mathlib v4.32.  Reading both chords in the
affine coordinate centred at `x` collapses the statement to an inequality between four
scalars: with

* `ρ = chordHigh K x u`, `μ = −chordLow K x u` (the `x`–`u` chord, in units of `|x − u|`),
* `k = chordHigh K x v`, `m = −chordLow K x v` (the `x`–`v` chord, in units of `|x − v|`),

one has `ℓ(u,x) = (ρ + μ)|x − u|` and `ℓ(v,x) = (k + m)|x − v|`, so **both Euclidean lengths
cancel** and the comparison is exactly `k + m ≤ 2(ρ + μ)`.

Menelaus is then replaced by two explicit convex combinations.  Writing `p` and `q` for the
endpoints of the `u`–`v` chord (`chordStart`, `chordEnd`) and `w`, `w'` for the endpoints of
the `x`–`v` chord, the point of `[p, w]` on the line `x u` and the point of `[q, w']` on that
line give

* `le_chordHigh_of_chordLow` — `k(1 − a₁) ≤ ρ(k − a₁)`, and
* `chordLow_le_of_chordHigh` — `chordLow K x u · (b₁ − a₂) ≤ (b₁ − 1)·a₂`,

where `a₁ = chordLow K u v`, `b₁ = chordHigh K u v`, `a₂ = chordLow K x v`.  Both are one
application of `Convex` to two points of `K` plus `match_scalars`.  The cross-ratio
hypothesis enters only through `crossRatioDist K u v < 1/8 ⟹ −a₁ > 8 ∧ b₁ − 1 > 8`
(`eight_lt_of_crossRatioDist_lt`), which is the closed form `crossRatioDist_eq_param` read
backwards.  Neither the near-orthogonality hypothesis (8) nor the median-step hypothesis of
`hchord` is used: the comparison is pure convex geometry.

## The printed hypothesis of `hchord` is not sufficient — a second one is needed

`HitAndRunOverlap.lean` states the chord comparison under the single chord hypothesis
`−3 ≤ chordLow K u x` (the complement of the paper's `A₃`).  **That hypothesis alone does not
imply the conclusion**, for either reading of the paper's `a(u,x)`.  Take `n = 2`, `ε > 0`
small, `M` large and

  `K = conv{(−20ε, 1), (21ε, 1), (0, −M)}`,  `u = (ε, 1)`,  `v = (0, 1)`,  `x = (0, 0)`.

Then `d_K(u,v) = 41/400 < 1/8`, `x − u ⊥ u − v` up to `O(ε)`, `|x − u| ≈ 1` exceeds the
median step (which is `Θ(ε)`), and `chordLow K u x = 0 ≥ −3`; but `ℓ(v,x) = 1 + M` while
`ℓ(u,x) ≈ 21`, so `ℓ(v,x)|x − u| ≤ 2|x − v|ℓ(u,x)` fails for `M > 41`.  Replacing the
hypothesis by `chordHigh K u x ≤ 3` (the other reading of `A₃`) fails symmetrically, on
`K = conv{(−20ε,1), (21ε,1), (0,M), (0,0)}` with the same `u, v, x`.

What is true — and proved here as `chordDiff_le_two_mul` — is the comparison under **both**
bounds, `−3 ≤ chordLow K u x` *and* `chordHigh K u x ≤ 3`; that is, under
`max |u − a| ≤ 3|x − u|` over the two endpoints `a` of the chord through `u` and `x`.  The
factor `2` of the paper then holds with room to spare: the proof only needs
`chordHigh K x u ≤ 4.5` and `−chordLow K x u ≤ 3.73`.

## The mass of the bad steps: `1/3` each, `1/2` for the union — not `1/3`

Each of the two bad sets separately has mass `≤ 1/3`: `hitAndRun_chordLow_lt_le` is the
paper's `P_u(A₃) ≤ 1/3` verbatim, and `hitAndRun_chordHigh_gt_le` is the same bound for the
second one.  Both are one line of geometry per chord — if `x` is bad then rescaling its chord
parameter by `∓3` still lands on the chord, so the bad parameters are contained in a
`∓3`-preimage of the chord, of a third of its length.

Subadditivity would give `2/3` for the union.  The sharp value is `1/2` and it is proved here
(`hitAndRun_chord_bad_le`), because on a chord split by `u` in ratio `λ : 1 − λ` the two bad
pieces overlap; `1/2` is attained at ratio `1 : 3`.  The paper's budget
`1/8 + q₂ + 1/3 < 3/4` therefore becomes `1/8 + q₂ + 1/2`, which is `< 1` exactly when
`q₂ < 3/8` — true for the sharp cap constant `2(1 − Φ(1)) = 0.3173…` but not for the
dimension-free `q₂ = 1/2` that `tvLe_hitAndRun_lemma41_of_half` once assumed — that corollary
is now **deleted**, because the corrected budget `1/8 + q₂ + 1/2` is vacuous there.  See the report to the caller
for what this does to the paper's constants and for the alternative of retuning the factor
`2` (a factor `Λ` allows the confinement `ρ ≤ 9 − 8/Λ`, `μ ≤ 8 − 9/Λ`, and at `Λ = 8` the
union of the bad sets has mass `≈ 0.24`).

## Main results

* `Arlib.chordDiff_le_two_mul` — the chord comparison in chord parameters.
* `Arlib.MarkovChains.chordLength_mul_norm_le` — the same as `hchord` is stated, in terms of
  `chordLength` and Euclidean norms.
* `Arlib.MarkovChains.measurableSet_chordLow_lt`,
  `Arlib.MarkovChains.measurableSet_chordHigh_gt` — the measurability of the two bad sets
  (`hA3m`).
* `Arlib.MarkovChains.hitAndRun_chordLow_lt_le`,
  `Arlib.MarkovChains.hitAndRun_chordHigh_gt_le` — `P_u ≤ 1/3` for each of them (`hA3`).
* `Arlib.MarkovChains.hitAndRun_chord_bad_le` — `P_u ≤ 1/2` for their union.
-/

open Set MeasureTheory
open scoped ENNReal

namespace Arlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} {u v x : E}

/-! ### A scaling lemma for convex subsets of `ℝ`

If `t` and `s·t` both lie in a convex `S ⊆ ℝ`, so does `c·t` for every `c` between `s`
and `1`.  This is the whole content of the two chord-mass bounds below. -/

/-- If `t ∈ S` and `s * t ∈ S` with `s ≤ c ≤ 1`, then `c * t ∈ S`. -/
theorem mul_mem_of_le_one {S : Set ℝ} (hS : Convex ℝ S) {t s c : ℝ}
    (ht : t ∈ S) (hst : s * t ∈ S) (hsc : s ≤ c) (hc1 : c ≤ 1) : c * t ∈ S := by
  rcases eq_or_lt_of_le (le_trans hsc hc1) with hs1 | hs1
  · have : c = 1 := le_antisymm hc1 (hs1 ▸ hsc)
    simpa [this] using ht
  · set lam : ℝ := (c - s) / (1 - s) with hlam
    have hden : (0 : ℝ) < 1 - s := by linarith
    have hlam0 : 0 ≤ lam := by
      rw [hlam]; exact div_nonneg (by linarith) (by linarith)
    have hlam1 : lam ≤ 1 := by
      rw [hlam, div_le_one hden]; linarith
    have hsum : lam + (1 - lam) = 1 := by ring
    have := hS ht hst hlam0 (by linarith) hsum
    have heq : lam • t + (1 - lam) • (s * t) = c * t := by
      simp only [smul_eq_mul, hlam]
      field_simp
      ring
    rwa [heq] at this

/-- If `t ∈ S` and `s * t ∈ S` with `1 ≤ c ≤ s`, then `c * t ∈ S`. -/
theorem mul_mem_of_one_le {S : Set ℝ} (hS : Convex ℝ S) {t s c : ℝ}
    (ht : t ∈ S) (hst : s * t ∈ S) (h1c : 1 ≤ c) (hcs : c ≤ s) : c * t ∈ S := by
  rcases eq_or_lt_of_le (le_trans h1c hcs) with hs1 | hs1
  · have : c = 1 := le_antisymm (hs1 ▸ hcs) h1c
    simpa [this] using ht
  · set lam : ℝ := (s - c) / (s - 1) with hlam
    have hden : (0 : ℝ) < s - 1 := by linarith
    have hlam0 : 0 ≤ lam := by
      rw [hlam]; exact div_nonneg (by linarith) (by linarith)
    have hlam1 : lam ≤ 1 := by
      rw [hlam, div_le_one hden]; linarith
    have hsum : lam + (1 - lam) = 1 := by ring
    have := hS ht hst hlam0 (by linarith) hsum
    have heq : lam • t + (1 - lam) • (s * t) = c * t := by
      simp only [smul_eq_mul, hlam]
      field_simp
      ring
    rwa [heq] at this

/-! ### The cross-ratio hypothesis, in chord parameters -/

/-- **`d_K(u,v) < 1/8` says that the chord through `u` and `v` extends by more than
`8|u − v|` past each of them.**  With `a = chordLow K u v` and `b = chordHigh K u v` the
closed form of `crossRatioDist` is `(b − a)/((−a)(b − 1))`, so `d_K < 1/8` reads
`8(A + C + 1) < A·C` with `A = −a` and `C = b − 1`, which forces `A, C > 8`. -/
theorem eight_lt_of_crossRatioDist_lt (hKb : Bornology.IsBounded K) (huv : u ≠ v)
    (hu : u ∈ K) (hv : v ∈ K) (ha : chordLow K u v < 0) (hb : 1 < chordHigh K u v)
    (hd : crossRatioDist K u v < 1 / 8) :
    8 < -chordLow K u v ∧ 8 < chordHigh K u v - 1 := by
  rw [crossRatioDist_eq_param hKb huv hu hv] at hd
  set A : ℝ := -chordLow K u v with hA
  set C : ℝ := chordHigh K u v - 1 with hC
  have hA0 : 0 < A := by rw [hA]; linarith
  have hC0 : 0 < C := by rw [hC]; linarith
  have hrw : (chordHigh K u v - chordLow K u v) / (-chordLow K u v * (chordHigh K u v - 1))
      = (A + C + 1) / (A * C) := by rw [hA, hC]; ring_nf
  rw [hrw, div_lt_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 8)] at hd
  constructor
  · nlinarith
  · nlinarith

/-! ### The two convex combinations that replace Menelaus' theorem -/

/-- **The far endpoint of the `x`–`v` chord and the endpoint of the `u`–`v` chord beyond `u`
pin the `x`–`u` chord from above.**

Let `a = chordLow K u v` (so `p = chordStart K u v` is the endpoint of the `u`–`v` chord
beyond `u`) and `k = chordHigh K x v` (so `w = chordEnd K x v` is the endpoint of the `x`–`v`
chord beyond `v`).  The point of the segment `[p, w]` lying on the line through `x` and `u`
is `lineMap x u (k(1 − a)/(k − a))`, and it belongs to `K`; hence
`k(1 − a)/(k − a) ≤ chordHigh K x u`.  This is Lovász's Menelaus step. -/
theorem le_chordHigh_of_chordLow (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hu : u ∈ K) (hv : v ∈ K) (hx : x ∈ K)
    (huv : u ≠ v) (hxu : x ≠ u) (hxv : x ≠ v) (ha : chordLow K u v < 0) :
    chordHigh K x v * (1 - chordLow K u v)
      ≤ chordHigh K x u * (chordHigh K x v - chordLow K u v) := by
  set a : ℝ := chordLow K u v with hadef
  set k : ℝ := chordHigh K x v with hkdef
  have hk1 : 1 ≤ k := one_le_chordHigh hKb hxv hv
  have hden : 0 < k - a := by linarith
  set lam : ℝ := k / (k - a) with hlamdef
  have hlam0 : 0 ≤ lam := by rw [hlamdef]; positivity
  have hlam1 : lam ≤ 1 := by
    rw [hlamdef, div_le_one hden]; linarith
  have hp : chordStart K u v ∈ K := chordStart_mem hKc hKcl hKb huv hu hv
  have hw : chordEnd K x v ∈ K := chordEnd_mem hKc hKcl hKb hxv hx hv
  have hz : lam • chordStart K u v + (1 - lam) • chordEnd K x v
      = (AffineMap.lineMap x u : ℝ → E) (k * (1 - a) / (k - a)) := by
    simp only [chordStart, chordEnd, lineMap_apply', ← hadef, ← hkdef, hlamdef]
    match_scalars <;> field_simp <;> ring
  have hmem : k * (1 - a) / (k - a) ∈ chordParam K x u := by
    rw [mem_chordParam, ← hz]
    exact hKc hp hw hlam0 (by linarith) (by ring)
  have hle : k * (1 - a) / (k - a) ≤ chordHigh K x u :=
    le_csSup (bddAbove_chordParam hKb hxu) hmem
  rw [div_le_iff₀ hden] at hle
  linarith

/-- **The far endpoint of the `x`–`v` chord on the other side, together with the endpoint of
the `u`–`v` chord beyond `v`, pin the `x`–`u` chord from below.**

With `b = chordHigh K u v` (`q = chordEnd K u v`) and `a₂ = chordLow K x v`
(`w' = chordStart K x v`), the point of `[q, w']` on the line through `x` and `u` is
`lineMap x u ((b − 1)a₂/(b − a₂))`, so `chordLow K x u ≤ (b − 1)a₂/(b − a₂)`. -/
theorem chordLow_le_of_chordHigh (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hu : u ∈ K) (hv : v ∈ K) (hx : x ∈ K)
    (huv : u ≠ v) (hxu : x ≠ u) (hxv : x ≠ v) (hb : 1 < chordHigh K u v) :
    chordLow K x u * (chordHigh K u v - chordLow K x v)
      ≤ (chordHigh K u v - 1) * chordLow K x v := by
  set b : ℝ := chordHigh K u v with hbdef
  set a₂ : ℝ := chordLow K x v with ha₂def
  have ha₂ : a₂ ≤ 0 := chordLow_nonpos hKb hxv hx
  have hden : 0 < b - a₂ := by linarith
  set lam : ℝ := -a₂ / (b - a₂) with hlamdef
  have hlam0 : 0 ≤ lam := by
    rw [hlamdef]; exact div_nonneg (by linarith) (by linarith)
  have hlam1 : lam ≤ 1 := by
    rw [hlamdef, div_le_one hden]; linarith
  have hq : chordEnd K u v ∈ K := chordEnd_mem hKc hKcl hKb huv hu hv
  have hw : chordStart K x v ∈ K := chordStart_mem hKc hKcl hKb hxv hx hv
  have hz : lam • chordEnd K u v + (1 - lam) • chordStart K x v
      = (AffineMap.lineMap x u : ℝ → E) ((b - 1) * a₂ / (b - a₂)) := by
    simp only [chordStart, chordEnd, lineMap_apply', ← hbdef, ← ha₂def, hlamdef]
    match_scalars <;> field_simp <;> ring
  have hmem : (b - 1) * a₂ / (b - a₂) ∈ chordParam K x u := by
    rw [mem_chordParam, ← hz]
    exact hKc hq hw hlam0 (by linarith) (by ring)
  have hle : chordLow K x u ≤ (b - 1) * a₂ / (b - a₂) :=
    csInf_le (bddBelow_chordParam hKb hxu) hmem
  rw [le_div_iff₀ hden] at hle
  linarith

/-! ### The arithmetic -/

/-- The scalar core of the chord comparison.  `ρ, μ` describe the `x`–`u` chord and `k, m`
the `x`–`v` chord, both in units of the distance from `x`; `A, C > 8` come from
`d_K(u,v) < 1/8` and `h1, h2` from the two convex combinations above.  The hypotheses
`ρ ≤ 4` and `μ ≤ 2` are the two-sided confinement of the `x`–`u` chord. -/
theorem add_le_two_mul_add {A C k m ρ μ : ℝ} (hA : 8 < A) (hC : 8 < C)
    (hk : 1 ≤ k) (hm : 0 ≤ m) (hρ : ρ ≤ 4) (hμ : μ ≤ 2)
    (h1 : k * (1 + A) ≤ ρ * (k + A)) (h2 : m * C ≤ μ * (m + 1 + C)) :
    k + m ≤ 2 * (ρ + μ) := by
  have hkA : (0 : ℝ) < k + A := by linarith
  have hk8 : (0 : ℝ) < k + 8 := by linarith
  have hmC : (0 : ℝ) < m + 1 + C := by linarith
  have hm9 : (0 : ℝ) < m + 9 := by linarith
  -- the `k` half
  have hstep1 : 9 * k * (k + A) ≤ ρ * (k + 8) * (k + A) := by
    nlinarith [mul_le_mul_of_nonneg_right h1 hk8.le,
      mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ k) (by linarith : (0:ℝ) ≤ A - 8))
        (by linarith : (0:ℝ) ≤ k - 1)]
  have hstep1' : 9 * k ≤ ρ * (k + 8) := le_of_mul_le_mul_right hstep1 hkA
  have hk10 : k ≤ 10 := by nlinarith
  have hkρ : k * (k + 8) ≤ 2 * ρ * (k + 8) := by nlinarith
  have hkρ' : k ≤ 2 * ρ := le_of_mul_le_mul_right hkρ hk8
  -- the `m` half
  have hstep2 : 8 * m * (m + 1 + C) ≤ μ * (m + 9) * (m + 1 + C) := by
    nlinarith [mul_le_mul_of_nonneg_right h2 hm9.le,
      mul_nonneg (mul_nonneg hm (by linarith : (0:ℝ) ≤ C - 8))
        (by linarith : (0:ℝ) ≤ m + 1)]
  have hstep2' : 8 * m ≤ μ * (m + 9) := le_of_mul_le_mul_right hstep2 hmC
  have hm7 : m ≤ 7 := by nlinarith
  have hmμ : m * (m + 9) ≤ 2 * μ * (m + 9) := by nlinarith
  have hmμ' : m ≤ 2 * μ := le_of_mul_le_mul_right hmμ hm9
  linarith

/-! ### The chord comparison -/

/-- **The chord comparison, in chord parameters.**

If `u`, `v` are at cross-ratio distance `< 1/8` and the chord of `K` through `u` and `x`
stays within `3|x − u|` of `u` on *both* sides (`−3 ≤ chordLow K u x` and
`chordHigh K u x ≤ 3`), then the chord through `v` and `x`, measured in units of `|x − v|`,
is at most twice the chord through `u` and `x`, measured in units of `|x − u|`:

  `ℓ(v,x)/|x − v| ≤ 2·ℓ(u,x)/|x − u|`.

This is Lovász's Menelaus step of Lemma 8; see the module docstring for why the second
hypothesis cannot be dropped. -/
theorem chordDiff_le_two_mul (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hu : u ∈ K) (hv : v ∈ K) (hx : x ∈ K)
    (huv : u ≠ v) (hxu : x ≠ u) (hxv : x ≠ v)
    (ha : chordLow K u v < 0) (hb : 1 < chordHigh K u v)
    (hd : crossRatioDist K u v < 1 / 8)
    (hlow : -3 ≤ chordLow K u x) (hhigh : chordHigh K u x ≤ 3) :
    chordHigh K v x - chordLow K v x ≤ 2 * (chordHigh K u x - chordLow K u x) := by
  obtain ⟨hA, hC⟩ := eight_lt_of_crossRatioDist_lt hKb huv hu hv ha hb hd
  -- pass from the `u`- and `v`-based coordinates to the `x`-based one
  have hswap1 : chordLow K u x = 1 - chordHigh K x u := chordLow_swap hKb hxu hx
  have hswap2 : chordHigh K u x = 1 - chordLow K x u := chordHigh_swap hKb hxu hx
  have hswap3 : chordLow K v x = 1 - chordHigh K x v := chordLow_swap hKb hxv hx
  have hswap4 : chordHigh K v x = 1 - chordLow K x v := chordHigh_swap hKb hxv hx
  have hk1 : 1 ≤ chordHigh K x v := one_le_chordHigh hKb hxv hv
  have hm0 : chordLow K x v ≤ 0 := chordLow_nonpos hKb hxv hx
  have h1 := le_chordHigh_of_chordLow hKc hKcl hKb hu hv hx huv hxu hxv ha
  have h2 := chordLow_le_of_chordHigh hKc hKcl hKb hu hv hx huv hxu hxv hb
  have key := add_le_two_mul_add (A := -chordLow K u v) (C := chordHigh K u v - 1)
    (k := chordHigh K x v) (m := -chordLow K x v) (ρ := chordHigh K x u)
    (μ := -chordLow K x u) hA hC hk1 (by linarith) (by linarith) (by linarith)
    (by nlinarith [h1]) (by nlinarith [h2])
  linarith

end Arlib

namespace Arlib.MarkovChains

open Arlib

variable {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} {u v x : EuclideanSpace ℝ (Fin n)}

/-! ### `chordLength` in chord parameters -/

/-- The parameter set of `Arlib.MarkovChains.chordSet` at the direction `x − u` is the
parameter set `Arlib.chordParam` of the chord through `u` and `x`. -/
theorem chordSet_eq_chordParam (K : Set (EuclideanSpace ℝ (Fin n)))
    (u x : EuclideanSpace ℝ (Fin n)) : chordSet K u (x - u) = chordParam K u x := by
  ext t
  simp only [chordSet, Set.mem_setOf_eq, mem_chordParam, lineMap_apply']
  rw [add_comm]

/-- **`ℓ(u,x) = |x − u|·(chordHigh − chordLow)`** — the chord length in chord parameters. -/
theorem chordLength_eq_ofReal (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hu : u ∈ K) (hxu : x ≠ u) :
    chordLength K u x
      = ENNReal.ofReal (‖x - u‖ * (chordHigh K u x - chordLow K u x)) := by
  rw [chordLength, chordSet_eq_chordParam,
    chordParam_eq_Icc hKc hKcl hKb (Ne.symm hxu) hu, Real.volume_Icc,
    ← ENNReal.ofReal_mul (norm_nonneg _)]

/-! ### The comparison in the form `HitAndRunOverlap` consumes -/

/-- **The chord comparison** `ℓ(v,x)·|x − u| ≤ 2·|x − v|·ℓ(u,x)`, the hypothesis `hchord` of
`Arlib.MarkovChains.tvLe_hitAndRun_lemma41`.

The Euclidean factors cancel: this is `Arlib.chordDiff_le_two_mul` re-read through
`chordLength_eq_ofReal`.  Note the second chord hypothesis `chordHigh K u x ≤ 3`, which the
printed statement of `hchord` lacks and cannot do without (module docstring). -/
theorem chordLength_mul_norm_le (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hu : u ∈ K) (hv : v ∈ K) (hx : x ∈ K)
    (huv : u ≠ v) (ha : chordLow K u v < 0) (hb : 1 < chordHigh K u v)
    (hd : crossRatioDist K u v < 1 / 8)
    (hlow : -3 ≤ chordLow K u x) (hhigh : chordHigh K u x ≤ 3) :
    chordLength K v x * ENNReal.ofReal ‖x - u‖
      ≤ 2 * (ENNReal.ofReal ‖x - v‖ * chordLength K u x) := by
  rcases eq_or_ne x u with rfl | hxu
  · simp
  rcases eq_or_ne x v with rfl | hxv
  · simp [chordLength]
  have key := chordDiff_le_two_mul hKc hKcl hKb hu hv hx huv hxu hxv ha hb hd hlow hhigh
  have hDu : 0 ≤ chordHigh K u x - chordLow K u x := by
    have h1 : chordLow K u x ≤ 0 := chordLow_nonpos hKb (Ne.symm hxu) hu
    have h2 : 1 ≤ chordHigh K u x := one_le_chordHigh hKb (Ne.symm hxu) hx
    linarith
  have hDv : 0 ≤ chordHigh K v x - chordLow K v x := by
    have h1 : chordLow K v x ≤ 0 := chordLow_nonpos hKb (Ne.symm hxv) hv
    have h2 : 1 ≤ chordHigh K v x := one_le_chordHigh hKb (Ne.symm hxv) hx
    linarith
  have h1 : (0 : ℝ) ≤ ‖x - u‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖x - v‖ := norm_nonneg _
  have hprodL : ENNReal.ofReal (‖x - v‖ * (chordHigh K v x - chordLow K v x))
        * ENNReal.ofReal ‖x - u‖
      = ENNReal.ofReal (‖x - v‖ * (chordHigh K v x - chordLow K v x) * ‖x - u‖) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
  have hprodR : (2 : ℝ≥0∞) * (ENNReal.ofReal ‖x - v‖
        * ENNReal.ofReal (‖x - u‖ * (chordHigh K u x - chordLow K u x)))
      = ENNReal.ofReal (2 * (‖x - v‖ * (‖x - u‖ * (chordHigh K u x - chordLow K u x)))) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_mul h2,
      ENNReal.ofReal_ofNat]
  rw [chordLength_eq_ofReal hKc hKcl hKb hv hxv, chordLength_eq_ofReal hKc hKcl hKb hu hxu,
    hprodL, hprodR]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [mul_nonneg h1 h2]

/-! ### The two bad sets: measurability -/

/-- The degenerate chord: `chordLow K u u = 0`, whichever of `u ∈ K` or `u ∉ K` holds.  So
`u` never belongs to either bad set. -/
theorem chordLow_self (K : Set (EuclideanSpace ℝ (Fin n))) (u : EuclideanSpace ℝ (Fin n)) :
    chordLow K u u = 0 := by
  by_cases h : u ∈ K
  · have huniv : chordParam K u u = Set.univ := by
      ext t; simp [mem_chordParam, h]
    rw [chordLow, huniv]
    exact Real.sInf_of_not_bddBelow not_bddBelow_univ
  · have hempty : chordParam K u u = (∅ : Set ℝ) := by
      ext t; simp [mem_chordParam, h]
    rw [chordLow, hempty, Real.sInf_empty]

/-- `chordHigh K u u = 0`. -/
theorem chordHigh_self (K : Set (EuclideanSpace ℝ (Fin n))) (u : EuclideanSpace ℝ (Fin n)) :
    chordHigh K u u = 0 := by
  by_cases h : u ∈ K
  · have huniv : chordParam K u u = Set.univ := by
      ext t; simp [mem_chordParam, h]
    rw [chordHigh, huniv, Real.sSup_univ]
  · have hempty : chordParam K u u = (∅ : Set ℝ) := by
      ext t; simp [mem_chordParam, h]
    rw [chordHigh, hempty, Real.sSup_empty]

/-- **`{x : chordLow K u x < −3}` is measurable** — the hypothesis `hA3m` of
`Arlib.MarkovChains.tvLe_hitAndRun_lemma41`.

On a convex bounded `K` containing `u`, `chordLow K u x < −3` says that some parameter below
`−3` is admissible, and by convexity some *rational* one is; so the set is the countable
union of the preimages of `K` under the maps `x ↦ u + q(x − u)`, minus the point `u`. -/
theorem measurableSet_chordLow_lt (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hu : u ∈ K) :
    MeasurableSet {x : EuclideanSpace ℝ (Fin n) | chordLow K u x < -3} := by
  have hset : {x : EuclideanSpace ℝ (Fin n) | chordLow K u x < -3}
      = (⋃ q : ℚ, ⋃ (_ : (q : ℝ) < -3),
          (fun x : EuclideanSpace ℝ (Fin n) => (q : ℝ) • (x - u) + u) ⁻¹' K) ∩ {u}ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage,
      Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · intro hx
      have hne : x ≠ u := by
        rintro rfl
        rw [chordLow_self] at hx
        norm_num at hx
      obtain ⟨s, hs, hslt⟩ :=
        exists_lt_of_csInf_lt ⟨0, zero_mem_chordParam (v := x) hu⟩ hx
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hslt
      have hmem : ((q : ℝ)) ∈ chordParam K u x :=
        ((convex_chordParam hKc).ordConnected).out hs (zero_mem_chordParam hu)
          ⟨hq1.le, by linarith⟩
      rw [mem_chordParam, lineMap_apply'] at hmem
      exact ⟨⟨q, hq2, hmem⟩, hne⟩
    · rintro ⟨⟨q, hq, hmem⟩, hne⟩
      have hmem' : ((q : ℝ)) ∈ chordParam K u x := by
        rw [mem_chordParam, lineMap_apply']; exact hmem
      exact lt_of_le_of_lt (csInf_le (bddBelow_chordParam hKb (Ne.symm hne)) hmem') hq
  rw [hset]
  refine MeasurableSet.inter ?_ (measurableSet_singleton u).compl
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ => ?_
  exact hKm.preimage (by fun_prop)

/-- **`{x : 3 < chordHigh K u x}` is measurable** — the companion of
`measurableSet_chordLow_lt` for the second bad set. -/
theorem measurableSet_chordHigh_gt (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hu : u ∈ K) :
    MeasurableSet {x : EuclideanSpace ℝ (Fin n) | 3 < chordHigh K u x} := by
  have hset : {x : EuclideanSpace ℝ (Fin n) | 3 < chordHigh K u x}
      = (⋃ q : ℚ, ⋃ (_ : (3 : ℝ) < (q : ℝ)),
          (fun x : EuclideanSpace ℝ (Fin n) => (q : ℝ) • (x - u) + u) ⁻¹' K) ∩ {u}ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage,
      Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · intro hx
      have hne : x ≠ u := by
        rintro rfl
        rw [chordHigh_self] at hx
        norm_num at hx
      obtain ⟨s, hs, hslt⟩ :=
        exists_lt_of_lt_csSup ⟨0, zero_mem_chordParam (v := x) hu⟩ hx
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hslt
      have hmem : ((q : ℝ)) ∈ chordParam K u x :=
        ((convex_chordParam hKc).ordConnected).out (zero_mem_chordParam hu) hs
          ⟨by linarith, hq2.le⟩
      rw [mem_chordParam, lineMap_apply'] at hmem
      exact ⟨⟨q, hq1, hmem⟩, hne⟩
    · rintro ⟨⟨q, hq, hmem⟩, hne⟩
      have hmem' : ((q : ℝ)) ∈ chordParam K u x := by
        rw [mem_chordParam, lineMap_apply']; exact hmem
      exact lt_of_lt_of_le hq (le_csSup (bddAbove_chordParam hKb (Ne.symm hne)) hmem')
  rw [hset]
  refine MeasurableSet.inter ?_ (measurableSet_singleton u).compl
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ => ?_
  exact hKm.preimage (by fun_prop)

/-! ### The two bad sets: mass -/

/-- The parameter set of a chord of a convex body is convex. -/
theorem convex_chordSet (hKc : Convex ℝ K) (u w : EuclideanSpace ℝ (Fin n)) :
    Convex ℝ (chordSet K u w) := by
  have hrw : chordSet K u w = chordParam K u (u + w) := by
    ext t
    simp only [chordSet, Set.mem_setOf_eq, mem_chordParam, lineMap_apply', add_sub_cancel_left]
    rw [add_comm]
  rw [hrw]
  exact convex_chordParam hKc

/-- Reading the chord through `u` and `u + t·θ` in the direction coordinate: `s` is an
admissible parameter for the former iff `s·t` is one for the latter. -/
theorem mem_chordParam_iff_mul_mem (K : Set (EuclideanSpace ℝ (Fin n)))
    (u θ : EuclideanSpace ℝ (Fin n)) (t s : ℝ) :
    s ∈ chordParam K u (u + t • θ) ↔ s * t ∈ chordSet K u θ := by
  simp only [mem_chordParam, lineMap_apply', chordSet, Set.mem_setOf_eq, add_sub_cancel_left,
    smul_smul]
  rw [add_comm]

/-- **On every chord, at most a third of the mass is `A₃`.**  If the step lands at `x` with
`chordLow K u x < −3` — i.e. the chord runs on past `u`, away from `x`, for more than
`3|x − u|` — then rescaling the parameter by `−3` still lands on the chord.  So the bad
parameters are contained in a set of Lebesgue measure `(1/3)·ℓ`. -/
theorem uniformOn_chordLow_lt_le (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    (hA3m : MeasurableSet {x : EuclideanSpace ℝ (Fin n) | chordLow K u x < -3})
    (θ : EuclideanSpace ℝ (Fin n)) :
    Arlib.uniformOn (volume : Measure ℝ) (chordSet K u θ)
        {t : ℝ | u + t • θ ∈ {x : EuclideanSpace ℝ (Fin n) | chordLow K u x < -3}}
      ≤ ENNReal.ofReal (1 / 3) := by
  set S : Set ℝ := chordSet K u θ with hSdef
  set T : Set ℝ :=
    {t : ℝ | u + t • θ ∈ {x : EuclideanSpace ℝ (Fin n) | chordLow K u x < -3}} with hTdef
  have hSm : MeasurableSet S := measurableSet_chordSet hKm u θ
  have hTm : MeasurableSet T := hA3m.preimage (by fun_prop)
  rw [Arlib.uniformOn_apply _ hSm hTm]
  refine ENNReal.div_le_of_le_mul ?_
  have hsub : T ∩ S ⊆ (fun t : ℝ => (-3 : ℝ) * t) ⁻¹' S := by
    rintro t ⟨htT, htS⟩
    have hlow : chordLow K u (u + t • θ) < -3 := htT
    have hne : (chordParam K u (u + t • θ)).Nonempty :=
      ⟨1, by rw [mem_chordParam_iff_mul_mem]; simpa using htS⟩
    obtain ⟨s, hs, hslt⟩ := exists_lt_of_csInf_lt hne hlow
    rw [mem_chordParam_iff_mul_mem] at hs
    exact mul_mem_of_le_one (convex_chordSet hKc u θ) htS hs hslt.le (by norm_num)
  calc volume (T ∩ S) ≤ volume ((fun t : ℝ => (-3 : ℝ) * t) ⁻¹' S) := measure_mono hsub
    _ = ENNReal.ofReal |(-3 : ℝ)⁻¹| * volume S :=
        Real.volume_preimage_mul_left (by norm_num) S
    _ = ENNReal.ofReal (1 / 3) * volume S := by norm_num

/-- The companion of `uniformOn_chordLow_lt_le` for the second bad set. -/
theorem uniformOn_chordHigh_gt_le (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    (hA4m : MeasurableSet {x : EuclideanSpace ℝ (Fin n) | 3 < chordHigh K u x})
    (θ : EuclideanSpace ℝ (Fin n)) :
    Arlib.uniformOn (volume : Measure ℝ) (chordSet K u θ)
        {t : ℝ | u + t • θ ∈ {x : EuclideanSpace ℝ (Fin n) | 3 < chordHigh K u x}}
      ≤ ENNReal.ofReal (1 / 3) := by
  set S : Set ℝ := chordSet K u θ with hSdef
  set T : Set ℝ :=
    {t : ℝ | u + t • θ ∈ {x : EuclideanSpace ℝ (Fin n) | 3 < chordHigh K u x}} with hTdef
  have hSm : MeasurableSet S := measurableSet_chordSet hKm u θ
  have hTm : MeasurableSet T := hA4m.preimage (by fun_prop)
  rw [Arlib.uniformOn_apply _ hSm hTm]
  refine ENNReal.div_le_of_le_mul ?_
  have hsub : T ∩ S ⊆ (fun t : ℝ => (3 : ℝ) * t) ⁻¹' S := by
    rintro t ⟨htT, htS⟩
    have hhigh : (3 : ℝ) < chordHigh K u (u + t • θ) := htT
    have hne : (chordParam K u (u + t • θ)).Nonempty :=
      ⟨1, by rw [mem_chordParam_iff_mul_mem]; simpa using htS⟩
    obtain ⟨s, hs, hslt⟩ := exists_lt_of_lt_csSup hne hhigh
    rw [mem_chordParam_iff_mul_mem] at hs
    exact mul_mem_of_one_le (convex_chordSet hKc u θ) htS hs (by norm_num) hslt.le
  calc volume (T ∩ S) ≤ volume ((fun t : ℝ => (3 : ℝ) * t) ⁻¹' S) := measure_mono hsub
    _ = ENNReal.ofReal |(3 : ℝ)⁻¹| * volume S :=
        Real.volume_preimage_mul_left (by norm_num) S
    _ = ENNReal.ofReal (1 / 3) * volume S := by norm_num

/-- **`P_u{x : chordLow K u x < −3} ≤ 1/3`**, for the proposal. -/
theorem hitAndRunProposal_chordLow_lt_le (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hu : u ∈ K) :
    hitAndRunProposal K u {x : EuclideanSpace ℝ (Fin n) | chordLow K u x < -3}
      ≤ ENNReal.ofReal (1 / 3) := by
  have hA3m := measurableSet_chordLow_lt hKm hKc hKb hu
  rw [hitAndRunProposal_apply_uniformOn hKm u hA3m]
  calc ∫⁻ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        Arlib.uniformOn (volume : Measure ℝ)
          (chordSet K u (θ : EuclideanSpace ℝ (Fin n)))
          {t : ℝ | u + t • (θ : EuclideanSpace ℝ (Fin n)) ∈
            {x : EuclideanSpace ℝ (Fin n) | chordLow K u x < -3}} ∂(unifSphere n)
      ≤ ∫⁻ _ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          ENNReal.ofReal (1 / 3) ∂(unifSphere n) :=
        lintegral_mono fun θ => uniformOn_chordLow_lt_le hKm hKc hA3m _
    _ = ENNReal.ofReal (1 / 3) * unifSphere n Set.univ := by rw [lintegral_const]
    _ ≤ ENNReal.ofReal (1 / 3) * 1 := mul_le_mul' le_rfl (unifSphere_univ_le_one n)
    _ = ENNReal.ofReal (1 / 3) := mul_one _

/-- **`P_u{x : 3 < chordHigh K u x} ≤ 1/3`**, for the proposal. -/
theorem hitAndRunProposal_chordHigh_gt_le (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hu : u ∈ K) :
    hitAndRunProposal K u {x : EuclideanSpace ℝ (Fin n) | 3 < chordHigh K u x}
      ≤ ENNReal.ofReal (1 / 3) := by
  have hA4m := measurableSet_chordHigh_gt hKm hKc hKb hu
  rw [hitAndRunProposal_apply_uniformOn hKm u hA4m]
  calc ∫⁻ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        Arlib.uniformOn (volume : Measure ℝ)
          (chordSet K u (θ : EuclideanSpace ℝ (Fin n)))
          {t : ℝ | u + t • (θ : EuclideanSpace ℝ (Fin n)) ∈
            {x : EuclideanSpace ℝ (Fin n) | 3 < chordHigh K u x}} ∂(unifSphere n)
      ≤ ∫⁻ _ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          ENNReal.ofReal (1 / 3) ∂(unifSphere n) :=
        lintegral_mono fun θ => uniformOn_chordHigh_gt_le hKm hKc hA4m _
    _ = ENNReal.ofReal (1 / 3) * unifSphere n Set.univ := by rw [lintegral_const]
    _ ≤ ENNReal.ofReal (1 / 3) * 1 := mul_le_mul' le_rfl (unifSphere_univ_le_one n)
    _ = ENNReal.ofReal (1 / 3) := mul_one _

/-- **`P_u(A₃) ≤ 1/3`** — the hypothesis `hA3` of
`Arlib.MarkovChains.tvLe_hitAndRun_lemma41`, for the walk itself.  The lazy atom of
`hitAndRun` sits at `u`, which is never in `A₃` (`chordLow_self`). -/
theorem hitAndRun_chordLow_lt_le (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hu : u ∈ K) :
    hitAndRun K u {x : EuclideanSpace ℝ (Fin n) | chordLow K u x < -3}
      ≤ ENNReal.ofReal (1 / 3) := by
  have hA3m := measurableSet_chordLow_lt hKm hKc hKb hu
  have hnot : u ∉ {x : EuclideanSpace ℝ (Fin n) | chordLow K u x < -3} := by
    simp only [Set.mem_setOf_eq, chordLow_self]
    norm_num
  rw [hitAndRun_apply_set hKm u hA3m, Set.indicator_of_notMem hnot, mul_zero, add_zero]
  exact hitAndRunProposal_chordLow_lt_le hKm hKc hKb hu

/-- **`P_u{x : 3 < chordHigh K u x} ≤ 1/3`** for the walk — the bound on the second bad set
that the corrected chord comparison needs. -/
theorem hitAndRun_chordHigh_gt_le (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hu : u ∈ K) :
    hitAndRun K u {x : EuclideanSpace ℝ (Fin n) | 3 < chordHigh K u x}
      ≤ ENNReal.ofReal (1 / 3) := by
  have hA4m := measurableSet_chordHigh_gt hKm hKc hKb hu
  have hnot : u ∉ {x : EuclideanSpace ℝ (Fin n) | 3 < chordHigh K u x} := by
    simp only [Set.mem_setOf_eq, chordHigh_self]
    norm_num
  rw [hitAndRun_apply_set hKm u hA4m, Set.indicator_of_notMem hnot, mul_zero, add_zero]
  exact hitAndRunProposal_chordHigh_gt_le hKm hKc hKb hu

/-! ### The union of the two bad sets has mass `≤ 1/2`, not `2/3`

Subadditivity gives only `1/3 + 1/3`; on each chord the true bound is `1/2`, and it is
attained (a chord split by `u` in the ratio `1 : 3`).  This is what makes the corrected
Lemma 4.1 non-vacuous. -/

/-- A convex subset of `ℝ` of finite measure is bounded above. -/
private theorem bddAbove_of_volume_ne_top {S : Set ℝ} (hS : Convex ℝ S)
    (hfin : volume S ≠ ⊤) : BddAbove S := by
  by_contra hb
  rcases S.eq_empty_or_nonempty with rfl | ⟨c, hc⟩
  · exact hb bddAbove_empty
  · have hsub : Set.Ici c ⊆ S := by
      intro y hy
      obtain ⟨z, hz, hyz⟩ := not_bddAbove_iff.1 hb y
      exact hS.ordConnected.out hc hz ⟨hy, hyz.le⟩
    have : volume (Set.Ici c) ≤ volume S := measure_mono hsub
    rw [Real.volume_Ici] at this
    exact hfin (top_le_iff.1 this)

/-- A convex subset of `ℝ` of finite measure is bounded below. -/
private theorem bddBelow_of_volume_ne_top {S : Set ℝ} (hS : Convex ℝ S)
    (hfin : volume S ≠ ⊤) : BddBelow S := by
  by_contra hb
  rcases S.eq_empty_or_nonempty with rfl | ⟨c, hc⟩
  · exact hb bddBelow_empty
  · have hsub : Set.Iic c ⊆ S := by
      intro y hy
      obtain ⟨z, hz, hyz⟩ := not_bddBelow_iff.1 hb y
      exact hS.ordConnected.out hz hc ⟨hyz.le, hy⟩
    have : volume (Set.Iic c) ≤ volume S := measure_mono hsub
    rw [Real.volume_Iic] at this
    exact hfin (top_le_iff.1 this)

/-- A convex subset of `ℝ` fills the open interval between its bounds. -/
private theorem ofReal_sub_le_volume {S : Set ℝ} (hS : Convex ℝ S) (hne : S.Nonempty) :
    ENNReal.ofReal (sSup S - sInf S) ≤ volume S := by
  have hsub : Set.Ioo (sInf S) (sSup S) ⊆ S := by
    rintro y ⟨h1, h2⟩
    obtain ⟨c, hc, hcy⟩ := exists_lt_of_csInf_lt hne h1
    obtain ⟨d, hd, hyd⟩ := exists_lt_of_lt_csSup hne h2
    exact hS.ordConnected.out hc hd ⟨hcy.le, hyd.le⟩
  calc ENNReal.ofReal (sSup S - sInf S) = volume (Set.Ioo (sInf S) (sSup S)) :=
        (Real.volume_Ioo).symm
    _ ≤ volume S := measure_mono hsub

/-- **The sharp one-chord bound.**  For a convex `S ⊆ ℝ` containing `0`, the parameters `t`
of `S` with `3t ∈ S` or `−3t ∈ S` fill at most half of `S`.  (Half is attained: `S = [−1,3]`
gives `[−1,1]`.) -/
theorem volume_inter_scale_union_le {S : Set ℝ} (hS : Convex ℝ S) (h0 : (0 : ℝ) ∈ S) :
    volume (S ∩ ((fun t : ℝ => (3 : ℝ) * t) ⁻¹' S ∪ (fun t : ℝ => (-3 : ℝ) * t) ⁻¹' S))
      ≤ ENNReal.ofReal (1 / 2) * volume S := by
  set W : Set ℝ :=
    S ∩ ((fun t : ℝ => (3 : ℝ) * t) ⁻¹' S ∪ (fun t : ℝ => (-3 : ℝ) * t) ⁻¹' S) with hWdef
  rcases eq_or_ne (volume S) ⊤ with htop | htop
  · rw [htop, ENNReal.mul_top (by simp : ENNReal.ofReal (1 / 2) ≠ 0)]
    exact le_top
  have hba : BddAbove S := bddAbove_of_volume_ne_top hS htop
  have hbb : BddBelow S := bddBelow_of_volume_ne_top hS htop
  set a : ℝ := sInf S with hadef
  set b : ℝ := sSup S with hbdef
  have hbound : ∀ y ∈ S, a ≤ y ∧ y ≤ b := fun y hy => ⟨csInf_le hbb hy, le_csSup hba hy⟩
  have ha0 : a ≤ 0 := (hbound 0 h0).1
  have hb0 : (0 : ℝ) ≤ b := (hbound 0 h0).2
  have hvol : ENNReal.ofReal (b - a) ≤ volume S := ofReal_sub_le_volume hS ⟨0, h0⟩
  -- the four cases, each an explicit interval
  have hfinish : ∀ c d : ℝ, W ⊆ Set.Icc c d → d - c ≤ (b - a) / 2 →
      volume W ≤ ENNReal.ofReal (1 / 2) * volume S := by
    intro c d hsub hlen
    calc volume W ≤ volume (Set.Icc c d) := measure_mono hsub
      _ = ENNReal.ofReal (d - c) := Real.volume_Icc
      _ ≤ ENNReal.ofReal (1 / 2 * (b - a)) := ENNReal.ofReal_le_ofReal (by linarith)
      _ = ENNReal.ofReal (1 / 2) * ENNReal.ofReal (b - a) :=
          ENNReal.ofReal_mul (by norm_num)
      _ ≤ ENNReal.ofReal (1 / 2) * volume S := mul_le_mul' le_rfl hvol
  have hdisj : ∀ t ∈ W, (a ≤ 3 * t ∧ 3 * t ≤ b) ∨ (a ≤ -3 * t ∧ -3 * t ≤ b) := by
    rintro t ⟨-, ht | ht⟩
    · exact Or.inl (hbound _ ht)
    · exact Or.inr (hbound _ ht)
  have hmemS : ∀ t ∈ W, a ≤ t ∧ t ≤ b := fun t ht => hbound t ht.1
  rcases le_total (-a) b with hcase | hcase
  · -- the chord is longer on the `b` side
    rcases le_total (-(b / 3)) a with h2 | h2
    · refine hfinish a (b / 3) ?_ (by linarith)
      rintro t ht
      refine ⟨(hmemS t ht).1, ?_⟩
      rcases hdisj t ht with ⟨-, h⟩ | ⟨h, -⟩ <;> linarith
    · refine hfinish (-(b / 3)) (b / 3) ?_ (by linarith)
      rintro t ht
      constructor
      · rcases hdisj t ht with ⟨h, -⟩ | ⟨-, h⟩ <;> linarith
      · rcases hdisj t ht with ⟨-, h⟩ | ⟨h, -⟩ <;> linarith
  · -- the chord is longer on the `a` side
    rcases le_total b (-(a / 3)) with h2 | h2
    · refine hfinish (a / 3) b ?_ (by linarith)
      rintro t ht
      refine ⟨?_, (hmemS t ht).2⟩
      rcases hdisj t ht with ⟨h, -⟩ | ⟨-, h⟩ <;> linarith
    · refine hfinish (a / 3) (-(a / 3)) ?_ (by linarith)
      rintro t ht
      constructor
      · rcases hdisj t ht with ⟨h, -⟩ | ⟨-, h⟩ <;> linarith
      · rcases hdisj t ht with ⟨-, h⟩ | ⟨h, -⟩ <;> linarith

/-- The union of the two bad sets, on one chord: mass `≤ 1/2`. -/
theorem uniformOn_chord_bad_le (hKm : MeasurableSet K) (hKc : Convex ℝ K) (hu : u ∈ K)
    (hbadm : MeasurableSet ({x : EuclideanSpace ℝ (Fin n) | chordLow K u x < -3}
      ∪ {x : EuclideanSpace ℝ (Fin n) | 3 < chordHigh K u x}))
    (θ : EuclideanSpace ℝ (Fin n)) :
    Arlib.uniformOn (volume : Measure ℝ) (chordSet K u θ)
        {t : ℝ | u + t • θ ∈ ({x : EuclideanSpace ℝ (Fin n) | chordLow K u x < -3}
          ∪ {x : EuclideanSpace ℝ (Fin n) | 3 < chordHigh K u x})}
      ≤ ENNReal.ofReal (1 / 2) := by
  set S : Set ℝ := chordSet K u θ with hSdef
  set T : Set ℝ := {t : ℝ | u + t • θ ∈ ({x : EuclideanSpace ℝ (Fin n) | chordLow K u x < -3}
    ∪ {x : EuclideanSpace ℝ (Fin n) | 3 < chordHigh K u x})} with hTdef
  have hSm : MeasurableSet S := measurableSet_chordSet hKm u θ
  have hTm : MeasurableSet T := hbadm.preimage (by fun_prop)
  have hSconv : Convex ℝ S := convex_chordSet hKc u θ
  have h0 : (0 : ℝ) ∈ S := by
    simp only [hSdef, chordSet, Set.mem_setOf_eq, zero_smul, add_zero]; exact hu
  rw [Arlib.uniformOn_apply _ hSm hTm]
  refine ENNReal.div_le_of_le_mul ?_
  have hsub : T ∩ S ⊆
      S ∩ ((fun t : ℝ => (3 : ℝ) * t) ⁻¹' S ∪ (fun t : ℝ => (-3 : ℝ) * t) ⁻¹' S) := by
    rintro t ⟨htT, htS⟩
    refine ⟨htS, ?_⟩
    have hne : (chordParam K u (u + t • θ)).Nonempty :=
      ⟨1, by rw [mem_chordParam_iff_mul_mem]; simpa using htS⟩
    rcases htT with hlow | hhigh
    · obtain ⟨s, hs, hslt⟩ := exists_lt_of_csInf_lt hne hlow
      rw [mem_chordParam_iff_mul_mem] at hs
      exact Or.inr (mul_mem_of_le_one hSconv htS hs hslt.le (by norm_num))
    · obtain ⟨s, hs, hslt⟩ := exists_lt_of_lt_csSup hne hhigh
      rw [mem_chordParam_iff_mul_mem] at hs
      exact Or.inl (mul_mem_of_one_le hSconv htS hs (by norm_num) hslt.le)
  exact le_trans (measure_mono hsub) (volume_inter_scale_union_le hSconv h0)

/-- **`P_u(A₃ ∪ A₄) ≤ 1/2`** — the sharp bound for the union of the two bad sets, for the
proposal. -/
theorem hitAndRunProposal_chord_bad_le (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hu : u ∈ K) :
    hitAndRunProposal K u ({x : EuclideanSpace ℝ (Fin n) | chordLow K u x < -3}
        ∪ {x : EuclideanSpace ℝ (Fin n) | 3 < chordHigh K u x})
      ≤ ENNReal.ofReal (1 / 2) := by
  have hbadm := (measurableSet_chordLow_lt hKm hKc hKb hu).union
    (measurableSet_chordHigh_gt hKm hKc hKb hu)
  rw [hitAndRunProposal_apply_uniformOn hKm u hbadm]
  calc ∫⁻ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        Arlib.uniformOn (volume : Measure ℝ)
          (chordSet K u (θ : EuclideanSpace ℝ (Fin n)))
          {t : ℝ | u + t • (θ : EuclideanSpace ℝ (Fin n)) ∈
            ({x : EuclideanSpace ℝ (Fin n) | chordLow K u x < -3}
              ∪ {x : EuclideanSpace ℝ (Fin n) | 3 < chordHigh K u x})} ∂(unifSphere n)
      ≤ ∫⁻ _ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          ENNReal.ofReal (1 / 2) ∂(unifSphere n) :=
        lintegral_mono fun θ => uniformOn_chord_bad_le hKm hKc hu hbadm _
    _ = ENNReal.ofReal (1 / 2) * unifSphere n Set.univ := by rw [lintegral_const]
    _ ≤ ENNReal.ofReal (1 / 2) * 1 := mul_le_mul' le_rfl (unifSphere_univ_le_one n)
    _ = ENNReal.ofReal (1 / 2) := mul_one _

/-- **`P_u(A₃ ∪ A₄) ≤ 1/2`** for the walk: the mass of the set of steps on which the
corrected chord comparison is not available. -/
theorem hitAndRun_chord_bad_le (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hu : u ∈ K) :
    hitAndRun K u ({x : EuclideanSpace ℝ (Fin n) | chordLow K u x < -3}
        ∪ {x : EuclideanSpace ℝ (Fin n) | 3 < chordHigh K u x})
      ≤ ENNReal.ofReal (1 / 2) := by
  have hbadm := (measurableSet_chordLow_lt hKm hKc hKb hu).union
    (measurableSet_chordHigh_gt hKm hKc hKb hu)
  have hnot : u ∉ ({x : EuclideanSpace ℝ (Fin n) | chordLow K u x < -3}
      ∪ {x : EuclideanSpace ℝ (Fin n) | 3 < chordHigh K u x}) := by
    simp only [Set.mem_union, Set.mem_setOf_eq, chordLow_self, chordHigh_self]
    norm_num
  rw [hitAndRun_apply_set hKm u hbadm, Set.indicator_of_notMem hnot, mul_zero, add_zero]
  exact hitAndRunProposal_chord_bad_le hKm hKc hKb hu

/-! ### Axiom profile -/

section AxiomCheck

#print axioms Arlib.mul_mem_of_le_one
#print axioms Arlib.mul_mem_of_one_le
#print axioms Arlib.eight_lt_of_crossRatioDist_lt
#print axioms Arlib.le_chordHigh_of_chordLow
#print axioms Arlib.chordLow_le_of_chordHigh
#print axioms Arlib.add_le_two_mul_add
#print axioms Arlib.chordDiff_le_two_mul
#print axioms chordSet_eq_chordParam
#print axioms chordLength_eq_ofReal
#print axioms chordLength_mul_norm_le
#print axioms chordLow_self
#print axioms chordHigh_self
#print axioms measurableSet_chordLow_lt
#print axioms measurableSet_chordHigh_gt
#print axioms convex_chordSet
#print axioms mem_chordParam_iff_mul_mem
#print axioms uniformOn_chordLow_lt_le
#print axioms uniformOn_chordHigh_gt_le
#print axioms hitAndRunProposal_chordLow_lt_le
#print axioms hitAndRunProposal_chordHigh_gt_le
#print axioms hitAndRun_chordLow_lt_le
#print axioms hitAndRun_chordHigh_gt_le
#print axioms volume_inter_scale_union_le
#print axioms uniformOn_chord_bad_le
#print axioms hitAndRunProposal_chord_bad_le
#print axioms hitAndRun_chord_bad_le

end AxiomCheck

end Arlib.MarkovChains
