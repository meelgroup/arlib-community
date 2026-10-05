/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.LocalizationLemma
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Probability.UniformOn

/-!
# Towards the Dyer–Frieze / Lovász–Simonovits isoperimetric inequality

The inequality in question is:

> Let `K ⊆ ℝⁿ` be a convex body of diameter `D`, let `A, B ⊆ K` be measurable with
> `dist u v ≥ d` for every `u ∈ A`, `v ∈ B`, and let `C = K \ A \ B`.  Then
> `vol C * vol K ≥ (2d/D) * vol A * vol B`.

**Nothing in this file assumes it.**  There is no `def`, `structure`, `class` or named `Prop`
here that asserts an isoperimetric inequality; every declaration below is either an explicit
set/function or a theorem proved outright.  Where a statement is conditional (the bisection
*step*), the hypothesis is written out inline in the theorem's type, so a reader of the type
sees exactly what is assumed.

## What is proved here, unconditionally

* `Arlib.le_abs_sub_csSup`, `Arlib.le_abs_sub_csInf` — a supremum/infimum of a set that stays
  at distance `≥ d` from a point stays at distance `≥ d` from that point.  (True with no
  closedness hypothesis, by a two-case argument: either some element is on the far side, or
  all of them are on the near side.)

* `Arlib.exists_gap_of_separated` — **the geometric heart of the one-dimensional case.**  If
  `A, B ⊆ ℝ` satisfy `d ≤ |x - y|` for all `x ∈ A`, `y ∈ B`, and `u ∈ A`, `v ∈ B` with
  `u ≤ v`, then the interval `[u,v]` contains an *open* subinterval `(s,t)` of length `≥ d`
  meeting neither `A` nor `B`.

* `Arlib.ofReal_le_volume_sdiff_of_separated` — hence `vol (Icc a b \ A \ B) ≥ d` whenever
  `A, B` are nonempty separated subsets of `Icc a b`.

* `Arlib.dyerFrieze_dim_one` — **the one-dimensional Dyer–Frieze inequality, in full**:
  for convex `K ⊆ ℝ` and `A, B ⊆ K` measurable and `d`-separated,
  `2d * vol A * vol B ≤ vol (K \ A \ B) * (vol K)^2`.
  This is the `n = 1` instance of the displayed statement above with `D = diam K = vol K`,
  `κ = 2/D`, cleared of the denominator.  `Arlib.dyerFrieze_dim_one'` restates it in the
  undivided `κ · d · vol A · vol B ≤ vol (K \ A \ B) · vol K` shape with `κ = 2 / vol K`,
  and `Arlib.uniformOn_dyerFrieze_dim_one` restates it once more in *exactly* the shape of the
  `hiso` hypothesis of `Arlib.conductance_ballWalk_ge`, so that the match is machine-checked
  rather than asserted in prose.

* `Arlib.exists_freeSegment_of_separated` — the `n`-dimensional form of the gap lemma: in a
  convex `K`, for any `u ∈ A` and `v ∈ B` the *segment* from `u` to `v` contains a
  subsegment of length `≥ d` lying in `K` and meeting neither `A` nor `B`.  (Every chord from
  `A` to `B` has a free stretch of length `d`.)

* `Arlib.mul_add_le_of_proportional` — the **lossless merge**: if the inequality
  `κ aᵢ bᵢ ≤ cᵢ Vᵢ` holds on two pieces and the pieces split `A` and `B` *in the same
  proportion* (`a₁ b₂ = a₂ b₁`), then `κ (a₁+a₂)(b₁+b₂) ≤ (c₁+c₂)(V₁+V₂)`.  Note this is
  exactly where proportionality is needed: the AM–GM step
  `2√(a₁b₂ · a₂b₁) ≤ a₁b₂ + a₂b₁` is an equality iff `a₁b₂ = a₂b₁`.

* `Arlib.mul_add_le_of_proportional_ennreal` — the same statement in `ℝ≥0∞`, with the
  finiteness guards spelled out.

* `Arlib.exists_halfSpace_proportional` — **the proportional cut exists, in any prescribed
  direction.**  Applying `Arlib.exists_halfSpace_bisecting` to the *signed* integrand
  `vol B · 1_A - vol A · 1_B` (whose integral over `K` is `0`) produces a halfspace `P` with
  `vol(A ∩ P) * vol(B \ P) = vol(A \ P) * vol(B ∩ P)`, i.e. a cut splitting `A` and `B` in
  the same proportion.  This replaces the usual Borsuk–Ulam / ham-sandwich appeal: only one
  real condition has to be met, and the bisecting-hyperplane IVT already meets it, so the
  direction of the cut stays free.

* `Arlib.dyerFrieze_step` — **the induction step, proved**: the inequality for the two sides
  of a proportional cut implies it for `K`.  `Arlib.exists_halfSpace_dyerFrieze_step` packages
  the previous two: for every bounded `K` of finite measure and every direction `L`, *there
  exists* a hyperplane cut such that the inequality on both sides gives the inequality on `K`.

## What is *not* proved here, and why

The bisection step above is *lossless* but does **not** decrease dimension, and the position
of the cut is forced by the proportionality condition (not by geometry), so neither piece need
be geometrically smaller.  The classical proof closes the loop with a compactness/limiting
argument — iterate the cut and pass to the limit, where the pieces degenerate to
one-dimensional needles and `dyerFrieze_dim_one` applies.  That limit is exactly the content
of the Localization Lemma, and it is not available here (see
`Arlib.Convexity.LocalizationLemma`).  The precise residual goal is recorded in the docstring
of `Arlib.dyerFrieze_step`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Arlib

/-! ### Suprema and infima of separated sets -/

/-- If every element of `S` is at distance `≥ d` from `y`, so is `sSup S`.

No closedness or limit argument is needed: either some element of `S` lies at `≥ y + d`, and
then so does `sSup S`; or every element lies `≤ y - d`, and then so does `sSup S`. -/
theorem le_abs_sub_csSup {S : Set ℝ} (hne : S.Nonempty) (hbdd : BddAbove S) {y d : ℝ}
    (h : ∀ x ∈ S, d ≤ |x - y|) : d ≤ |sSup S - y| := by
  by_cases hex : ∃ x ∈ S, y + d ≤ x
  · obtain ⟨x, hxS, hx⟩ := hex
    have hle : y + d ≤ sSup S := hx.trans (le_csSup hbdd hxS)
    calc d ≤ sSup S - y := by linarith
      _ ≤ |sSup S - y| := le_abs_self _
  · push Not at hex
    have hub : ∀ x ∈ S, x ≤ y - d := by
      intro x hxS
      have h1 := h x hxS
      have h2 := hex x hxS
      rcases abs_cases (x - y) with ⟨he, _⟩ | ⟨he, _⟩ <;> linarith [h1, he]
    have hle : sSup S ≤ y - d := csSup_le hne hub
    calc d ≤ y - sSup S := by linarith
      _ ≤ |y - sSup S| := le_abs_self _
      _ = |sSup S - y| := abs_sub_comm _ _

/-- If every element of `S` is at distance `≥ d` from `y`, so is `sInf S`. -/
theorem le_abs_sub_csInf {S : Set ℝ} (hne : S.Nonempty) (hbdd : BddBelow S) {y d : ℝ}
    (h : ∀ x ∈ S, d ≤ |x - y|) : d ≤ |sInf S - y| := by
  by_cases hex : ∃ x ∈ S, x ≤ y - d
  · obtain ⟨x, hxS, hx⟩ := hex
    have hle : sInf S ≤ y - d := (csInf_le hbdd hxS).trans hx
    calc d ≤ y - sInf S := by linarith
      _ ≤ |y - sInf S| := le_abs_self _
      _ = |sInf S - y| := abs_sub_comm _ _
  · push Not at hex
    have hlb : ∀ x ∈ S, y + d ≤ x := by
      intro x hxS
      have h1 := h x hxS
      have h2 := hex x hxS
      rcases abs_cases (x - y) with ⟨he, _⟩ | ⟨he, _⟩ <;> linarith [h1, he]
    have hle : y + d ≤ sInf S := le_csInf hne hlb
    calc d ≤ sInf S - y := by linarith
      _ ≤ |sInf S - y| := le_abs_self _

/-! ### The one-dimensional gap -/

/-- **The gap lemma.**  Let `A, B ⊆ ℝ` be `d`-separated (`d ≤ |x - y|` for `x ∈ A`, `y ∈ B`),
and let `u ∈ A`, `v ∈ B` with `u ≤ v`.  Then between `u` and `v` there is an *open* interval
`(s, t)` of length at least `d` that meets neither `A` nor `B`.

This is the whole content of the one-dimensional isoperimetric inequality; the rest is
arithmetic.  The witnesses are `s = sup (A ∩ [u,v])` and `t = inf (B ∩ [s,v])`: nothing of `A`
lies above `s` inside `[u,v]`, nothing of `B` lies below `t` inside `[s,v]`, and `t - s ≥ d`
because `s` and `t` inherit the separation from `A` and `B` by `le_abs_sub_csSup` /
`le_abs_sub_csInf`. -/
theorem exists_gap_of_separated {A B : Set ℝ} {d u v : ℝ}
    (huA : u ∈ A) (hvB : v ∈ B) (huv : u ≤ v)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, d ≤ |x - y|) :
    ∃ s t : ℝ, u ≤ s ∧ t ≤ v ∧ s + d ≤ t ∧ ∀ z ∈ Ioo s t, z ∉ A ∧ z ∉ B := by
  classical
  set S : Set ℝ := A ∩ Icc u v with hS
  have hSne : S.Nonempty := ⟨u, huA, ⟨le_rfl, huv⟩⟩
  have hSbdd : BddAbove S := ⟨v, fun x hx => hx.2.2⟩
  set s : ℝ := sSup S with hs
  have hus : u ≤ s := le_csSup hSbdd ⟨huA, ⟨le_rfl, huv⟩⟩
  have hsv : s ≤ v := csSup_le hSne fun x hx => hx.2.2
  -- `s` inherits the separation from `A`
  have hsB : ∀ y ∈ B, d ≤ |s - y| := fun y hy =>
    le_abs_sub_csSup hSne hSbdd fun x hx => hsep x hx.1 y hy
  set T : Set ℝ := B ∩ Icc s v with hT
  have hTne : T.Nonempty := ⟨v, hvB, ⟨hsv, le_rfl⟩⟩
  have hTbdd : BddBelow T := ⟨s, fun y hy => hy.2.1⟩
  set t : ℝ := sInf T with ht
  have hst : s ≤ t := le_csInf hTne fun y hy => hy.2.1
  have htv : t ≤ v := csInf_le hTbdd ⟨hvB, ⟨hsv, le_rfl⟩⟩
  -- `t` inherits the separation from `B`, hence is at distance `≥ d` from `s`
  have hts : d ≤ |t - s| := le_abs_sub_csInf hTne hTbdd fun y hy => by
    rw [abs_sub_comm]; exact hsB y hy.1
  have hdt : s + d ≤ t := by
    have : |t - s| = t - s := abs_of_nonneg (by linarith)
    rw [this] at hts; linarith
  refine ⟨s, t, hus, htv, hdt, fun z hz => ⟨?_, ?_⟩⟩
  · intro hzA
    have : z ∈ S := ⟨hzA, ⟨le_trans hus hz.1.le, le_trans hz.2.le htv⟩⟩
    exact absurd (le_csSup hSbdd this) (not_le.2 hz.1)
  · intro hzB
    have : z ∈ T := ⟨hzB, ⟨hz.1.le, le_trans hz.2.le htv⟩⟩
    exact absurd (csInf_le hTbdd this) (not_le.2 hz.2)

/-- Any two `d`-separated nonempty subsets of a **convex** `K ⊆ ℝ` leave a hole in `K` of
measure at least `d`.  (`Arlib.exists_gap_of_separated` plus `Real.volume_Ioo`; the gap lies
between a point of `A` and a point of `B`, hence in `K` because `K` is order-connected.) -/
theorem ofReal_le_volume_sdiff_of_separated {K A B : Set ℝ} {d : ℝ} (hK : Convex ℝ K)
    (hA : A ⊆ K) (hB : B ⊆ K) (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, d ≤ dist x y) :
    ENNReal.ofReal d ≤ volume ((K \ A) \ B) := by
  have hsep' : ∀ x ∈ A, ∀ y ∈ B, d ≤ |x - y| := by
    intro x hx y hy; simpa [Real.dist_eq] using hsep x hx y hy
  obtain ⟨u, huA⟩ := hAne
  obtain ⟨v, hvB⟩ := hBne
  -- the argument is symmetric in `A` and `B`; get the gap from whichever order holds
  have key : ∀ (A' B' : Set ℝ), A' ⊆ K → B' ⊆ K → ∀ u' ∈ A', ∀ v' ∈ B', u' ≤ v' →
      (∀ x ∈ A', ∀ y ∈ B', d ≤ |x - y|) →
      ENNReal.ofReal d ≤ volume ((K \ A') \ B') := by
    intro A' B' hA' hB' u' hu' v' hv' huv' hs'
    obtain ⟨s, t, hus, htv, hdt, hgap⟩ := exists_gap_of_separated hu' hv' huv' hs'
    have hIcc : Icc u' v' ⊆ K := hK.ordConnected.out (hA' hu') (hB' hv')
    have hsub : Ioo s t ⊆ (K \ A') \ B' := by
      intro z hz
      have hzK : z ∈ K := hIcc ⟨le_trans hus hz.1.le, le_trans hz.2.le htv⟩
      exact ⟨⟨hzK, (hgap z hz).1⟩, (hgap z hz).2⟩
    calc ENNReal.ofReal d ≤ ENNReal.ofReal (t - s) := by
          apply ENNReal.ofReal_le_ofReal; linarith
      _ = volume (Ioo s t) := (Real.volume_Ioo).symm
      _ ≤ volume ((K \ A') \ B') := measure_mono hsub
  rcases le_total u v with h | h
  · exact key A B hA hB u huA v hvB h hsep'
  · have := key B A hB hA v hvB u huA h (fun x hx y hy => by
      rw [abs_sub_comm]; exact hsep' y hy x hx)
    refine this.trans (le_of_eq ?_)
    congr 1
    ext z; simp only [mem_sdiff]; tauto

/-! ### Arithmetic in `ℝ≥0∞` -/

/-- `2ab ≤ L²` whenever `a + b ≤ L`, in `ℝ≥0∞`. -/
theorem two_mul_mul_le_sq_of_add_le {a b L : ℝ≥0∞} (h : a + b ≤ L) : 2 * (a * b) ≤ L ^ 2 := by
  rcases le_total a b with hab | hab
  · have h1 : 2 * a ≤ L := by
      refine le_trans ?_ h
      rw [two_mul]; exact add_le_add le_rfl hab
    have h2 : b ≤ L := le_trans (by simp) h
    calc 2 * (a * b) = 2 * a * b := by ring
      _ ≤ L * L := mul_le_mul' h1 h2
      _ = L ^ 2 := (sq L).symm
  · have h1 : 2 * b ≤ L := by
      refine le_trans ?_ h
      rw [two_mul]; exact add_le_add hab le_rfl
    have h2 : a ≤ L := le_trans (by simp) h
    calc 2 * (a * b) = 2 * b * a := by ring
      _ ≤ L * L := mul_le_mul' h1 h2
      _ = L ^ 2 := (sq L).symm

/-! ### The one-dimensional Dyer–Frieze inequality -/

/-- **The Dyer–Frieze isoperimetric inequality in dimension one, proved outright.**

Let `K ⊆ ℝ` be convex, and let `A, B ⊆ K` be measurable with `dist u v ≥ d > 0` for all
`u ∈ A`, `v ∈ B`.  Then

    2 d · vol A · vol B  ≤  vol (K \ A \ B) · (vol K)² .

This is exactly the displayed inequality `vol C · vol K ≥ (2d/D) · vol A · vol B` for `n = 1`,
where `D = diam K = vol K`, cleared of the denominator `D`.  No boundedness or finiteness
hypothesis is needed: if `vol K = ∞` the right-hand side is `∞` unless `vol (K \ A \ B) = 0`,
and that cannot happen for nonempty `A`, `B` (the hole has measure `≥ d > 0`).

Proof: the separated sets leave a hole of measure `≥ d`
(`Arlib.ofReal_le_volume_sdiff_of_separated`), and `2 · vol A · vol B ≤ (vol K)²` because `A`
and `B` are *disjoint* subsets of `K` (`Arlib.two_mul_mul_le_sq_of_add_le`). -/
theorem dyerFrieze_dim_one {K A B : Set ℝ} {d : ℝ} (hd : 0 < d) (hK : Convex ℝ K)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAK : A ⊆ K) (hBK : B ⊆ K)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, d ≤ dist x y) :
    ENNReal.ofReal (2 * d) * volume A * volume B ≤ volume ((K \ A) \ B) * volume K ^ 2 := by
  rcases A.eq_empty_or_nonempty with rfl | hAne
  · simp
  rcases B.eq_empty_or_nonempty with rfl | hBne
  · simp
  have hgap : ENNReal.ofReal d ≤ volume ((K \ A) \ B) :=
    ofReal_le_volume_sdiff_of_separated hK hAK hBK hAne hBne hsep
  -- `A` and `B` are disjoint, so their measures add up to at most `vol K`
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    have := hsep x hxA x hxB
    simp only [dist_self] at this
    linarith
  have hsum : volume A + volume B ≤ volume K := by
    rw [← measure_union hdisj hB]
    exact measure_mono (Set.union_subset hAK hBK)
  have harith : 2 * (volume A * volume B) ≤ volume K ^ 2 :=
    two_mul_mul_le_sq_of_add_le hsum
  calc ENNReal.ofReal (2 * d) * volume A * volume B
      = ENNReal.ofReal d * (2 * (volume A * volume B)) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        simp only [show ENNReal.ofReal 2 = 2 by
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.ofReal_natCast]; norm_num]
        ring
    _ ≤ volume ((K \ A) \ B) * volume K ^ 2 := mul_le_mul' hgap harith

/-- The `hiso`-shaped form of the one-dimensional case: with `κ = 2 / vol K` the inequality
reads `κ · d · vol A · vol B ≤ vol (K \ A \ B) · vol K`, which after multiplying through by
`vol K` is `Arlib.dyerFrieze_dim_one`.  Stated for `0 < vol K < ∞` so that the division is
harmless. -/
theorem dyerFrieze_dim_one' {K A B : Set ℝ} {d : ℝ} (hd : 0 < d) (hK : Convex ℝ K)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAK : A ⊆ K) (hBK : B ⊆ K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, d ≤ dist x y) :
    (2 / volume K) * ENNReal.ofReal d * volume A * volume B
      ≤ volume ((K \ A) \ B) * volume K := by
  have hmain := dyerFrieze_dim_one hd hK hA hB hAK hBK hsep
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)] at hmain
  have h2 : ENNReal.ofReal (2:ℝ) = 2 := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.ofReal_natCast]; norm_num
  rw [h2] at hmain
  have e1 : 2 / volume K * ENNReal.ofReal d * volume A * volume B
      = (2 * ENNReal.ofReal d * volume A * volume B) / volume K := by
    simp only [div_eq_mul_inv]; ring
  have e2 : volume ((K \ A) \ B) * volume K ^ 2 / volume K
      = volume ((K \ A) \ B) * volume K := by
    rw [sq, ← mul_assoc, ENNReal.mul_div_cancel_right hK0 hKtop]
  rw [e1, ← e2]
  exact ENNReal.div_le_div_right hmain _

/-- **The one-dimensional case, in exactly the shape of the `hiso` hypothesis** of
`Arlib.conductance_ballWalk_ge`.

With `κ = 2 / vol K` (i.e. `2/D`, since `D = diam K = vol K` in dimension one) and `π` the
uniform measure on `K`:

    κ · d · π A · π B  ≤  π (K \ A \ B).

This is `Arlib.dyerFrieze_dim_one` divided through by `(vol K)³`; it is recorded separately so
that the match with the consuming hypothesis is machine-checked and not asserted in prose. -/
theorem uniformOn_dyerFrieze_dim_one {K A B : Set ℝ} {d : ℝ} (hd : 0 < d) (hK : Convex ℝ K)
    (hKm : MeasurableSet K) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAK : A ⊆ K) (hBK : B ⊆ K) (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    (hsep : ∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) :
    (2 / volume K) * ENNReal.ofReal d * uniformOn volume K A * uniformOn volume K B
      ≤ uniformOn volume K ((K \ A) \ B) := by
  have hVinv : volume K * (volume K)⁻¹ = 1 := ENNReal.mul_inv_cancel hK0 hKtop
  have hCK : ((K \ A) \ B) ⊆ K := Set.Subset.trans Set.sdiff_subset Set.sdiff_subset
  have hCm : MeasurableSet ((K \ A) \ B) := (hKm.diff hA).diff hB
  have eA : uniformOn volume K A = volume A * (volume K)⁻¹ := by
    rw [uniformOn_apply volume hKm hA, Set.inter_eq_self_of_subset_left hAK, div_eq_mul_inv]
  have eB : uniformOn volume K B = volume B * (volume K)⁻¹ := by
    rw [uniformOn_apply volume hKm hB, Set.inter_eq_self_of_subset_left hBK, div_eq_mul_inv]
  have eC : uniformOn volume K ((K \ A) \ B) = volume ((K \ A) \ B) * (volume K)⁻¹ := by
    rw [uniformOn_apply volume hKm hCm, Set.inter_eq_self_of_subset_left hCK, div_eq_mul_inv]
  have hmain := dyerFrieze_dim_one hd hK hA hB hAK hBK hsep
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
    show ENNReal.ofReal (2:ℝ) = 2 by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.ofReal_natCast]; norm_num] at hmain
  rw [eA, eB, eC]
  have lhs_eq : 2 / volume K * ENNReal.ofReal d * (volume A * (volume K)⁻¹)
        * (volume B * (volume K)⁻¹)
      = (2 * ENNReal.ofReal d * volume A * volume B) * ((volume K)⁻¹) ^ 3 := by
    simp only [div_eq_mul_inv]; ring
  rw [lhs_eq]
  calc (2 * ENNReal.ofReal d * volume A * volume B) * ((volume K)⁻¹) ^ 3
      ≤ (volume ((K \ A) \ B) * volume K ^ 2) * ((volume K)⁻¹) ^ 3 :=
        mul_le_mul' hmain le_rfl
    _ = volume ((K \ A) \ B) * (volume K)⁻¹ * (volume K * (volume K)⁻¹) ^ 2 := by ring
    _ = volume ((K \ A) \ B) * (volume K)⁻¹ := by rw [hVinv, one_pow, mul_one]

/-! ### The free segment in `n` dimensions -/

section Segment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Every chord from `A` to `B` has a free stretch of length `d`.**

If `K` is convex, `A, B ⊆ K` are `d`-separated with `d > 0`, and `u ∈ A`, `v ∈ B`, then the
segment `[u,v]` — which lies in `K` — contains a subsegment `[p,q]` of length at least `d`
whose interior lies in `K` and meets neither `A` nor `B`.

This is `Arlib.exists_gap_of_separated` transported along the affine parametrisation
`τ ↦ u + τ·(v-u)` of the chord: the pullbacks of `A` and `B` are `(d/‖v-u‖)`-separated subsets
of `[0,1]`, so the one-dimensional gap lemma produces a parameter interval of length
`≥ d/‖v-u‖`, i.e. a subsegment of length `≥ d`. -/
theorem exists_freeSegment_of_separated {K A B : Set E} {d : ℝ} (hd : 0 < d)
    (hK : Convex ℝ K) (hA : A ⊆ K) (hB : B ⊆ K)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, d ≤ dist x y) {u v : E} (hu : u ∈ A) (hv : v ∈ B) :
    ∃ p q : E, p ∈ K ∧ q ∈ K ∧ d ≤ dist p q ∧
      ∀ z ∈ openSegment ℝ p q, z ∈ K ∧ z ∉ A ∧ z ∉ B := by
  classical
  have hduv : d ≤ dist u v := hsep u hu v hv
  have hr : 0 < ‖v - u‖ := by
    have h0 : (0:ℝ) < dist u v := lt_of_lt_of_le hd hduv
    rwa [dist_eq_norm, ← norm_neg, neg_sub] at h0
  set r : ℝ := ‖v - u‖ with hrdef
  set γ : ℝ → E := fun τ => u + τ • (v - u) with hγ
  have hγ0 : γ 0 = u := by simp [hγ]
  have hγ1 : γ 1 = v := by simp [hγ]
  have hγK : ∀ τ ∈ Icc (0:ℝ) 1, γ τ ∈ K := by
    intro τ hτ
    have heq : γ τ = (1 - τ) • u + τ • v := by simp only [hγ]; module
    rw [heq]
    exact hK (hA hu) (hB hv) (by linarith [hτ.2]) hτ.1 (by ring)
  have hdist : ∀ τ σ : ℝ, dist (γ τ) (γ σ) = |τ - σ| * r := by
    intro τ σ
    have heq : γ τ - γ σ = (τ - σ) • (v - u) := by simp only [hγ]; module
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs]
  set A' : Set ℝ := {τ | τ ∈ Icc (0:ℝ) 1 ∧ γ τ ∈ A} with hA'
  set B' : Set ℝ := {τ | τ ∈ Icc (0:ℝ) 1 ∧ γ τ ∈ B} with hB'
  have h0A : (0:ℝ) ∈ A' := ⟨⟨le_rfl, zero_le_one⟩, by rw [hγ0]; exact hu⟩
  have h1B : (1:ℝ) ∈ B' := ⟨⟨zero_le_one, le_rfl⟩, by rw [hγ1]; exact hv⟩
  have hd'pos : 0 < d / r := div_pos hd hr
  have hsep' : ∀ τ ∈ A', ∀ σ ∈ B', d / r ≤ |τ - σ| := by
    intro τ hτ σ hσ
    have hle := hsep _ hτ.2 _ hσ.2
    rw [hdist] at hle
    rw [div_le_iff₀ hr]
    exact hle
  obtain ⟨s, t, hs0, ht1, hdt, hgap⟩ := exists_gap_of_separated h0A h1B zero_le_one hsep'
  have hst : s < t := by linarith
  have hsmem : s ∈ Icc (0:ℝ) 1 := ⟨hs0, le_trans hst.le ht1⟩
  have htmem : t ∈ Icc (0:ℝ) 1 := ⟨le_trans hs0 hst.le, ht1⟩
  refine ⟨γ s, γ t, hγK s hsmem, hγK t htmem, ?_, ?_⟩
  · rw [hdist, abs_of_nonpos (by linarith : s - t ≤ 0)]
    have hle : d / r ≤ -(s - t) := by linarith
    calc d = d / r * r := (div_mul_cancel₀ d (ne_of_gt hr)).symm
      _ ≤ -(s - t) * r := mul_le_mul_of_nonneg_right hle hr.le
  · intro z hz
    rw [openSegment_eq_image] at hz
    obtain ⟨θ, hθ, rfl⟩ := hz
    dsimp only
    have heq : (1 - θ) • γ s + θ • γ t = γ ((1 - θ) * s + θ * t) := by
      simp only [hγ]; module
    rw [heq]
    set τ : ℝ := (1 - θ) * s + θ * t with hτ
    have hτs : s < τ := by nlinarith [hθ.1, hθ.2, hst]
    have hτt : τ < t := by nlinarith [hθ.1, hθ.2, hst]
    have hτmem : τ ∈ Icc (0:ℝ) 1 := ⟨le_trans hs0 hτs.le, le_trans hτt.le ht1⟩
    obtain ⟨hnA, hnB⟩ := hgap τ ⟨hτs, hτt⟩
    refine ⟨hγK τ hτmem, fun hmem => hnA ⟨hτmem, hmem⟩, fun hmem => hnB ⟨hτmem, hmem⟩⟩

end Segment

/-! ### The lossless merge of two proportional pieces -/

/-- **The bisection merge, over `ℝ`.**

If the target inequality `κ·aᵢ·bᵢ ≤ cᵢ·Vᵢ` holds on two pieces which split `A` and `B` in the
*same proportion* (`a₁ b₂ = a₂ b₁`), then it holds for the union with no loss at all:
`κ·(a₁+a₂)·(b₁+b₂) ≤ (c₁+c₂)·(V₁+V₂)`.

The cross terms are handled by AM–GM:
`c₁V₂ + c₂V₁ ≥ 2√(c₁V₁·c₂V₂) ≥ 2κ√(a₁b₁·a₂b₂) = 2κ√(a₁b₂·a₂b₁) = 2κ a₁b₂`,
the last equality being exactly the proportionality hypothesis.  Proportionality is not a
convenience: `2√(a₁b₂·a₂b₁) ≤ a₁b₂ + a₂b₁` is an equality **iff** `a₁b₂ = a₂b₁`, so any other
split loses. -/
theorem mul_add_le_of_proportional {κ a₁ b₁ c₁ V₁ a₂ b₂ c₂ V₂ : ℝ}
    (hκ : 0 ≤ κ) (ha₁ : 0 ≤ a₁) (hb₁ : 0 ≤ b₁) (hc₁ : 0 ≤ c₁) (hV₁ : 0 ≤ V₁)
    (ha₂ : 0 ≤ a₂) (hb₂ : 0 ≤ b₂) (hc₂ : 0 ≤ c₂) (hV₂ : 0 ≤ V₂)
    (h₁ : κ * a₁ * b₁ ≤ c₁ * V₁) (h₂ : κ * a₂ * b₂ ≤ c₂ * V₂)
    (hprop : a₁ * b₂ = a₂ * b₁) :
    κ * (a₁ + a₂) * (b₁ + b₂) ≤ (c₁ + c₂) * (V₁ + V₂) := by
  have hx : (0:ℝ) ≤ 2 * (κ * a₁ * b₂) := by positivity
  have hy : (0:ℝ) ≤ c₁ * V₂ + c₂ * V₁ := by positivity
  have hprod : (κ * a₁ * b₁) * (κ * a₂ * b₂) ≤ (c₁ * V₁) * (c₂ * V₂) :=
    mul_le_mul h₁ h₂ (by positivity) (by positivity)
  have e1 : (2 * (κ * a₁ * b₂)) ^ 2 = 4 * ((κ * a₁ * b₁) * (κ * a₂ * b₂)) := by
    linear_combination (4 * κ ^ 2 * a₁ * b₂) * hprop
  have e3 : 4 * ((c₁ * V₁) * (c₂ * V₂)) ≤ (c₁ * V₂ + c₂ * V₁) ^ 2 := by
    nlinarith [sq_nonneg (c₁ * V₂ - c₂ * V₁)]
  have hsq : (2 * (κ * a₁ * b₂)) ^ 2 ≤ (c₁ * V₂ + c₂ * V₁) ^ 2 := by
    rw [e1]; linarith [hprod, e3]
  have key : 2 * (κ * a₁ * b₂) ≤ c₁ * V₂ + c₂ * V₁ := by
    have hsqrt := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq hx, Real.sqrt_sq hy] at hsqrt
  have hprop' : κ * a₁ * b₂ = κ * a₂ * b₁ := by
    rw [mul_assoc, hprop, ← mul_assoc]
  linarith [h₁, h₂, key, hprop']

/-- **The bisection merge, over `ℝ≥0∞`**, with the finiteness guards spelled out.

Every one of the nine finiteness hypotheses is needed: `ENNReal.toReal ⊤ = 0` silently, so
without them the statement would be comparing zeros.  In the intended application all nine
quantities are bounded by `volume K < ∞`. -/
theorem mul_add_le_of_proportional_ennreal {κ a₁ b₁ c₁ V₁ a₂ b₂ c₂ V₂ : ℝ≥0∞}
    (hκ : κ ≠ ⊤) (ha₁ : a₁ ≠ ⊤) (hb₁ : b₁ ≠ ⊤) (hc₁ : c₁ ≠ ⊤) (hV₁ : V₁ ≠ ⊤)
    (ha₂ : a₂ ≠ ⊤) (hb₂ : b₂ ≠ ⊤) (hc₂ : c₂ ≠ ⊤) (hV₂ : V₂ ≠ ⊤)
    (h₁ : κ * a₁ * b₁ ≤ c₁ * V₁) (h₂ : κ * a₂ * b₂ ≤ c₂ * V₂)
    (hprop : a₁ * b₂ = a₂ * b₁) :
    κ * (a₁ + a₂) * (b₁ + b₂) ≤ (c₁ + c₂) * (V₁ + V₂) := by
  have hLtop : κ * (a₁ + a₂) * (b₁ + b₂) ≠ ⊤ := by finiteness
  have hRtop : (c₁ + c₂) * (V₁ + V₂) ≠ ⊤ := by finiteness
  rw [← ENNReal.toReal_le_toReal hLtop hRtop]
  have h₁' : (κ * a₁ * b₁).toReal ≤ (c₁ * V₁).toReal :=
    ENNReal.toReal_mono (by finiteness) h₁
  have h₂' : (κ * a₂ * b₂).toReal ≤ (c₂ * V₂).toReal :=
    ENNReal.toReal_mono (by finiteness) h₂
  have hprop' : (a₁ * b₂).toReal = (a₂ * b₁).toReal := by rw [hprop]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_add ha₁ ha₂, ENNReal.toReal_add hb₁ hb₂,
    ENNReal.toReal_add hc₁ hc₂, ENNReal.toReal_add hV₁ hV₂] at h₁' h₂' hprop' ⊢
  exact mul_add_le_of_proportional ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg h₁' h₂' hprop'

/-! ### The proportional cut, and the induction step -/

section Bisection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **A hyperplane cutting `A` and `B` in the same proportion exists, in every prescribed
direction.**

For measurable `A, B ⊆ K` with `K` bounded of finite measure and any nonzero functional `L`,
there is a level `s` with

    μ (A ∩ P) * μ (B \ P) = μ (A \ P) * μ (B ∩ P),   P = halfSpace L s true,

i.e. `A` and `B` are split in the *same* ratio by the hyperplane `{L = s}`.

The usual textbook proof of this fact invokes Borsuk–Ulam (ham sandwich): one bisects `A` with
a hyperplane of each normal direction and runs an antipodal argument on the sphere to also
bisect `B`.  That is unnecessary.  Apply `Arlib.exists_halfSpace_bisecting` — which needs no
sign hypothesis on the integrand — to the *signed* function

    f = μ(B) · 1_A  −  μ(A) · 1_B,

whose integral over `K` is exactly `0`.  Bisecting `∫_K f` therefore produces a side with
`∫ f = 0`, which is literally the proportionality identity.  Only one real condition has to be
met and the intermediate value theorem already meets it, so the direction `L` stays free. -/
theorem exists_halfSpace_proportional {A B K : Set E} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAK : A ⊆ K) (hBK : B ⊆ K)
    (hKb : Bornology.IsBounded K) (hKtop : μ K ≠ ⊤) {L : E →L[ℝ] ℝ} (hL : L ≠ 0) :
    ∃ s : ℝ, μ (A ∩ halfSpace L s true) * μ (B \ halfSpace L s true)
      = μ (A \ halfSpace L s true) * μ (B ∩ halfSpace L s true) := by
  classical
  haveI hfin : IsFiniteMeasure (μ.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hKtop⟩
  set α : ℝ := (μ A).toReal with hα
  set β : ℝ := (μ B).toReal with hβ
  set f : E → ℝ := fun x =>
    β * A.indicator (fun _ => (1:ℝ)) x - α * B.indicator (fun _ => (1:ℝ)) x with hfdef
  have hIA : IntegrableOn (A.indicator (fun _ => (1:ℝ))) K μ :=
    Integrable.indicator (integrable_const (1:ℝ)) hA
  have hIB : IntegrableOn (B.indicator (fun _ => (1:ℝ))) K μ :=
    Integrable.indicator (integrable_const (1:ℝ)) hB
  have hf : IntegrableOn f K μ := (hIA.const_mul β).sub (hIB.const_mul α)
  have hint : ∀ (S T : Set E), MeasurableSet S →
      ∫ x in T, S.indicator (fun _ => (1:ℝ)) x ∂μ = (μ (T ∩ S)).toReal := by
    intro S T hS
    rw [setIntegral_indicator hS, setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  have hFK : ∫ x in K, f x ∂μ = 0 := by
    rw [hfdef]
    rw [integral_sub (hIA.const_mul β) (hIB.const_mul α), integral_const_mul, integral_const_mul,
      hint A K hA, hint B K hB, Set.inter_eq_self_of_subset_right hAK,
      Set.inter_eq_self_of_subset_right hBK, ← hα, ← hβ]
    ring
  obtain ⟨s, hs⟩ := exists_halfSpace_bisecting (μ := μ) hf hKb hL
  rw [hFK] at hs
  set P : Set E := halfSpace L s true with hP
  have hPm : MeasurableSet P := measurableSet_halfSpace L s true
  have hEA : IntegrableOn (fun x => β * A.indicator (fun _ => (1:ℝ)) x) (K ∩ P) μ :=
    IntegrableOn.mono_set (hIA.const_mul β) Set.inter_subset_left
  have hEB : IntegrableOn (fun x => α * B.indicator (fun _ => (1:ℝ)) x) (K ∩ P) μ :=
    IntegrableOn.mono_set (hIB.const_mul α) Set.inter_subset_left
  have eA : (K ∩ P) ∩ A = A ∩ P := by
    ext x; simp only [Set.mem_inter_iff]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hAK h.1, h.2⟩, h.1⟩⟩
  have eB : (K ∩ P) ∩ B = B ∩ P := by
    ext x; simp only [Set.mem_inter_iff]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hBK h.1, h.2⟩, h.1⟩⟩
  have hkey : β * (μ (A ∩ P)).toReal - α * (μ (B ∩ P)).toReal = 0 := by
    have := hs
    rw [hfdef] at this
    rw [integral_sub hEA hEB, integral_const_mul, integral_const_mul, hint A _ hA, hint B _ hB,
      eA, eB] at this
    simpa using this
  -- the four pieces are finite
  have hfin' : ∀ S : Set E, S ⊆ K → μ S ≠ ⊤ := fun S hS =>
    ne_top_of_le_ne_top hKtop (measure_mono hS)
  have ha₁ : μ (A ∩ P) ≠ ⊤ := hfin' _ (Set.Subset.trans Set.inter_subset_left hAK)
  have ha₂ : μ (A \ P) ≠ ⊤ := hfin' _ (Set.Subset.trans Set.sdiff_subset hAK)
  have hb₁ : μ (B ∩ P) ≠ ⊤ := hfin' _ (Set.Subset.trans Set.inter_subset_left hBK)
  have hb₂ : μ (B \ P) ≠ ⊤ := hfin' _ (Set.Subset.trans Set.sdiff_subset hBK)
  -- the pieces add up
  have hsplitA : (μ (A ∩ P)).toReal + (μ (A \ P)).toReal = α := by
    rw [hα, ← ENNReal.toReal_add ha₁ ha₂, measure_inter_add_sdiff A hPm]
  have hsplitB : (μ (B ∩ P)).toReal + (μ (B \ P)).toReal = β := by
    rw [hβ, ← ENNReal.toReal_add hb₁ hb₂, measure_inter_add_sdiff B hPm]
  refine ⟨s, ?_⟩
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_mul]
  have hrw : (μ (A ∩ P)).toReal * (μ (B \ P)).toReal - (μ (A \ P)).toReal * (μ (B ∩ P)).toReal
      = β * (μ (A ∩ P)).toReal - α * (μ (B ∩ P)).toReal := by
    rw [← hsplitA, ← hsplitB]; ring
  linarith [hrw, hkey]

/-- **The induction step of the Dyer–Frieze proof, proved outright.**

Let `P` be *any* measurable set (the intended instance is a halfspace `halfSpace L s true`
produced by `Arlib.exists_halfSpace_proportional`).  If

* `P` splits `A` and `B` in the same proportion, and
* the target inequality holds on both sides of the cut, with the same constant `κ`,

then the target inequality holds on `K`.  The merge is **lossless**: no constant is given up
(`Arlib.mul_add_le_of_proportional_ennreal`).  Convexity plays no role in this step.

Note the hypotheses are written out inline; nothing here is a named predicate standing in for
an isoperimetric inequality.

## The residual goal

Together with `Arlib.exists_halfSpace_proportional` this gives, for every convex body `K` and
every direction `L`, a cut into two convex pieces on which the inequality is *equivalent* to the
inequality on `K`.  What it does **not** give is a well-founded recursion: the cut's position is
forced by the proportionality condition rather than by geometry, so neither `K ∩ P` nor `K \ P`
need be geometrically smaller than `K`, and the recursion does not decrease dimension either.
Closing the argument requires iterating the cut and passing to a limit in which the pieces
degenerate to one-dimensional needles, where `Arlib.dyerFrieze_dim_one` applies; that limit is
exactly the Localization Lemma, which is not available (see `Arlib.Convexity.LocalizationLemma`).

Concretely, what remains unproved is:

> for a convex body `K ⊆ E` of diameter `D`, measurable `A, B ⊆ K` with `d ≤ dist u v` for all
> `u ∈ A`, `v ∈ B`:
> `ENNReal.ofReal (2 * d / D) * μ A * μ B ≤ μ ((K \ A) \ B) * μ K`. -/
theorem dyerFrieze_step {A B K P : Set E} (hAK : A ⊆ K) (hBK : B ⊆ K) (hP : MeasurableSet P)
    (hKtop : μ K ≠ ⊤) {κ : ℝ≥0∞} (hκ : κ ≠ ⊤)
    (hprop : μ (A ∩ P) * μ (B \ P) = μ (A \ P) * μ (B ∩ P))
    (h₁ : κ * μ (A ∩ P) * μ (B ∩ P) ≤ μ (((K ∩ P) \ A) \ B) * μ (K ∩ P))
    (h₂ : κ * μ (A \ P) * μ (B \ P) ≤ μ (((K \ P) \ A) \ B) * μ (K \ P)) :
    κ * μ A * μ B ≤ μ ((K \ A) \ B) * μ K := by
  classical
  have hfin' : ∀ S : Set E, S ⊆ K → μ S ≠ ⊤ := fun S hS =>
    ne_top_of_le_ne_top hKtop (measure_mono hS)
  -- the cut splits `C = (K \ A) \ B` too
  have eC₁ : ((K ∩ P) \ A) \ B = ((K \ A) \ B) ∩ P := by
    ext x; simp only [Set.mem_sdiff, Set.mem_inter_iff]; tauto
  have eC₂ : ((K \ P) \ A) \ B = ((K \ A) \ B) \ P := by
    ext x; simp only [Set.mem_sdiff]; tauto
  rw [eC₁] at h₁
  rw [eC₂] at h₂
  rw [← measure_inter_add_sdiff A hP, ← measure_inter_add_sdiff B hP,
    ← measure_inter_add_sdiff K hP, ← measure_inter_add_sdiff ((K \ A) \ B) hP]
  refine mul_add_le_of_proportional_ennreal hκ
    (hfin' _ (Set.Subset.trans Set.inter_subset_left hAK))
    (hfin' _ (Set.Subset.trans Set.inter_subset_left hBK))
    (hfin' _ (Set.Subset.trans Set.inter_subset_left
      (Set.Subset.trans Set.sdiff_subset Set.sdiff_subset)))
    (hfin' _ Set.inter_subset_left)
    (hfin' _ (Set.Subset.trans Set.sdiff_subset hAK))
    (hfin' _ (Set.Subset.trans Set.sdiff_subset hBK))
    (hfin' _ (Set.Subset.trans Set.sdiff_subset
      (Set.Subset.trans Set.sdiff_subset Set.sdiff_subset)))
    (hfin' _ Set.sdiff_subset) h₁ h₂ hprop

/-- **One full step of the Dyer–Frieze induction, packaged.**

For every bounded `K` of finite measure, every measurable `A, B ⊆ K` and every direction `L`
there is a hyperplane `{L = s}` such that the target inequality on the two sides of the cut
implies the target inequality on `K`, with the same constant `κ`.  Both sides of the cut are
convex whenever `K` is (`Arlib.convex_halfSpace`), so the induction stays inside the class of
convex bodies.

Everything in this statement is proved; what is missing is only a *termination* argument for
the resulting recursion.  See the docstring of `Arlib.dyerFrieze_step`. -/
theorem exists_halfSpace_dyerFrieze_step {A B K : Set E} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAK : A ⊆ K) (hBK : B ⊆ K) (hKb : Bornology.IsBounded K)
    (hKtop : μ K ≠ ⊤) {L : E →L[ℝ] ℝ} (hL : L ≠ 0) {κ : ℝ≥0∞} (hκ : κ ≠ ⊤) :
    ∃ s : ℝ,
      κ * μ (A ∩ halfSpace L s true) * μ (B ∩ halfSpace L s true)
          ≤ μ (((K ∩ halfSpace L s true) \ A) \ B) * μ (K ∩ halfSpace L s true) →
      κ * μ (A \ halfSpace L s true) * μ (B \ halfSpace L s true)
          ≤ μ (((K \ halfSpace L s true) \ A) \ B) * μ (K \ halfSpace L s true) →
      κ * μ A * μ B ≤ μ ((K \ A) \ B) * μ K := by
  obtain ⟨s, hs⟩ := exists_halfSpace_proportional hA hB hAK hBK hKb hKtop hL
  exact ⟨s, fun h₁ h₂ =>
    dyerFrieze_step hAK hBK (measurableSet_halfSpace L s true) hKtop hκ hs h₁ h₂⟩

end Bisection

/-! ### Axiom audit -/

#print axioms le_abs_sub_csSup
#print axioms le_abs_sub_csInf
#print axioms exists_gap_of_separated
#print axioms ofReal_le_volume_sdiff_of_separated
#print axioms two_mul_mul_le_sq_of_add_le
#print axioms dyerFrieze_dim_one
#print axioms dyerFrieze_dim_one'
#print axioms uniformOn_dyerFrieze_dim_one
#print axioms exists_freeSegment_of_separated
#print axioms mul_add_le_of_proportional
#print axioms mul_add_le_of_proportional_ennreal
#print axioms exists_halfSpace_proportional
#print axioms dyerFrieze_step
#print axioms exists_halfSpace_dyerFrieze_step

end Arlib
