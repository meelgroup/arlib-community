/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.Isoperimetry

/-!
# Disjoint open enlargements for a *continuous* density, with no Lipschitz constant

`Arlib.gaussianRestricted_isoperimetry_of_openClosed_enlargement`
(`Arlib/Convexity/IsoOpenClosed.lean:1114`) reduces the measurable case of Cousins–Vempala's
`thm:iso` to the open/closed case, **given** disjoint open `U₁ ⊇ S₁`, `U₂ ⊇ S₂` on which the
separation hypothesis still holds.  Everything turns on producing that enlargement.

The route taken so far — `Arlib.exists_disjoint_open_enlargement_gaussianIndicator`
(`Arlib/Convexity/IsoIndicator.lean:405`) — produces it by pushing **every** pair into the
*metric* branch of the disjunction, which needs a global log-Lipschitz bound
`d_h(u,v) ≤ L·‖u − v‖`.  For the indicator density `1_K·γ` that is free (`1_K` is constant on
`K`, `γ` has `L = R/σ²`).  For the `ℓ`-weighted density it is the binder `hellLip`, which
`AUDIT.md` §0i argues has no witness with non-constant `ℓ` at the operative step, because
`hLσ` caps `L` far below the true rate `≈ √n·log 2/δ` forced by a corner
(`Arlib.MarkovChains.two_pow_mul_ell_cube_corner_le_one`).

**This file takes the other route: never convert the density branch.**  Each pair stays in
whichever branch it was already in, and both branches are allowed to degrade slightly.  The
only thing then needed is that `densDist h` does not move much under a small perturbation of
its two arguments — and that is free from *uniform continuity on a compact set*, provided the
thickening radius is chosen **after** the sets are fixed.  A global constant has to satisfy an
inequality against `σ`, `R` and `n`; a radius chosen second has nothing to satisfy.

Two facts make it work, and both are already in the tree for the density that matters:

* `h = ℓ·γ` is globally **continuous** (`Arlib.continuous_ell_toReal`) and log-concave
  (`Arlib.isLogConcave_ell_toReal`), and `Arlib.ellGaussian_isoperimetry_openClosed_logTwo` is
  stated for exactly that `h`, with no indicator — so the open/closed side needs no change.
* `{h = 0}` carries no `h`-mass, and that is precisely where the known obstruction lives: in
  `Arlib.exists_separated_no_disjoint_open_enlargement`
  (`Arlib/Convexity/IsoOpenClosed.lean:1205`) the touching is on the sphere, *inside* `{h = 0}`.
  Restricting to compact subsets of `{h > 0}` deletes it, at no cost in mass.

## What is proved here

* `Arlib.densDist_ge_sub_of_perturb` — the arithmetic core: if `a, b, a', b'` all lie in
  `[m, ∞)` with `m > 0` and `|a − a'|, |b − b'| ≤ η`, then

      |a − b| / max a b  −  3η/m  ≤  |a' − b'| / max a' b'.

  The constant `3` is not optimised; it comes from `|a − b| ≤ max a b`.
* `Arlib.densDist_ge_sub_of_perturb_fun` — the same for `densDist h` at perturbed points.
* **`Arlib.exists_disjoint_open_enlargement_of_continuous`** — the enlargement itself.  From
  disjoint compacts `C₁, C₂` inside `{h > 0}` carrying the disjunction at `(c₁, c₂)`, it
  produces disjoint **open** `U₁ ⊇ C₁`, `U₂ ⊇ C₂` carrying it at any strictly smaller
  `(c₁', c₂')`.  The only hypotheses on `h` are continuity and positivity on the compacts;
  there is no Lipschitz constant, no `σ`, no `R`, no dimension threshold.
* `Arlib.exists_disjoint_open_enlargement_of_continuous_witness` — non-vacuity, on an
  instance where the **metric branch is false** at the only pair, so the density branch
  carries the disjunction alone.  That instance is out of reach of the Lipschitz route.

## Scope — what this file is not

This is a statement about enlarging sets, not an isoperimetric inequality.  Two further
pieces are needed before `thm:iso` holds for measurable `S₁, S₂, S₃`, and they are in
separate files: inner regularity, to replace measurable `S₁, S₂` by compact subsets of
`{h > 0}` at negligible cost in mass, and a slack-tolerant form of
`Arlib.gaussianRestricted_isoperimetry_of_openClosed_enlargement`, which currently demands
*exact* supersets `S₁ ⊆ U₁`.  Nothing here may be quoted as a conductance, mixing-time or
runtime statement.

Every declaration is a `theorem`; there is no `def`, `structure`, `class` or `axiom` here.
-/

namespace Arlib

variable {E : Type*}

/-! ## 1. `|a − b| ≤ max a b` for nonnegative reals -/

/-- For nonnegative reals the gap never exceeds the larger value.  This is what makes the
constant in `Arlib.densDist_ge_sub_of_perturb` a `3` rather than something involving `X/M`. -/
theorem abs_sub_le_max_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |a - b| ≤ max a b := by
  rcases le_total a b with h | h
  · rw [abs_of_nonpos (by linarith)]
    calc -(a - b) = b - a := by ring
      _ ≤ b := by linarith
      _ ≤ max a b := le_max_right a b
  · rw [abs_of_nonneg (by linarith)]
    calc a - b ≤ a := by linarith
      _ ≤ max a b := le_max_left a b

/-! ## 2. The arithmetic core -/

/-- **The perturbation bound for `densDist`, as arithmetic on reals.**

If `a, b, a', b'` are all at least `m > 0` and the primed values are within `η` of the
unprimed ones, then the density distance drops by at most `3η/m`:

    |a − b| / max a b  −  3η/m  ≤  |a' − b'| / max a' b'.

Note what does **not** appear: no Lipschitz constant, no bound relating `η` to the ambient
geometry.  In the consumer, `m` is the minimum of a continuous positive `h` on a compact set
and `η` is supplied by uniform continuity *after* `m` is known, so the two are chosen in the
order that makes the estimate free. -/
theorem densDist_ge_sub_of_perturb {a b a' b' m η : ℝ} (hm : 0 < m)
    (ha : m ≤ a) (hb : m ≤ b) (ha' : m ≤ a') (hb' : m ≤ b')
    (hη : 0 ≤ η) (hda : |a - a'| ≤ η) (hdb : |b - b'| ≤ η) :
    |a - b| / max a b - 3 * η / m ≤ |a' - b'| / max a' b' := by
  set M : ℝ := max a b with hMdef
  set M' : ℝ := max a' b' with hM'def
  have hMa : a ≤ M := le_max_left a b
  have hMb : b ≤ M := le_max_right a b
  have hmM : m ≤ M := le_trans ha hMa
  have hM0 : 0 < M := lt_of_lt_of_le hm hmM
  have hmM' : m ≤ M' := le_trans ha' (le_max_left a' b')
  have hM'0 : 0 < M' := lt_of_lt_of_le hm hmM'
  have hX : |a - b| ≤ M :=
    abs_sub_le_max_of_nonneg (le_trans hm.le ha) (le_trans hm.le hb)
  -- the numerator can drop by at most `2η`
  have hnum : |a - b| - 2 * η ≤ |a' - b'| := by
    have e : a - b = (a - a') + ((a' - b') + (b' - b)) := by ring
    have h1 : |a - b| ≤ |a - a'| + |(a' - b') + (b' - b)| := by
      rw [e]; exact abs_add_le _ _
    have h2 : |(a' - b') + (b' - b)| ≤ |a' - b'| + |b' - b| := abs_add_le _ _
    have h3 : |b' - b| ≤ η := by rwa [abs_sub_comm]
    linarith
  -- the denominator can grow by at most `η`
  have hden : M' ≤ M + η := by
    have h1 : a' ≤ M + η := by
      have := (abs_le.mp hda).1
      linarith
    have h2 : b' ≤ M + η := by
      have := (abs_le.mp hdb).1
      linarith
    exact max_le h1 h2
  rcases le_or_gt (|a - b|) (2 * η) with hsmall | hbig
  · -- the unperturbed distance was already within the slack
    have h1 : |a - b| / M ≤ 3 * η / m := by
      have hle : |a - b| / M ≤ 2 * η / m := by
        calc |a - b| / M ≤ (2 * η) / M := by gcongr
          _ ≤ (2 * η) / m := by gcongr
      have : 2 * η / m ≤ 3 * η / m := by gcongr <;> linarith
      linarith
    have h2 : 0 ≤ |a' - b'| / M' := div_nonneg (abs_nonneg _) hM'0.le
    linarith
  · -- the main case: the numerator stays positive
    have hpos : 0 < |a - b| - 2 * η := by linarith
    have hMη : 0 < M + η := by linarith
    have hstep1 : (|a - b| - 2 * η) / (M + η) ≤ |a' - b'| / M' := by
      rw [div_le_div_iff₀ hMη hM'0]
      nlinarith [mul_le_mul_of_nonneg_right hnum hM'0.le,
        mul_le_mul_of_nonneg_left hden (abs_nonneg (a' - b'))]
    have hstep2 : |a - b| / M - 3 * η / m ≤ (|a - b| - 2 * η) / (M + η) := by
      have hkey : |a - b| / M - (|a - b| - 2 * η) / (M + η)
          = η * (|a - b| + 2 * M) / (M * (M + η)) := by
        field_simp
        ring
      have hb1 : η * (|a - b| + 2 * M) / (M * (M + η)) ≤ 3 * η / (M + η) := by
        rw [div_le_div_iff₀ (by positivity) hMη]
        have hfac : (|a - b| + 2 * M) * (M + η) ≤ (3 * M) * (M + η) :=
          mul_le_mul_of_nonneg_right (by linarith) hMη.le
        nlinarith [mul_le_mul_of_nonneg_left hfac hη]
      have hb2 : 3 * η / (M + η) ≤ 3 * η / m := by
        gcongr
        linarith
      linarith
    linarith

/-! ## 3. The same, at perturbed points of a function -/

/-- **`Arlib.densDist_ge_sub_of_perturb` in the shape the enlargement lemma consumes.**

`m` is a positive lower bound for `h` at the four points, `η` a common bound on the movement
of `h`.  No hypothesis relates `η` to any distance: the consumer picks the thickening radius
*after* both `m` and `η`. -/
theorem densDist_ge_sub_of_perturb_fun {h : E → ℝ} {u v u' v' : E} {m η : ℝ} (hm : 0 < m)
    (hu : m ≤ h u) (hv : m ≤ h v) (hu' : m ≤ h u') (hv' : m ≤ h v')
    (hη : 0 ≤ η) (hdu : |h u - h u'| ≤ η) (hdv : |h v - h v'| ≤ η) :
    densDist h u v - 3 * η / m ≤ densDist h u' v' :=
  densDist_ge_sub_of_perturb hm hu hv hu' hv' hη hdu hdv

/-! ## 4. The enlargement, with the radius chosen last -/

open Metric in
/-- **Disjoint open enlargements of two compact sets inside `{h > 0}`, at any strictly
weakened pair of thresholds — with no Lipschitz hypothesis.**

Let `C₁, C₂` be disjoint compact sets on which the continuous `h` is strictly positive, and
suppose every pair `(u,v) ∈ C₁ × C₂` satisfies the Cousins–Vempala disjunction at `(c₁, c₂)`:
either `c₁ ≤ ‖u − v‖` or `c₂ ≤ d_h(u,v)`.  Then for **any** strictly smaller pair
`(c₁', c₂')` there are disjoint open `U₁ ⊇ C₁`, `U₂ ⊇ C₂` on which every pair satisfies the
disjunction at `(c₁', c₂')`.

This is the replacement for `Arlib.exists_disjoint_open_enlargement_gaussianIndicator`
(`Arlib/Convexity/IsoIndicator.lean:405`).  That one converts the density branch into the
metric branch and therefore needs a global log-Lipschitz constant for `h`; this one leaves
each pair in its own branch, so it needs nothing but continuity.

**The order of choice is the whole trick.**  The thickening radius `ρ` is picked *after*

* `ρ₀`, a radius whose closed thickening of `C₁ ∪ C₂` still lies in the open set `{h > 0}`;
* `m > 0`, the minimum of `h` on that (compact) closed thickening `N`;
* `η := (c₂ − c₂')·m/3`, so that `3η/m` is exactly the density slack `c₂ − c₂'`;
* `ρ₁`, from **uniform** continuity of `h` on the compact `N` at tolerance `η`;
* `ρ₂`, a radius separating the disjoint compacts `C₁, C₂` (`Disjoint.exists_thickenings`);
* `(c₁ − c₁')/2`, the metric slack.

A global Lipschitz constant would have to be compared against `σ`, `R` and `n` — that is
`hLσ`, and it fails.  Here nothing is compared against anything: `ρ` is the minimum of five
positive numbers already in hand.

`Arlib.exists_separated_no_disjoint_open_enlargement`
(`Arlib/Convexity/IsoOpenClosed.lean:1205`) is not contradicted: there the two sets touch
*inside* `{h = 0}`, and the hypotheses `hC₁h`, `hC₂h` exclude exactly that.  In the consumer,
`C₁, C₂` come from inner regularity applied inside `{h > 0}`, which costs no mass because
`h` vanishes on the discarded part. -/
theorem exists_disjoint_open_enlargement_of_continuous {n : ℕ}
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hhc : Continuous h)
    {C₁ C₂ : Set (EuclideanSpace ℝ (Fin n))}
    (hC₁ : IsCompact C₁) (hC₂ : IsCompact C₂)
    (hC₁h : ∀ x ∈ C₁, 0 < h x) (hC₂h : ∀ x ∈ C₂, 0 < h x)
    (hdisj : Disjoint C₁ C₂)
    {c₁ c₂ c₁' c₂' : ℝ} (hlt₁ : c₁' < c₁) (hlt₂ : c₂' < c₂)
    (hsep : ∀ u ∈ C₁, ∀ v ∈ C₂, c₁ ≤ ‖u - v‖ ∨ c₂ ≤ densDist h u v) :
    ∃ U₁ U₂ : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen U₁ ∧ IsOpen U₂ ∧ Disjoint U₁ U₂ ∧ C₁ ⊆ U₁ ∧ C₂ ⊆ U₂ ∧
      ∀ u ∈ U₁, ∀ v ∈ U₂, c₁' ≤ ‖u - v‖ ∨ c₂' ≤ densDist h u v := by
  classical
  -- the degenerate cases, where one side of the disjunction is vacuous
  rcases Set.eq_empty_or_nonempty C₁ with rfl | hne₁
  · exact ⟨∅, Set.univ, isOpen_empty, isOpen_univ, by simp, by simp, by simp, by simp⟩
  rcases Set.eq_empty_or_nonempty C₂ with rfl | hne₂
  · exact ⟨Set.univ, ∅, isOpen_univ, isOpen_empty, by simp, by simp, by simp, by simp⟩
  set K : Set (EuclideanSpace ℝ (Fin n)) := C₁ ∪ C₂ with hKdef
  have hKc : IsCompact K := hC₁.union hC₂
  have hKpos : ∀ x ∈ K, 0 < h x := by
    intro x hx
    rcases hx with hx | hx
    · exact hC₁h x hx
    · exact hC₂h x hx
  have hopen : IsOpen {x : EuclideanSpace ℝ (Fin n) | 0 < h x} :=
    isOpen_lt continuous_const hhc
  -- `ρ₀`: a closed thickening of `K` still inside `{h > 0}`
  obtain ⟨ρ₀, hρ₀, hρ₀sub⟩ := hKc.exists_cthickening_subset_open hopen hKpos
  set N : Set (EuclideanSpace ℝ (Fin n)) := cthickening ρ₀ K with hNdef
  have hNc : IsCompact N := hKc.cthickening
  have hKN : K ⊆ N := self_subset_cthickening K
  have hNne : N.Nonempty := Set.Nonempty.mono (Set.subset_union_left.trans hKN) hne₁
  -- `m`: the minimum of `h` on `N`, positive because `N ⊆ {h > 0}`
  obtain ⟨x₀, hx₀N, hx₀min⟩ := hNc.exists_isMinOn hNne hhc.continuousOn
  set m : ℝ := h x₀ with hmdef
  have hm : 0 < m := hρ₀sub hx₀N
  have hmle : ∀ y ∈ N, m ≤ h y := fun y hy => isMinOn_iff.mp hx₀min y hy
  -- `η`: the movement of `h` that the density slack can absorb
  set η : ℝ := (c₂ - c₂') * m / 3 with hηdef
  have hηpos : 0 < η := by
    have hc : 0 < c₂ - c₂' := by linarith
    rw [hηdef]
    positivity
  have h3η : 3 * η / m = c₂ - c₂' := by
    rw [hηdef]
    field_simp
  -- `ρ₁`: uniform continuity of `h` on the compact `N`, at tolerance `η`
  obtain ⟨ρ₁, hρ₁, hρ₁unif⟩ :=
    Metric.uniformContinuousOn_iff.mp
      (hNc.uniformContinuousOn_of_continuous hhc.continuousOn) η hηpos
  -- `ρ₂`: the disjoint compacts are a positive distance apart
  obtain ⟨ρ₂, hρ₂, hρ₂disj⟩ := hdisj.exists_thickenings hC₁ hC₂.isClosed
  set ρ : ℝ := min (min ρ₀ ρ₁) (min ρ₂ ((c₁ - c₁') / 2)) with hρdef
  have hρρ₀ : ρ ≤ ρ₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρρ₁ : ρ ≤ ρ₁ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρρ₂ : ρ ≤ ρ₂ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρmet : ρ ≤ (c₁ - c₁') / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hρpos : 0 < ρ := by
    have hc : 0 < (c₁ - c₁') / 2 := by linarith
    rw [hρdef, lt_min_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨hρ₀, hρ₁⟩, hρ₂, hc⟩
  -- every thickening of a subset of `K` stays inside `N`
  have hUN : ∀ C : Set (EuclideanSpace ℝ (Fin n)), C ⊆ K → thickening ρ C ⊆ N := by
    intro C hC
    calc thickening ρ C ⊆ thickening ρ K := thickening_subset_of_subset ρ hC
      _ ⊆ thickening ρ₀ K := thickening_mono hρρ₀ K
      _ ⊆ N := thickening_subset_cthickening ρ₀ K
  refine ⟨thickening ρ C₁, thickening ρ C₂, isOpen_thickening, isOpen_thickening,
    hρ₂disj.mono (thickening_mono hρρ₂ C₁) (thickening_mono hρρ₂ C₂),
    self_subset_thickening hρpos C₁, self_subset_thickening hρpos C₂, ?_⟩
  intro u' hu' v' hv'
  obtain ⟨u, huC, hdu⟩ := mem_thickening_iff.mp hu'
  obtain ⟨v, hvC, hdv⟩ := mem_thickening_iff.mp hv'
  -- the four points all live in `N`
  have huN : u ∈ N := hKN (Set.mem_union_left _ huC)
  have hvN : v ∈ N := hKN (Set.mem_union_right _ hvC)
  have hu'N : u' ∈ N := hUN C₁ Set.subset_union_left hu'
  have hv'N : v' ∈ N := hUN C₂ Set.subset_union_right hv'
  -- the movement of `h` between them is at most `η`
  have hmoveu : |h u - h u'| ≤ η := by
    have hd : dist u u' < ρ₁ := by
      rw [dist_comm]
      exact lt_of_lt_of_le hdu hρρ₁
    have := hρ₁unif u huN u' hu'N hd
    rw [Real.dist_eq] at this
    exact this.le
  have hmovev : |h v - h v'| ≤ η := by
    have hd : dist v v' < ρ₁ := by
      rw [dist_comm]
      exact lt_of_lt_of_le hdv hρρ₁
    have := hρ₁unif v hvN v' hv'N hd
    rw [Real.dist_eq] at this
    exact this.le
  rcases hsep u huC v hvC with hmetric | hdens
  · -- the metric branch degrades from `c₁` to `c₁'`
    left
    have hnu : ‖u - u'‖ < ρ := by rw [← dist_eq_norm, dist_comm]; exact hdu
    have hnv : ‖v' - v‖ < ρ := by rw [← dist_eq_norm]; exact hdv
    have htri : ‖u - v‖ ≤ ‖u - u'‖ + ‖u' - v'‖ + ‖v' - v‖ := by
      calc ‖u - v‖ = ‖(u - u') + ((u' - v') + (v' - v))‖ := by congr 1; abel
        _ ≤ ‖u - u'‖ + ‖(u' - v') + (v' - v)‖ := norm_add_le _ _
        _ ≤ ‖u - u'‖ + (‖u' - v'‖ + ‖v' - v‖) := by gcongr; exact norm_add_le _ _
        _ = ‖u - u'‖ + ‖u' - v'‖ + ‖v' - v‖ := by ring
    linarith
  · -- the density branch degrades from `c₂` to `c₂'`, by exactly `3η/m`
    right
    have hkey := densDist_ge_sub_of_perturb_fun (h := h) hm (hmle u huN) (hmle v hvN)
      (hmle u' hu'N) (hmle v' hv'N) hηpos.le hmoveu hmovev
    rw [h3η] at hkey
    linarith

/-! ## 5. Non-vacuity (`CLAUDE.md` §11) -/

open Metric in
/-- **The hypothesis bundle of `Arlib.exists_disjoint_open_enlargement_of_continuous` is
satisfiable — on an instance where the *metric* branch fails.**

`n = 1`, `h x = 1/(1 + ‖x‖)`, `C₁ = {0}`, `C₂ = {e₀}`, `c₁ = 2`, `c₂ = 1/2`, weakened to
`c₁' = 1`, `c₂' = 1/4`.  At the only pair, `‖0 − e₀‖ = 1 < 2 = c₁`, so the metric branch is
**false**, and the disjunction holds only because `d_h(0,e₀) = 1/2 = c₂`.

That is the point of the witness, and the reason the last conjunct is stated: this instance
is out of reach of `Arlib.exists_disjoint_open_enlargement_gaussianIndicator`, whose whole
method is to discharge the metric branch.  It also shows the theorem is not vacuously about
its two degenerate branches — both compacts are nonempty. -/
theorem exists_disjoint_open_enlargement_of_continuous_witness :
    ∃ (k : ℕ) (h : EuclideanSpace ℝ (Fin k) → ℝ)
      (C₁ C₂ : Set (EuclideanSpace ℝ (Fin k))) (c₁ c₂ c₁' c₂' : ℝ),
      Continuous h ∧ IsCompact C₁ ∧ IsCompact C₂ ∧
      (∀ x ∈ C₁, 0 < h x) ∧ (∀ x ∈ C₂, 0 < h x) ∧ Disjoint C₁ C₂ ∧
      C₁.Nonempty ∧ C₂.Nonempty ∧ c₁' < c₁ ∧ c₂' < c₂ ∧
      (∀ u ∈ C₁, ∀ v ∈ C₂, c₁ ≤ ‖u - v‖ ∨ c₂ ≤ densDist h u v) ∧
      (∃ u ∈ C₁, ∃ v ∈ C₂, ¬ c₁ ≤ ‖u - v‖) ∧
      ∃ U₁ U₂ : Set (EuclideanSpace ℝ (Fin k)),
        IsOpen U₁ ∧ IsOpen U₂ ∧ Disjoint U₁ U₂ ∧ C₁ ⊆ U₁ ∧ C₂ ⊆ U₂ ∧
        ∀ u ∈ U₁, ∀ v ∈ U₂, c₁' ≤ ‖u - v‖ ∨ c₂' ≤ densDist h u v := by
  classical
  set e : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ) with hedef
  have hen : ‖e‖ = 1 := by rw [hedef, PiLp.norm_single]; norm_num
  set h : EuclideanSpace ℝ (Fin 1) → ℝ := fun x => 1 / (1 + ‖x‖) with hhdef
  have hcont : Continuous h := by
    rw [hhdef]
    exact Continuous.div continuous_const (by fun_prop) (fun x => by positivity)
  have hpos : ∀ x : EuclideanSpace ℝ (Fin 1), 0 < h x := by
    intro x; rw [hhdef]; positivity
  have hh0 : h 0 = 1 := by rw [hhdef]; simp
  have hhe : h e = 1 / 2 := by rw [hhdef]; simp only [hen]; norm_num
  have hne : (0 : EuclideanSpace ℝ (Fin 1)) ≠ e := by
    intro hc
    rw [← hc, norm_zero] at hen
    norm_num at hen
  have hdist : ‖(0 : EuclideanSpace ℝ (Fin 1)) - e‖ = 1 := by
    rw [zero_sub, norm_neg, hen]
  have hdens : densDist h 0 e = 1 / 2 := by
    rw [densDist, hh0, hhe]
    rw [max_eq_left (by norm_num : (1 : ℝ) / 2 ≤ 1)]
    norm_num
  have hsep : ∀ u ∈ ({0} : Set (EuclideanSpace ℝ (Fin 1))), ∀ v ∈ ({e} : Set _),
      (2 : ℝ) ≤ ‖u - v‖ ∨ (1 / 2 : ℝ) ≤ densDist h u v := by
    intro u hu v hv
    rw [Set.mem_singleton_iff] at hu hv
    subst hu; subst hv
    exact Or.inr (by rw [hdens])
  obtain ⟨U₁, U₂, hU₁, hU₂, hUd, hs₁, hs₂, hUsep⟩ :=
    exists_disjoint_open_enlargement_of_continuous (n := 1) (h := h) hcont
      isCompact_singleton isCompact_singleton
      (fun x _ => hpos x) (fun x _ => hpos x)
      (Set.disjoint_singleton.mpr hne)
      (by norm_num : (1 : ℝ) < 2) (by norm_num : (1 / 4 : ℝ) < 1 / 2) hsep
  refine ⟨1, h, {0}, {e}, 2, 1 / 2, 1, 1 / 4, hcont, isCompact_singleton, isCompact_singleton,
    fun x _ => hpos x, fun x _ => hpos x, Set.disjoint_singleton.mpr hne,
    Set.singleton_nonempty _, Set.singleton_nonempty _, by norm_num, by norm_num, hsep,
    ⟨0, rfl, e, rfl, ?_⟩, U₁, U₂, hU₁, hU₂, hUd, hs₁, hs₂, hUsep⟩
  rw [hdist]
  norm_num

section AxiomCheck

#print axioms Arlib.abs_sub_le_max_of_nonneg
#print axioms Arlib.densDist_ge_sub_of_perturb
#print axioms Arlib.densDist_ge_sub_of_perturb_fun
#print axioms Arlib.exists_disjoint_open_enlargement_of_continuous
#print axioms Arlib.exists_disjoint_open_enlargement_of_continuous_witness

end AxiomCheck

end Arlib
