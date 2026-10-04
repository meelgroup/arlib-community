import Nfa.Interface.Pseudocode

/-!
# Real expectations under finitely supported PMFs

`PmfExpect.ex μ f = Σ_a μ(a) f(a)`, the expectation of a real-valued `f` under a PMF
`μ`.  Every law in the analysis of `countNFAcore` (`reduce`, `drawAll`, the core loop)
has finite support, and under that hypothesis `ex` is linear, commutes with `bind`
and `map`, and factorises over the independent draws of `Pseudocode.drawAll`
(`ex_drawAll_prod`).  This is the expectation the paper's tower-rule arguments
(analysis.tex:156-370) are carried out with.
-/

set_option autoImplicit false

open scoped ENNReal

namespace Nfa.Analysis.PmfExpect

variable {α β : Type}

/-- `E_μ[f]`.

INTERNAL: the real expectation of analysis.tex:156-162, for a PMF.
TEXLINE: analysis.tex:156-162 -/
noncomputable def ex (μ : PMF α) (f : α → ℝ) : ℝ := ∑' a, (μ a).toReal * f a

/-- `ex` as a finite sum over any finset containing the support.

INTERNAL: expectation bookkeeping.
TEXLINE: analysis.tex:156-162 -/
theorem ex_eq_sum (μ : PMF α) (f : α → ℝ) (s : Finset α) (hs : ∀ a, a ∉ s → μ a = 0) :
    ex μ f = ∑ a ∈ s, (μ a).toReal * f a :=
  tsum_eq_sum fun a ha => by simp [hs a ha]

/-- Outside a finite support's `toFinset` the mass is `0`.

INTERNAL: expectation bookkeeping.
TEXLINE: analysis.tex:156-162 -/
theorem apply_eq_zero_of_not_mem {μ : PMF α} (hμ : μ.support.Finite) (a : α)
    (ha : a ∉ hμ.toFinset) : μ a = 0 := by
  rw [Set.Finite.mem_toFinset] at ha
  exact (PMF.apply_eq_zero_iff μ a).2 ha

/-- Total mass `1`, as a finite real sum.

INTERNAL: expectation bookkeeping.
TEXLINE: analysis.tex:156-162 -/
theorem sum_toReal_eq_one (μ : PMF α) (s : Finset α) (hs : ∀ a, a ∉ s → μ a = 0) :
    ∑ a ∈ s, (μ a).toReal = 1 := by
  have h : ∑' a, μ a = ∑ a ∈ s, μ a := tsum_eq_sum hs
  rw [← ENNReal.toReal_sum fun a _ => PMF.apply_ne_top μ a, ← h, PMF.tsum_coe,
    ENNReal.toReal_one]

/-- `E[f] = E[g]` when `f = g` on the support.

INTERNAL: expectation bookkeeping.
TEXLINE: analysis.tex:156-162 -/
theorem ex_congr (μ : PMF α) {f g : α → ℝ} (h : ∀ a ∈ μ.support, f a = g a) :
    ex μ f = ex μ g := by
  unfold ex
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ μ.support
  · rw [h a ha]
  · rw [(PMF.apply_eq_zero_iff μ a).2 ha]; simp

/-- `E[c] = c`.

INTERNAL: expectation bookkeeping.
TEXLINE: analysis.tex:156-162 -/
theorem ex_const (μ : PMF α) (hμ : μ.support.Finite) (c : ℝ) : ex μ (fun _ => c) = c := by
  rw [ex_eq_sum μ _ hμ.toFinset (apply_eq_zero_of_not_mem hμ), ← Finset.sum_mul,
    sum_toReal_eq_one μ _ (apply_eq_zero_of_not_mem hμ), one_mul]

/-- `E[c f] = c E[f]`.

INTERNAL: expectation bookkeeping.
TEXLINE: analysis.tex:156-162 -/
theorem ex_mul_left (μ : PMF α) (c : ℝ) (f : α → ℝ) : ex μ (fun a => c * f a) = c * ex μ f := by
  unfold ex
  rw [← tsum_mul_left]
  exact tsum_congr fun a => by ring

/-- `E[f c] = E[f] c`.

INTERNAL: expectation bookkeeping.
TEXLINE: analysis.tex:156-162 -/
theorem ex_mul_right (μ : PMF α) (c : ℝ) (f : α → ℝ) : ex μ (fun a => f a * c) = ex μ f * c := by
  rw [mul_comm (ex μ f) c, ← ex_mul_left]
  exact tsum_congr fun a => by ring

/-- `E[f + g] = E[f] + E[g]`.

INTERNAL: expectation bookkeeping.
TEXLINE: analysis.tex:156-162 -/
theorem ex_add (μ : PMF α) (hμ : μ.support.Finite) (f g : α → ℝ) :
    ex μ (fun a => f a + g a) = ex μ f + ex μ g := by
  simp only [ex_eq_sum μ _ hμ.toFinset (apply_eq_zero_of_not_mem hμ), mul_add,
    Finset.sum_add_distrib]

/-- `E[f − g] = E[f] − E[g]`.

INTERNAL: expectation bookkeeping.
TEXLINE: analysis.tex:156-162 -/
theorem ex_sub (μ : PMF α) (hμ : μ.support.Finite) (f g : α → ℝ) :
    ex μ (fun a => f a - g a) = ex μ f - ex μ g := by
  simp only [ex_eq_sum μ _ hμ.toFinset (apply_eq_zero_of_not_mem hμ), mul_sub,
    Finset.sum_sub_distrib]

/-- `E[Σ_k f_k] = Σ_k E[f_k]`.

INTERNAL: expectation bookkeeping.
TEXLINE: analysis.tex:156-162 -/
theorem ex_sum {ι : Type} (μ : PMF α) (hμ : μ.support.Finite) (K : Finset ι)
    (f : ι → α → ℝ) : ex μ (fun a => ∑ k ∈ K, f k a) = ∑ k ∈ K, ex μ (f k) := by
  simp only [ex_eq_sum μ _ hμ.toFinset (apply_eq_zero_of_not_mem hμ), Finset.mul_sum]
  exact Finset.sum_comm

/-- `E[f] ≤ E[g]` when `f ≤ g` on the support.

INTERNAL: expectation bookkeeping.
TEXLINE: analysis.tex:156-162 -/
theorem ex_mono (μ : PMF α) (hμ : μ.support.Finite) {f g : α → ℝ}
    (h : ∀ a ∈ μ.support, f a ≤ g a) : ex μ f ≤ ex μ g := by
  rw [ex_eq_sum μ _ hμ.toFinset (apply_eq_zero_of_not_mem hμ),
    ex_eq_sum μ _ hμ.toFinset (apply_eq_zero_of_not_mem hμ)]
  refine Finset.sum_le_sum fun a ha => ?_
  rw [Set.Finite.mem_toFinset] at ha
  exact mul_le_mul_of_nonneg_left (h a ha) ENNReal.toReal_nonneg

/-- `E[f] ≥ 0` when `f ≥ 0` on the support.

INTERNAL: expectation bookkeeping.
TEXLINE: analysis.tex:156-162 -/
theorem ex_nonneg (μ : PMF α) {f : α → ℝ} (h : ∀ a ∈ μ.support, 0 ≤ f a) : 0 ≤ ex μ f := by
  unfold ex
  refine tsum_nonneg fun a => ?_
  by_cases ha : a ∈ μ.support
  · exact mul_nonneg ENNReal.toReal_nonneg (h a ha)
  · rw [(PMF.apply_eq_zero_iff μ a).2 ha]; simp

/-- `E_{pure a}[f] = f a`.

INTERNAL: expectation bookkeeping.
TEXLINE: analysis.tex:156-162 -/
theorem ex_pure (a : α) (f : α → ℝ) : ex (PMF.pure a) f = f a := by
  classical
  rw [ex_eq_sum _ f {a} fun b hb => by
    rw [Finset.mem_singleton] at hb; simp [PMF.pure_apply, hb]]
  simp

/-- Finite support is preserved by `bind`.

INTERNAL: expectation bookkeeping.
TEXLINE: analysis.tex:156-162 -/
theorem support_bind_finite (μ : PMF α) (K : α → PMF β) (hμ : μ.support.Finite)
    (hK : ∀ a ∈ μ.support, (K a).support.Finite) : (μ.bind K).support.Finite := by
  rw [PMF.support_bind]
  exact hμ.biUnion hK

/-- Finite support is preserved by `map`.

INTERNAL: expectation bookkeeping.
TEXLINE: analysis.tex:156-162 -/
theorem support_map_finite (μ : PMF α) (g : α → β) (hμ : μ.support.Finite) :
    (μ.map g).support.Finite := by
  rw [PMF.support_map]
  exact hμ.image g

/-- **Tower rule**: `E_{μ >>= K}[f] = E_μ[a ↦ E_{K a}[f]]`.

INTERNAL: the tower rule of analysis.tex:170-175, for a kernel.
TEXLINE: analysis.tex:170-175 -/
theorem ex_bind (μ : PMF α) (K : α → PMF β) (hμ : μ.support.Finite)
    (hK : ∀ a ∈ μ.support, (K a).support.Finite) (f : β → ℝ) :
    ex (μ.bind K) f = ex μ (fun a => ex (K a) f) := by
  classical
  set s := hμ.toFinset
  have hS := support_bind_finite μ K hμ hK
  set S := hS.toFinset
  have hs0 : ∀ a, a ∉ s → μ a = 0 := apply_eq_zero_of_not_mem hμ
  have hKS : ∀ a ∈ s, ∀ b, b ∉ S → K a b = 0 := by
    intro a ha b hb
    rw [Set.Finite.mem_toFinset, PMF.support_bind] at hb
    rw [Set.Finite.mem_toFinset] at ha
    by_contra h
    exact hb (Set.mem_biUnion ha ((PMF.mem_support_iff _ _).2 h))
  have hbind : ∀ b, ((μ.bind K) b).toReal = ∑ a ∈ s, (μ a).toReal * (K a b).toReal := by
    intro b
    rw [PMF.bind_apply, tsum_eq_sum (s := s) fun a ha => by simp [hs0 a ha],
      ENNReal.toReal_sum fun a _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
        (PMF.apply_ne_top _ _)]
    simp only [ENNReal.toReal_mul]
  rw [ex_eq_sum _ f S (apply_eq_zero_of_not_mem hS), ex_eq_sum μ _ s hs0]
  simp only [hbind, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [ex_eq_sum (K a) f S (hKS a ha), Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- `E_{map g μ}[f] = E_μ[f ∘ g]`.

INTERNAL: expectation bookkeeping.
TEXLINE: analysis.tex:156-162 -/
theorem ex_map (μ : PMF α) (g : α → β) (hμ : μ.support.Finite) (f : β → ℝ) :
    ex (μ.map g) f = ex μ (fun a => f (g a)) := by
  rw [← PMF.bind_pure_comp, ex_bind μ _ hμ (fun a _ => by simp [PMF.support_pure])]
  simp only [Function.comp, ex_pure]

/-- The ENNReal expectation of a nonnegative `f` is the real one.

INTERNAL: expectation bookkeeping.
TEXLINE: analysis.tex:156-162 -/
theorem tsum_ofReal_eq (μ : PMF α) (hμ : μ.support.Finite) (f : α → ℝ)
    (hf : ∀ a ∈ μ.support, 0 ≤ f a) :
    ∑' a, μ a * ENNReal.ofReal (f a) = ENNReal.ofReal (ex μ f) := by
  rw [ex_eq_sum μ _ hμ.toFinset (apply_eq_zero_of_not_mem hμ),
    tsum_eq_sum (s := hμ.toFinset) fun a ha => by simp [apply_eq_zero_of_not_mem hμ a ha],
    ENNReal.ofReal_sum_of_nonneg fun a ha => mul_nonneg ENNReal.toReal_nonneg
      (hf a ((Set.Finite.mem_toFinset hμ).1 ha))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]

/-! ## Independent draws -/

open Nfa.Pseudocode

/-- `drawAll` has finite support when every draw does.

INTERNAL: expectation bookkeeping.
TEXLINE: algorithm.tex:49-56 -/
theorem drawAll_support_finite {ι : Type} [DecidableEq ι] (f : ι → PMF β) (d : β)
    (hf : ∀ i, (f i).support.Finite) : ∀ L : List ι, (drawAll f d L).support.Finite
  | [] => by simp [drawAll, PMF.support_pure]
  | i :: is => by
      simp only [drawAll]
      exact support_bind_finite _ _ (hf i) fun b _ =>
        support_map_finite _ _ (drawAll_support_finite f d hf is)

/-- Off the list, `drawAll` reads the default.

INTERNAL: expectation bookkeeping.
TEXLINE: algorithm.tex:49-56 -/
theorem drawAll_support_off {ι : Type} [DecidableEq ι] (f : ι → PMF β) (d : β) :
    ∀ (L : List ι) (g : ι → β), g ∈ (drawAll f d L).support → ∀ i ∉ L, g i = d
  | [], g, hg, i, _ => by
      simp only [drawAll, PMF.support_pure, Set.mem_singleton_iff] at hg
      rw [hg]
  | j :: js, g, hg, i, hi => by
      simp only [drawAll, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hg
      obtain ⟨b, _, g', hg', rfl⟩ := hg
      rw [List.mem_cons, not_or] at hi
      rw [Function.update_of_ne hi.1]
      exact drawAll_support_off f d js g' hg' i hi.2

/-- **Independence of `drawAll`**: the expectation of a product of functions of distinct
coordinates is the product of the expectations.

INTERNAL: the independence of the coins of `reduce`, the `α` repetitions and the
predecessors' draws, used throughout analysis.tex:221-370.
TEXLINE: analysis.tex:221-370 -/
theorem ex_drawAll_prod {ι : Type} [DecidableEq ι] (f : ι → PMF β) (d : β)
    (hf : ∀ i, (f i).support.Finite) (φ : ι → β → ℝ) :
    ∀ L : List ι, L.Nodup →
      ex (drawAll f d L) (fun g => ∏ i ∈ L.toFinset, φ i (g i)) =
        ∏ i ∈ L.toFinset, ex (f i) (φ i)
  | [], _ => by simp [drawAll, ex_pure]
  | i :: is, hL => by
      rw [List.nodup_cons] at hL
      have ih := ex_drawAll_prod f d hf φ is hL.2
      have hi : i ∉ is.toFinset := by rw [List.mem_toFinset]; exact hL.1
      simp only [drawAll, List.toFinset_cons]
      rw [ex_bind _ _ (hf i) fun b _ =>
        support_map_finite _ _ (drawAll_support_finite f d hf is)]
      rw [Finset.prod_insert hi, ← ex_mul_right]
      refine ex_congr _ fun b _ => ?_
      rw [ex_map _ _ (drawAll_support_finite f d hf is), ← ih, ← ex_mul_left]
      refine ex_congr _ fun g _ => ?_
      rw [Finset.prod_insert hi, Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun j hj => ?_
      have : j ≠ i := fun h => hi (h ▸ hj)
      rw [Function.update_of_ne this]

end Nfa.Analysis.PmfExpect

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · finite-support expectation API and `drawAll` independence
-/
