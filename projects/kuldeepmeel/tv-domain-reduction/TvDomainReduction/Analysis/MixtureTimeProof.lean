import TvDomainReduction.Model.Prior
import TvDomainReduction.Model.Run
import TvDomainReduction.Meta.ModelClosure
import TvDomainReduction.Analysis.CorrectnessProof
import TvDomainReduction.Analysis.SpaceProof
import TvDomainReduction.Analysis.TimeProof
import TvDomainReduction.Interface.Encoding
import TvDomainReduction.Interface.Pseudocode
import TvDomainReduction.Interface.ProgramModel

/-!
Proof-side owner for the running-time half of `thm:main_fptas` (main.tex:794): one
polynomial `c · (n k q (1/ε)(1 + log(1/η)))^D`, with `c` and `D` depending only on the
family's constants, bounds the tally of every outcome of `Run.runLawMix`.

The run is `Program.runDense` on the compiled caterpillar `mixPair M`, so the per-region
accounting is `TimeProof.build_steps_le` reused verbatim, with `B = q + M` rows and width
`W = k₁ + k₂`.  The mixture-specific facts are structural: the caterpillar has `n − 1`
internal regions, `k` gates per region, size at most `n (2k + k³ + kq)`, and retained
budget at most `prior.size k`, which the prior's size bound at `δ = ε/(3n)`, `η' = η/n`
makes `≤ 18 C_size · X⁸` where `X = n k q (1/ε)(1 + log(1/η))`.  `IsStochastic` is used
only to make every factor of `X` at least one (`k₁, k₂ ≥ 1` from the weights summing to
one, `q ≥ 1` from the first table being a pmf); without it `q = 0` would make the
right-hand side vanish while the solver is still charged.  The solver's `Õ` factor is
bounded through `SparsifyFamily.Member.polylog_le`, its `(2W)^ω` through `ω ≤ 2.4 ≤ 3`.
The result is `D = 20 + 17 · plDeg`, and `c` is explicit in the proof.  `hprior` is not
used.
-/

set_option autoImplicit false

namespace TvDomainReduction.Analysis

open Arlib.Approximation
open Arlib.Computation
open Arlib.KnowledgeCompilation.Probabilistic
open TvDomainReduction.Model.Operations

/-- INTERNAL: the leaf domains of the caterpillar over coordinates `0..t` are bounded by any
common bound on `dom 0, …, dom t`; at `t = n − 1` this is `q`.
TEXLINE: main.tex:794 -/
theorem mixTime_catVtree_leafDomMax_le (dom : ℕ → ℕ) (Q : ℕ) :
    ∀ t : ℕ, (∀ s ≤ t, dom s ≤ Q) → leafDomMax (catVtree dom t) ≤ Q
  | 0, h => by simpa [catVtree, leafDomMax] using h 0 le_rfl
  | t + 1, h => by
      simp only [catVtree, leafDomMax]
      exact max_le (mixTime_catVtree_leafDomMax_le dom Q t (fun s hs => h s (by omega))) (h _ le_rfl)

/-- INTERNAL: every region of the compiled caterpillar carries exactly `k` gates, one per
mixture component.
TEXLINE: main.tex:717 -/
theorem mixTime_catCircuit_gateWidth (k : ℕ) (dom : ℕ → ℕ) (tab : (t : ℕ) → Fin k → Fin (dom t) → ℝ) :
    ∀ t : ℕ, gateWidth (catCircuit k dom tab t) = k
  | 0 => rfl
  | t + 1 => by
      simp only [catCircuit, gateWidth, mixTime_catCircuit_gateWidth k dom tab t]
      simp

/-- INTERNAL: the compiled caterpillar over coordinates `0..t` has at most
`(t + 1)(2k + k³ + kQ)` gates and wires (`k` gates, a `k × Q` table per leaf, a `k³`
diagonal tensor per node).
TEXLINE: main.tex:717-720 -/
theorem mixTime_catCircuit_size_le (k : ℕ) (dom : ℕ → ℕ) (tab : (t : ℕ) → Fin k → Fin (dom t) → ℝ)
    (Q : ℕ) : ∀ t : ℕ, (∀ s ≤ t, dom s ≤ Q) →
    circuitSize (catCircuit k dom tab t) ≤ (t + 1) * (2 * k + k * k * k + k * Q)
  | 0, h => by
      simp only [catCircuit, circuitSize]
      have := Nat.mul_le_mul_left k (h 0 le_rfl)
      nlinarith
  | t + 1, h => by
      simp only [catCircuit, circuitSize]
      have ih := mixTime_catCircuit_size_le k dom tab Q t (fun s hs => h s (by omega))
      have := Nat.mul_le_mul_left k (h (t + 1) le_rfl)
      nlinarith

/-- INTERNAL: every internal region of the caterpillar has feature dimension `k₁ + k₂`, so
the retained-row budget is at most one call's `prior.size (k₁ + k₂)`.
TEXLINE: main.tex:745-753 -/
theorem mixTime_catPair_retainedBudget_le {δ η' : ℝ} (prior : SparsifyPrior δ η') (M : MixtureInstance) :
    ∀ t : ℕ, retainedBudget prior (catPair M t).P (catPair M t).Q ≤ prior.size (M.k1 + M.k2)
  | 0 => Nat.zero_le _
  | t + 1 => by
      have ih := mixTime_catPair_retainedBudget_le prior M t
      simp only [catPair] at ih ⊢
      change max (prior.size (M.k1 + M.k2)) (max (retainedBudget prior
        (catCircuit M.k1 M.dom M.pTab t) (catCircuit M.k2 M.dom M.qTab t)) 0) ≤ _
      omega

/-- INTERNAL: the caterpillar over coordinates `0..t` has `t` internal regions, so the run
makes `n − 1` sparsification calls.
TEXLINE: main.tex:886-888 -/
theorem mixTime_catPair_steps (M : MixtureInstance) :
    ∀ t : ℕ, (pairRegion (catPair M t).P (catPair M t).Q).steps = t
  | 0 => rfl
  | t + 1 => by
      have ih := mixTime_catPair_steps M t
      simp only [catPair] at ih ⊢
      change (pairRegion (catCircuit M.k1 M.dom M.pTab t) (catCircuit M.k2 M.dom M.qTab t)).steps
        + (pairRegion (Circuit.leaf (M.pTab (t+1))) (Circuit.leaf (M.qTab (t+1)))).steps + 1 = t + 1
      rw [ih]; rfl

/-- INTERNAL: the tally of `Program.runDense` is that of `Program.build` plus the dense
output stage of Algorithm 1 line 13: `rows · d + rows` multiplications, `rows · (d − 1)
+ rows` additions, `rows` absolute values and one division.
TEXLINE: main.tex:782 -/
theorem mixTime_steps_runDense {δ η' : ℝ} {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ)
    (prior : SparsifyPrior δ η') (t : Program.Tape prior) :
    Charged.steps rate (Program.runDense C prior t)
      = Charged.steps rate (Program.build prior C.P C.Q t)
        + (Fintype.card (Program.build prior C.P C.Q t).val.Idx * (gP + gQ)
            + Fintype.card (Program.build prior C.P C.Q t).val.Idx)
        + (Fintype.card (Program.build prior C.P C.Q t).val.Idx * (gP + gQ - 1)
            + Fintype.card (Program.build prior C.P C.Q t).val.Idx)
        + Fintype.card (Program.build prior C.P C.Q t).val.Idx + 1 := by
  simp only [Program.runDense, Charged.steps_bind, abses, muls, adds, divs, steps_opMany_rate]
  refine Eq.trans (congrArg (fun x => _ + (_ + (_ + (_ + x)))) (steps_opMany_rate _ _ _)) ?_
  ring
/-- INTERNAL: each factor of a product of five reals that are all at least one is at most
the product. -/
theorem mixTime_le_of_one_le_prod5 {a b c d f : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hd : 1 ≤ d) (hf : 1 ≤ f) :
    a ≤ a * b * c * d * f ∧ b ≤ a * b * c * d * f ∧ c ≤ a * b * c * d * f ∧
      d ≤ a * b * c * d * f ∧ f ≤ a * b * c * d * f := by
  have key : ∀ x y : ℝ, 1 ≤ x → 1 ≤ y → x ≤ x * y := fun x y hx hy =>
    le_mul_of_one_le_right (by linarith) hy
  have m : ∀ x y : ℝ, 1 ≤ x → 1 ≤ y → 1 ≤ x * y := fun x y hx hy =>
    one_le_mul_of_one_le_of_one_le hx hy
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := key a (b * c * d * f) ha (m _ _ (m _ _ (m _ _ hb hc) hd) hf)
    linarith [show a * (b * c * d * f) = a * b * c * d * f by ring]
  · have := key b (a * c * d * f) hb (m _ _ (m _ _ (m _ _ ha hc) hd) hf)
    linarith [show b * (a * c * d * f) = a * b * c * d * f by ring]
  · have := key c (a * b * d * f) hc (m _ _ (m _ _ (m _ _ ha hb) hd) hf)
    linarith [show c * (a * b * d * f) = a * b * c * d * f by ring]
  · have := key d (a * b * c * f) hd (m _ _ (m _ _ (m _ _ ha hb) hc) hf)
    linarith [show d * (a * b * c * f) = a * b * c * d * f by ring]
  · have := key f (a * b * c * d) hf (m _ _ (m _ _ (m _ _ ha hb) hc) hd)
    linarith [show f * (a * b * c * d) = a * b * c * d * f by ring]

/-- INTERNAL: the prior's size bound `m ≤ C · (k log 2k / δ²) · log(1/η')` at
`δ = ε/(3n)`, `η' = η/n`, made polynomial: `m ≤ 18 C · k² n³ (1/ε)² (1 + log(1/η))`,
using `log(2k) ≤ 2k` and `log(n/η) ≤ n (1 + log(1/η))`.
TEXLINE: main.tex:745-753 -/
theorem mixTime_size_le_poly {ε η : ℝ} (n k s : ℕ) (hε0 : 0 < ε) (hη0 : 0 < η) (hη1 : η < 1)
    (hn : 1 ≤ n) (hk : 1 ≤ k) (prior : SparsifyPrior (perStepTol ε n) (perStepFail η n))
    (hs : prior.sizeConst ≤ s) :
    (prior.size k : ℝ) ≤ 18 * s * ((k : ℝ) * k * n * n * n * (1 / ε) * (1 / ε)
      * (1 + Real.log (1 / η))) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs' : (prior.sizeConst : ℝ) ≤ s := by exact_mod_cast hs
  have hlogk0 : 0 ≤ Real.log (2 * k) := Real.log_nonneg (by linarith)
  have hlogk : Real.log (2 * k) ≤ 2 * k := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 * k by linarith); linarith
  have hlη : 0 < Real.log (1 / η) := Real.log_pos (by rw [lt_div_iff₀ hη0]; linarith)
  have hη' : Real.log (1 / perStepFail η n) = Real.log n + Real.log (1 / η) := by
    rw [perStepFail, one_div_div, div_eq_mul_one_div, Real.log_mul (by positivity) (by positivity)]
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn'
  have hlogn : Real.log n ≤ n := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < n by linarith); linarith
  have hlη' : Real.log (1 / perStepFail η n) ≤ n * (1 + Real.log (1 / η)) := by
    rw [hη']; nlinarith
  have hlη'0 : 0 ≤ Real.log (1 / perStepFail η n) := by rw [hη']; positivity
  have hδ : (k : ℝ) * Real.log (2 * k) / perStepTol ε n ^ 2
      = (k : ℝ) * Real.log (2 * k) * (9 * n ^ 2 * (1 / ε) ^ 2) := by
    rw [perStepTol]; field_simp; ring
  have h1 : (k : ℝ) * Real.log (2 * k) / perStepTol ε n ^ 2
      ≤ (k : ℝ) * (2 * k) * (9 * n ^ 2 * (1 / ε) ^ 2) := by
    rw [hδ]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hlogk (by positivity)
  have h10 : 0 ≤ (k : ℝ) * Real.log (2 * k) / perStepTol ε n ^ 2 := by
    rw [hδ]; positivity
  refine (prior.size_le k).trans ?_
  calc (prior.sizeConst : ℝ) * ((k : ℝ) * Real.log (2 * k) / perStepTol ε n ^ 2)
        * Real.log (1 / perStepFail η n)
      ≤ (s : ℝ) * ((k : ℝ) * (2 * k) * (9 * n ^ 2 * (1 / ε) ^ 2))
        * (n * (1 + Real.log (1 / η))) := by
        apply mul_le_mul _ hlη' hlη'0 (by positivity)
        exact mul_le_mul hs' h1 h10 (by positivity)
    _ = _ := by ring

/-- INTERNAL: the real arithmetic of the time bound.  With `X ≥ 1` bounding `n`, `k` and
the caterpillar's step count, `B ≤ A X⁸` rows, size `≤ 4X⁴`, and the solver's suppressed
factor polynomial, the tally `build + rows (2k + 3) + 1` is at most `c X^(20 + 17 pd)`.
TEXLINE: main.tex:850-857 -/
theorem mixTime_poly_combine (X B L S W r k cc' pl ω A cc pc b : ℝ) (pd : ℕ)
    (hX : 1 ≤ X) (hB0 : 0 ≤ B) (hB : B ≤ A * X ^ 8) (hL0 : 0 ≤ L) (hL : L ≤ X)
    (hS0 : 0 ≤ S) (hS : S ≤ 4 * X ^ 4) (hW0 : 0 ≤ W) (hW : W ≤ X)
    (hr : r ≤ B) (hk0 : 0 ≤ k) (hk : k ≤ X)
    (hcc0 : 0 ≤ cc') (hcc : cc' ≤ cc) (hpl0 : 0 ≤ pl) (hpc : 0 ≤ pc)
    (hpl : pl ≤ pc * (2 * W * B ^ 2 + 2) ^ pd) (hω : 2 ≤ ω ∧ ω ≤ 2.4)
    (hb : b ≤ B ^ 2 * (L + 3 * S) + L * (cc' * pl * (2 * W * B ^ 2 + (2 * W) ^ ω))) :
    b + r * (2 * k + 3) + 1
      ≤ (13 * A ^ 2 + cc * pc * (2 * A ^ 2 + 2) ^ pd * (2 * A ^ 2 + 8) + 5 * A + 1)
        * X ^ (20 + 17 * pd) := by
  have hX0 : 0 ≤ X := by linarith
  have hA : 0 ≤ A := by
    by_contra h; rw [not_le] at h
    have : A * X ^ 8 < 0 := mul_neg_of_neg_of_pos h (by positivity)
    linarith
  have hcc1 : 0 ≤ cc := hcc0.trans hcc
  have hpow : ∀ a b : ℕ, a ≤ b → X ^ a ≤ X ^ b := fun a b h => pow_le_pow_right₀ hX h
  have hB2 : B ^ 2 ≤ A ^ 2 * X ^ 16 := by
    calc B ^ 2 ≤ (A * X ^ 8) ^ 2 := pow_le_pow_left₀ hB0 hB 2
      _ = A ^ 2 * X ^ 16 := by ring
  -- term 1
  have hLS : L + 3 * S ≤ 13 * X ^ 4 := by
    have := hpow 1 4 (by norm_num); simp at this; linarith
  have T1 : B ^ 2 * (L + 3 * S) ≤ 13 * A ^ 2 * X ^ (20 + 17 * pd) := by
    calc B ^ 2 * (L + 3 * S) ≤ (A ^ 2 * X ^ 16) * (13 * X ^ 4) :=
          mul_le_mul hB2 hLS (by positivity) (by positivity)
      _ = 13 * A ^ 2 * X ^ 20 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hpow _ _ (by omega)) (by positivity)
  -- term 2
  have hWB : 2 * W * B ^ 2 ≤ 2 * A ^ 2 * X ^ 17 := by
    calc 2 * W * B ^ 2 ≤ 2 * X * (A ^ 2 * X ^ 16) :=
          mul_le_mul (by linarith) hB2 (by positivity) (by positivity)
      _ = 2 * A ^ 2 * X ^ 17 := by ring
  have hX17 : 1 ≤ X ^ 17 := one_le_pow₀ hX
  have hpl' : pl ≤ pc * (2 * A ^ 2 + 2) ^ pd * X ^ (17 * pd) := by
    refine hpl.trans ?_
    calc pc * (2 * W * B ^ 2 + 2) ^ pd ≤ pc * ((2 * A ^ 2 + 2) * X ^ 17) ^ pd := by
          apply mul_le_mul_of_nonneg_left _ hpc
          apply pow_le_pow_left₀ (by positivity)
          nlinarith
      _ = _ := by rw [mul_pow, ← pow_mul]; ring
  have hωW : (2 * W) ^ ω ≤ 8 * X ^ 17 := by
    have h1 : (2 * W) ^ ω ≤ (2 * X) ^ ω :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
    have h2 : (2 * X) ^ ω ≤ (2 * X) ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num at hω ⊢; linarith)
    have h3 : (2 * X) ^ (3 : ℝ) = 8 * X ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    have h4 := hpow 3 17 (by norm_num)
    rw [h3] at h2
    linarith
  have hinner : 2 * W * B ^ 2 + (2 * W) ^ ω ≤ (2 * A ^ 2 + 8) * X ^ 17 := by linarith
  have hinner0 : 0 ≤ 2 * W * B ^ 2 + (2 * W) ^ ω := by
    have : 0 ≤ (2 * W) ^ ω := Real.rpow_nonneg (by positivity) _
    positivity
  have T2 : L * (cc' * pl * (2 * W * B ^ 2 + (2 * W) ^ ω))
      ≤ cc * pc * (2 * A ^ 2 + 2) ^ pd * (2 * A ^ 2 + 8) * X ^ (20 + 17 * pd) := by
    calc L * (cc' * pl * (2 * W * B ^ 2 + (2 * W) ^ ω))
        ≤ X * (cc * (pc * (2 * A ^ 2 + 2) ^ pd * X ^ (17 * pd)) * ((2 * A ^ 2 + 8) * X ^ 17)) := by
          apply mul_le_mul hL _ (by positivity) hX0
          apply mul_le_mul _ hinner hinner0 (by positivity)
          exact mul_le_mul hcc hpl' hpl0 hcc1
      _ = cc * pc * (2 * A ^ 2 + 2) ^ pd * (2 * A ^ 2 + 8) * X ^ (18 + 17 * pd) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hpow _ _ (by omega)) (by positivity)
  -- term 3
  have T3 : r * (2 * k + 3) + 1 ≤ (5 * A + 1) * X ^ (20 + 17 * pd) := by
    have h1 : r * (2 * k + 3) ≤ (A * X ^ 8) * (5 * X) :=
      mul_le_mul (hr.trans hB) (by linarith) (by positivity) (by positivity)
    have h2 := hpow 9 (20 + 17 * pd) (by omega)
    have h3 : 1 ≤ X ^ (20 + 17 * pd) := one_le_pow₀ hX
    have h4 : A * X ^ 8 * (5 * X) = 5 * A * X ^ 9 := by ring
    nlinarith
  nlinarith

/-- INTERNAL: `IsStochastic` forces `k₁, k₂ ≥ 1` (the weights sum to `1`) and, through the
first coordinate's normalised table, `q ≥ 1`; and `q` bounds every read domain.
TEXLINE: main.tex:713-716 -/
theorem mixTime_stoch_facts (M : MixtureInstance) (hM : M.IsStochastic) (hn : 1 ≤ M.n) :
    1 ≤ M.k1 ∧ 1 ≤ M.k2 ∧ 1 ≤ M.q ∧ ∀ s ≤ M.n - 1, M.dom s ≤ M.q := by
  have hk1 : 1 ≤ M.k1 := by
    rcases Nat.eq_zero_or_pos M.k1 with h | h
    · have := hM.alpha_sum
      have hE : IsEmpty (Fin M.k1) := by rw [h]; infer_instance
      simp at this
    · exact h
  have hk2 : 1 ≤ M.k2 := by
    rcases Nat.eq_zero_or_pos M.k2 with h | h
    · have := hM.beta_sum
      have hE : IsEmpty (Fin M.k2) := by rw [h]; infer_instance
      simp at this
    · exact h
  have hdomq : ∀ s ≤ M.n - 1, M.dom s ≤ M.q := fun s hs =>
    Finset.le_sup (f := M.dom) (Finset.mem_range.2 (by omega))
  refine ⟨hk1, hk2, ?_, hdomq⟩
  have hd0 : 1 ≤ M.dom 0 := by
    rcases Nat.eq_zero_or_pos (M.dom 0) with h | h
    · have := hM.pTab_sum 0 (by omega) ⟨0, hk1⟩
      have hE : IsEmpty (Fin (M.dom 0)) := by rw [h]; infer_instance
      simp at this
    · exact h
  exact hd0.trans (hdomq 0 (Nat.zero_le _))

/-- Proof-side owner for `TvDomainReduction.mixture_fpras_time`; its statement is fixed by the proof charter.
PAPER: main.tex:794 (complexity half of `thm:main_fptas`), accounting at main.tex:850-857. -/
theorem mixture_fpras_time_proof (hprior : Prior) (fam : SparsifyFamily) : ∃ c D : ℕ, ∀ (M : MixtureInstance), M.IsStochastic → ∀ (ε η : ℝ), 0 < ε → ε < 1 → 0 < η → η < 1 → 2 ≤ M.n → ∀ prior : SparsifyPrior (perStepTol ε M.n) (perStepFail η M.n), fam.Member prior → ∀ p ∈ (Run.runLawMix M prior).support, (Charged.steps rate p : ℝ) ≤ (c : ℝ) * ((M.n : ℝ) * (M.k : ℝ) * (M.q : ℝ) * (1 / ε) * (1 + Real.log (1 / η))) ^ D := by
  refine ⟨13 * (1 + 18 * fam.sizeConst) ^ 2
      + fam.costConst * fam.plConst * (2 * (1 + 18 * fam.sizeConst) ^ 2 + 2) ^ fam.plDeg
        * (2 * (1 + 18 * fam.sizeConst) ^ 2 + 8)
      + 5 * (1 + 18 * fam.sizeConst) + 1, 20 + 17 * fam.plDeg, ?_⟩
  intro M hM ε η hε0 hε1 hη0 hη1 hn prior hmem p hp
  rw [Run.runLawMix, PMF.mem_support_map_iff] at hp
  obtain ⟨t, -, rfl⟩ := hp
  obtain ⟨hk1, hk2, hq, hdomq⟩ := mixTime_stoch_facts M hM (by omega)
  -- the five factors of the base, each at least one
  have hn1 : (1 : ℝ) ≤ M.n := by exact_mod_cast (show 1 ≤ M.n by omega)
  have hk1' : (1 : ℝ) ≤ M.k := by
    exact_mod_cast (show 1 ≤ M.k by unfold MixtureInstance.k; omega)
  have hq1 : (1 : ℝ) ≤ M.q := by exact_mod_cast hq
  have he1 : (1 : ℝ) ≤ 1 / ε := by rw [le_div_iff₀ hε0]; linarith
  have hlη : 0 < Real.log (1 / η) := Real.log_pos (by rw [lt_div_iff₀ hη0]; linarith)
  have hLg1 : (1 : ℝ) ≤ 1 + Real.log (1 / η) := by linarith
  obtain ⟨hnX, hkX, hqX, heX, hLgX⟩ := mixTime_le_of_one_le_prod5 hn1 hk1' hq1 he1 hLg1
  generalize hXdef : (M.n : ℝ) * (M.k : ℝ) * (M.q : ℝ) * (1 / ε) * (1 + Real.log (1 / η)) = X
    at hnX hkX hqX heX hLgX
  have hX1 : 1 ≤ X := hn1.trans hnX
  have hX0 : 0 ≤ X := by linarith
  -- the retained-row budget
  have hsize := mixTime_size_le_poly M.n M.k fam.sizeConst hε0 hη0 hη1 (by omega)
    (by unfold MixtureInstance.k; omega) prior hmem.sizeConst_le
  have h8 : (M.k : ℝ) * M.k * M.n * M.n * M.n * (1 / ε) * (1 / ε) * (1 + Real.log (1 / η))
      ≤ X ^ 8 := by
    calc _ ≤ X * X * X * X * X * X * X * X := by
          gcongr
      _ = X ^ 8 := by ring
  have hs0 : (0 : ℝ) ≤ fam.sizeConst := Nat.cast_nonneg _
  have hsizeX : (prior.size M.k : ℝ) ≤ 18 * fam.sizeConst * X ^ 8 :=
    hsize.trans (mul_le_mul_of_nonneg_left h8 (by positivity))
  set B := leafDomMax (mixVtree M) + retainedBudget prior (mixPair M).P (mixPair M).Q with hBdef
  have hBnat : B ≤ M.q + prior.size M.k :=
    Nat.add_le_add (mixTime_catVtree_leafDomMax_le M.dom M.q (M.n - 1) hdomq)
      (mixTime_catPair_retainedBudget_le prior M (M.n - 1))
  have hB : (B : ℝ) ≤ ((1 : ℝ) + 18 * fam.sizeConst) * X ^ 8 := by
    have h1 : (B : ℝ) ≤ M.q + prior.size M.k := by exact_mod_cast hBnat
    have h2 : X ≤ X ^ 8 := by
      simpa using pow_le_pow_right₀ hX1 (show 1 ≤ 8 by norm_num)
    nlinarith
  -- the step count, width and size of the compiled caterpillar
  have hL : ((pairRegion (mixPair M).P (mixPair M).Q).steps : ℝ) ≤ X := by
    have : (pairRegion (mixPair M).P (mixPair M).Q).steps = M.n - 1 := mixTime_catPair_steps M (M.n - 1)
    rw [this]
    have : ((M.n - 1 : ℕ) : ℝ) ≤ M.n := by exact_mod_cast Nat.sub_le _ _
    linarith
  have hWP : gateWidth (mixPair M).P ≤ M.k1 + M.k2 := by
    have := mixTime_catCircuit_gateWidth M.k1 M.dom M.pTab (M.n - 1)
    change gateWidth (catCircuit M.k1 M.dom M.pTab (M.n - 1)) ≤ _; omega
  have hWQ : gateWidth (mixPair M).Q ≤ M.k1 + M.k2 := by
    have := mixTime_catCircuit_gateWidth M.k2 M.dom M.qTab (M.n - 1)
    change gateWidth (catCircuit M.k2 M.dom M.qTab (M.n - 1)) ≤ _; omega
  have hSnat : circuitSize (mixPair M).P + circuitSize (mixPair M).Q
      ≤ M.n * (2 * M.k + M.k * M.k * M.k + M.k * M.q) := by
    have h1 := mixTime_catCircuit_size_le M.k1 M.dom M.pTab M.q (M.n - 1) hdomq
    have h2 := mixTime_catCircuit_size_le M.k2 M.dom M.qTab M.q (M.n - 1) hdomq
    have hn' : M.n - 1 + 1 = M.n := by omega
    rw [hn'] at h1 h2
    change circuitSize (catCircuit M.k1 M.dom M.pTab (M.n - 1))
      + circuitSize (catCircuit M.k2 M.dom M.qTab (M.n - 1)) ≤ _
    unfold MixtureInstance.k
    have h3 : M.k1 * M.k1 * M.k1 + M.k2 * M.k2 * M.k2
        ≤ (M.k1 + M.k2) * (M.k1 + M.k2) * (M.k1 + M.k2) := by
      nlinarith [Nat.zero_le (M.k1 * M.k2 * M.k1), Nat.zero_le (M.k1 * M.k2 * M.k2)]
    have h4 : M.n * (2 * M.k1 + M.k1 * M.k1 * M.k1 + M.k1 * M.q)
        + M.n * (2 * M.k2 + M.k2 * M.k2 * M.k2 + M.k2 * M.q)
        ≤ M.n * (2 * (M.k1 + M.k2) + (M.k1 + M.k2) * (M.k1 + M.k2) * (M.k1 + M.k2)
          + (M.k1 + M.k2) * M.q) := by
      rw [← Nat.mul_add]
      apply Nat.mul_le_mul_left
      nlinarith
    omega
  have hS : ((circuitSize (mixPair M).P : ℝ) + circuitSize (mixPair M).Q) ≤ 4 * X ^ 4 := by
    have h1 : ((circuitSize (mixPair M).P : ℝ) + circuitSize (mixPair M).Q)
        ≤ (M.n : ℝ) * (2 * M.k + M.k * M.k * M.k + M.k * M.q) := by exact_mod_cast hSnat
    have h2 : (M.n : ℝ) * (2 * M.k + M.k * M.k * M.k + M.k * M.q)
        ≤ X * (2 * X + X * X * X + X * X) := by
      gcongr
    have h3 : X * (2 * X + X * X * X + X * X) ≤ 4 * X ^ 4 := by
      have a : X ^ 2 ≤ X ^ 4 := pow_le_pow_right₀ hX1 (by norm_num)
      have b : X ^ 3 ≤ X ^ 4 := pow_le_pow_right₀ hX1 (by norm_num)
      nlinarith
    linarith
  -- the run
  have hbuild := build_steps_le prior B (M.k1 + M.k2) (mixPair M).P (mixPair M).Q t le_rfl hWP hWQ
  have hcard : Fintype.card (Program.build prior (mixPair M).P (mixPair M).Q t).val.Idx ≤ B :=
    build_card_idx_le prior _ _ t
  have hrun := mixTime_steps_runDense (mixPair M) prior t
  generalize Fintype.card (Program.build prior (mixPair M).P (mixPair M).Q t).val.Idx = r
    at hcard hrun
  generalize Charged.steps rate (Program.build prior (mixPair M).P (mixPair M).Q t) = b
    at hbuild hrun
  have hstepsN : Charged.steps rate (Program.runDense (mixPair M) prior t)
      ≤ b + r * (2 * (M.k1 + M.k2) + 3) + 1 := by
    rw [hrun]
    have := Nat.mul_le_mul_left r (Nat.sub_le (M.k1 + M.k2) 1)
    have e : r * (2 * (M.k1 + M.k2) + 3) = 2 * (r * (M.k1 + M.k2)) + 3 * r := by ring
    omega
  have hsteps : (Charged.steps rate (Program.runDense (mixPair M) prior t) : ℝ)
      ≤ b + r * (2 * (M.k : ℝ) + 3) + 1 := by
    have : (Charged.steps rate (Program.runDense (mixPair M) prior t) : ℝ)
        ≤ ((b + r * (2 * (M.k1 + M.k2) + 3) + 1 : ℕ) : ℝ) := by exact_mod_cast hstepsN
    simpa [MixtureInstance.k] using this
  have hpl := hmem.polylog_le (2 * (M.k1 + M.k2) * B ^ 2)
  have hcc : (prior.costConst : ℝ) ≤ fam.costConst := by exact_mod_cast hmem.costConst_le
  have hW : ((M.k1 + M.k2 : ℕ) : ℝ) ≤ X := hkX
  have hr : (r : ℝ) ≤ B := by exact_mod_cast hcard
  have hS0 : (0 : ℝ) ≤ (circuitSize (mixPair M).P : ℝ) + circuitSize (mixPair M).Q :=
    add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hpl' : (prior.polylog (2 * (M.k1 + M.k2) * B ^ 2) : ℝ)
      ≤ (fam.plConst : ℝ) * (2 * ((M.k1 + M.k2 : ℕ) : ℝ) * (B : ℝ) ^ 2 + 2) ^ fam.plDeg := by
    refine hpl.trans (le_of_eq ?_)
    push_cast; ring
  have key := mixTime_poly_combine X B ((pairRegion (mixPair M).P (mixPair M).Q).steps : ℝ)
    ((circuitSize (mixPair M).P : ℝ) + circuitSize (mixPair M).Q)
    ((M.k1 + M.k2 : ℕ) : ℝ) r M.k (prior.costConst : ℝ)
    (prior.polylog (2 * (M.k1 + M.k2) * B ^ 2) : ℝ) prior.mmExp
    ((1 : ℝ) + 18 * fam.sizeConst) fam.costConst fam.plConst b fam.plDeg
    hX1 (Nat.cast_nonneg _) hB (Nat.cast_nonneg _) hL hS0 hS (Nat.cast_nonneg _) hW
    hr (Nat.cast_nonneg _) hkX (Nat.cast_nonneg _) hcc (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hpl' prior.mmExp_le hbuild
  refine hsteps.trans (key.trans (le_of_eq ?_))
  push_cast
  ring

end TvDomainReduction.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `mixture_fpras_time_proof` with `D = 20 + 17 · plDeg`, via `build_steps_le` and the `mixTime_*` caterpillar facts
-/
