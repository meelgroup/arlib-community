import Esa22Copy.Analysis.Alg2
import Esa22Copy.Analysis.BernSubset

/-!
# Algorithm 2's state is dominated, level by level, by Algorithm 3's `Y_k`

The paper bounds the events of Algorithm 2 by events of Algorithm 3 through the
asserted identification `X_j = Y_{k,j}` when `p_j = 2^{-k}`
(esa22-final.tex:678), which it does not prove.  What the bounds consume is the
consequence proved here:

* `loop2_level_eq_le_yLaw` — `Pr[level = k ∧ X ∈ 𝓑] ≤ Pr[Y_{k,m} ∈ 𝓑]`
  (used for `Error_{2,q}`, esa22-final.tex:748-751);
* `loop2_level_gt_le` — `Pr[level > k] ≤ Σ_j Pr[|Y_{k,j}| = thresh]`
  (used for `Bad = ⋃_j Bad_j`, esa22-final.tex:719-735): the level passes `k`
  at step `j` only if it was `k` before the step and the post-pick sample,
  dominated by `Y_{k,j}`, had size `thresh`.

## How it is proved

The domination `g_j(k,·) ≤ law(Y_{k,j})` is not inductive by itself.  Its
strengthening is (`thinR d X` = `d` successive thinning passes of line 6):

  `h_j(k, U) := Σ_s Pr_j[s] · [s.level ≤ k] · thinR (k - s.level) s.X ({U}) ≤ Pr[Y_{k,j} = U]`

(`loop2_phi_le`, with `phi k` the thinned view).  Step on `a` from a state at
level `q ≤ k`: drop `a`, re-add w.p. `2^{-q}` (`pick_eq_bern`: `firstOnes q` on
`L ≥ q` bits is exactly Bernoulli(`2^{-q}`)), and thinning to `k` keeps it
w.p. `2^{-(k-q)}`: overall `a` is re-added w.p. `2^{-k}` independently, which
is `yStep k a` (`thinR_pick`, from `bs_bind_yStep_eq`).  A throw at `q < k` is
absorbed into the thinning (`tail_le`); a throw at `q = k` moves mass out of
`{level ≤ k}`.  So `h_{j+1}(k,·) ≤ h_j(k,·) >>= yStep k a` (`step_bound`).
Taking only the `q = k` term gives `loop2_level_eq_le_yLaw`; the escaping mass
at step `j` is `Pr[level_{j-1} = k ∧ post-pick full] ≤ Pr[|Y_{k,j}| = thresh]`
(`step2_escape_le` with `dom_tsum`), which gives `loop2_level_gt_le` by
induction from the end.  `A.length ≤ L` keeps every reachable level `≤ L`
(`loop2_level_le`).
-/

set_option autoImplicit false

noncomputable section

namespace Esa22Copy.Analysis.Alg2

open Esa22Copy.Interface.Pseudocode

variable {n : ℕ}

/-- `firstOnes q` accepts iff the first `q` bits are ones (for `q ≤ L`).
INTERNAL. -/
theorem firstOnes_iff {L : ℕ} (q : ℕ) (hq : q ≤ L) (bits : Fin L → Bool) :
    firstOnes q bits = true ↔ ∀ i : Fin L, i.val < q → bits i = true := by
  unfold firstOnes
  rw [if_pos hq, List.all_eq_true]
  constructor
  · intro h i hi
    have hmem : bits i ∈ (List.ofFn bits).take q := by
      rw [List.mem_iff_getElem]
      refine ⟨i.val, by simp; omega, ?_⟩
      simp
    simpa using h _ hmem
  · intro h x hx
    rw [List.mem_iff_getElem] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    simp only [List.length_take, List.length_ofFn, lt_min_iff] at hj
    simp only [List.getElem_take, List.getElem_ofFn, id]
    exact h ⟨j, hj.2⟩ hj.1

/-- **Line 4 is a Bernoulli(`2^{-q}`) coin** when the level `q` is at most the block length.
INTERNAL.
TEXLINE: esa22-final.tex:431 -/
theorem uniform_firstOnes (L q : ℕ) (hq : q ≤ L) :
    (PMF.uniformOfFintype (Fin L → Bool)).map (firstOnes q) =
      PMF.bernoulli (keepProb q) (keepProb_le_one q) := by
  have hset : (Finset.univ.filter fun bits : Fin L → Bool => firstOnes q bits = true) =
      Fintype.piFinset (fun i : Fin L => if i.val < q then {true} else Finset.univ) := by
    ext bits
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
      firstOnes_iff q hq]
    constructor
    · intro h i; split_ifs with hi
      · simp [h i hi]
      · exact Finset.mem_univ _
    · intro h i hi; simpa [hi] using h i
  have hcard : (Finset.univ.filter fun bits : Fin L → Bool => firstOnes q bits = true).card
      = 2 ^ (L - q) := by
    rw [hset, Fintype.card_piFinset]
    rw [show (fun i : Fin L => ((if i.val < q then ({true} : Finset Bool) else Finset.univ)).card)
      = fun i => if i.val < q then 1 else 2 by funext i; split_ifs <;> rfl]
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    congr 1
    have h1 := Fin.card_filter_val_lt (n := L) (m := q)
    have h2 := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin L))) (fun i : Fin L => i.val < q)
    rw [Finset.card_univ, Fintype.card_fin] at h2

    omega
  have htrue : (PMF.uniformOfFintype (Fin L → Bool)).map (firstOnes q) true =
      ENNReal.ofReal (half q) := by
    rw [PMF.map_apply, tsum_fintype]
    simp only [PMF.uniformOfFintype_apply, eq_comm (a := true), ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul]
    rw [hcard, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, half, ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
    obtain ⟨e, rfl⟩ : ∃ e, L = q + e := ⟨L - q, by omega⟩
    rw [Nat.add_sub_cancel_left, pow_add]
    push_cast
    rw [ENNReal.mul_inv (by simp) (by simp), mul_comm ((2 : ENNReal) ^ q)⁻¹, ← mul_assoc,
      ENNReal.mul_inv_cancel (by simp) (by simp), one_mul, ENNReal.inv_pow]
  have hsum : ∀ p : PMF Bool, p false = 1 - p true := by
    intro p
    have := p.tsum_coe
    rw [tsum_fintype, Fintype.sum_bool] at this
    rw [← this, ENNReal.add_sub_cancel_left (PMF.apply_ne_top p true)]
  ext b
  cases b
  · rw [hsum, hsum, htrue, PMF.bernoulli_apply, cond_true, ← ENNReal.ofReal_coe_nnreal]
    congr 2
  · rw [htrue, PMF.bernoulli_apply, cond_true, ← ENNReal.ofReal_coe_nnreal]
    congr 1

/-- `pick` as a Bernoulli(`2^{-level}`) choice.
INTERNAL. -/
theorem pick_eq_bern (L : ℕ) (a : Fin n) (u : State n) (hu : u.level ≤ L) :
    pick L a u = (PMF.bernoulli (keepProb u.level) (keepProb_le_one u.level)).map
      (fun c => if c then { u with X := insert a u.X } else u) := by
  rw [pick, ← uniform_firstOnes L u.level hu, PMF.map_comp]
  rfl


/-- `d` successive thinning passes (line 6 applied `d` times to the sample).
INTERNAL: the kernel of the domination invariant. -/
def thinR : ℕ → Finset (Fin n) → PMF (Finset (Fin n))
  | 0, X => PMF.pure X
  | d + 1, X => (throwLaw X).bind (thinR d)

/-- INTERNAL. -/
theorem thinR_empty (d : ℕ) : thinR d (∅ : Finset (Fin n)) = PMF.pure ∅ := by
  induction d with
  | zero => rfl
  | succ d ih => rw [thinR, throwLaw_eq_bs, bs_empty, PMF.pure_bind, ih]

/-- **One arrival commutes with `d` thinning passes.**
INTERNAL: `bs_bind_yStep_eq` iterated through `thinR`. -/
theorem thinR_pick (d : ℕ) : ∀ (q : ℕ) (X : Finset (Fin n)) (a : Fin n),
    (PMF.bernoulli (keepProb q) (keepProb_le_one q)).bind
        (fun c => thinR d (if c then insert a (X.erase a) else X.erase a))
      = (thinR d X).bind (yStep (q + d) a) := by
  induction d with
  | zero =>
    intro q X a
    rw [thinR, PMF.pure_bind, Nat.add_zero, yStep, ← PMF.bind_pure_comp]
    congr 1
  | succ d ih =>
    intro q X a
    simp only [thinR]
    rw [← PMF.bind_bind]
    have h1 : (PMF.bernoulli (keepProb q) (keepProb_le_one q)).bind
        (fun c => throwLaw (if c then insert a (X.erase a) else X.erase a))
        = (throwLaw X).bind (yStep (q + 1) a) := by
      simp only [throwLaw_eq_bs]
      exact bs_bind_yStep_eq q 1 X a
    rw [h1, PMF.bind_bind, PMF.bind_bind]
    congr 1; funext V
    rw [yStep, PMF.bind_map]
    have := ih (q + 1) V a
    rw [show q + 1 + d = q + (d + 1) by omega] at this
    rw [← this]
    rfl

/-- The thinned view of a state: at level `q ≤ k`, its sample thinned `k - q` more times;
`none` above `k`.
INTERNAL: the left side of the domination invariant. -/
def phi (k : ℕ) (t : State n) : PMF (Option (Finset (Fin n))) :=
  if t.level ≤ k then (thinR (k - t.level) t.X).map some else PMF.pure none

/-- One arrival of `Y_k`, lifted to `Option`.
INTERNAL. -/
def psi (k : ℕ) (a : Fin n) : Option (Finset (Fin n)) → PMF (Option (Finset (Fin n)))
  | none => PMF.pure none
  | some V => (yStep k a V).map some

/-- INTERNAL. -/
theorem map_some_apply (p : PMF (Finset (Fin n))) (U : Finset (Fin n)) :
    p.map some (some U) = p U := by
  rw [PMF.map_apply]
  rw [tsum_eq_single U]
  · simp
  · intro b hb; rw [if_neg]; intro h; exact hb (Option.some_injective _ h).symm


/-- INTERNAL: `throw` unfolded under a bind. -/
theorem throw_bind_eq (s : State n) (f : State n → PMF (Option (Finset (Fin n)))) :
    (Esa22Copy.Interface.Pseudocode.throw s).bind f =
      (PMF.uniformOfFintype (Finset (Fin n))).bind
        (fun h => f { s with X := s.X.filter (· ∈ h) }) := by
  unfold Esa22Copy.Interface.Pseudocode.throw
  rw [PMF.bind_map]; rfl

/-- After the full-test at a level `q ≤ k`, the thinned view to level `k` is at most the
thinned view of the post-pick sample (a throw below `k` is absorbed into the thinning).
INTERNAL. -/
theorem tail_le (thr k : ℕ) (s : State n) (hq : s.level ≤ k) (U : Finset (Fin n)) :
    ((if full thr s then (Esa22Copy.Interface.Pseudocode.throw s).map halve else PMF.pure s).bind
        (phi k)) (some U)
      ≤ ((thinR (k - s.level) s.X).map some) (some U) := by
  by_cases hf : full thr s = true
  · rw [if_pos hf, PMF.bind_map, throw_bind_eq]
    rcases Nat.lt_or_ge s.level k with hlt | hge
    · have hk : k - s.level = (k - (s.level + 1)) + 1 := by omega
      have e : (PMF.uniformOfFintype (Finset (Fin n))).bind
          (fun h => (phi k ∘ halve) { s with X := s.X.filter (· ∈ h) })
          = ((throwLaw s.X).bind (thinR (k - (s.level + 1)))).map some := by
        rw [throwLaw, PMF.bind_map, PMF.map_bind]
        congr 1; funext h
        simp only [Function.comp, phi, halve]
        simp [show s.level + 1 ≤ k by omega]
      rw [e, hk, thinR]
    · have e : (PMF.uniformOfFintype (Finset (Fin n))).bind
          (fun h => (phi k ∘ halve) { s with X := s.X.filter (· ∈ h) }) = PMF.pure none := by
        have : (fun h : Finset (Fin n) => (phi k ∘ halve) { s with X := s.X.filter (· ∈ h) })
            = fun _ => PMF.pure none := by
          funext h; simp only [Function.comp, phi, halve]
          simp [show ¬ (s.level + 1 ≤ k) by omega]
        rw [this, PMF.bind_const]
      rw [e, PMF.pure_apply, if_neg (by simp)]
      exact bot_le
  · rw [if_neg hf, PMF.pure_bind, phi, if_pos hq]

/-- Above level `k` the thinned view stays `none`.
INTERNAL. -/
theorem tail_none (thr k : ℕ) (s : State n) (hs : ¬ s.level ≤ k) :
    (if full thr s then (Esa22Copy.Interface.Pseudocode.throw s).map halve else PMF.pure s).bind
        (phi k) = PMF.pure none := by
  by_cases hf : full thr s = true
  · rw [if_pos hf, PMF.bind_map, throw_bind_eq]
    have : (fun h : Finset (Fin n) => (phi k ∘ halve) { s with X := s.X.filter (· ∈ h) })
        = fun _ => PMF.pure none := by
      funext h; simp only [Function.comp, phi, halve]
      simp [show ¬ (s.level + 1 ≤ k) by omega]
    rw [this, PMF.bind_const]
  · rw [if_neg hf, PMF.pure_bind, phi, if_neg hs]

/-- **The one-step domination**: one step of Algorithm 2 followed by the thinned view is at
most the thinned view followed by one arrival of `Y_k`.
INTERNAL: the inductive step of the invariant. -/
theorem step_bound (L thr k : ℕ) (t : State n) (a : Fin n) (ht : t.level ≤ L)
    (U : Finset (Fin n)) :
    ((step2 L thr t a).bind (phi k)) (some U) ≤ ((phi k t).bind (psi k a)) (some U) := by
  rw [step2, PMF.bind_bind, pick_eq_bern L a (drop a t) (by simpa [drop] using ht), PMF.bind_map]
  by_cases hq : t.level ≤ k
  · calc _ ≤ ∑' c, (PMF.bernoulli (keepProb t.level) (keepProb_le_one t.level)) c *
            ((thinR (k - t.level) (if c then insert a (t.X.erase a) else t.X.erase a)).map some)
              (some U) := by
          rw [PMF.bind_apply]
          refine ENNReal.tsum_le_tsum fun c => mul_le_mul' le_rfl ?_
          have := tail_le thr k ((fun c => if c then { drop a t with X := insert a (drop a t).X }
            else drop a t) c) (by cases c <;> simpa [drop] using hq) U
          cases c <;> simpa [drop] using this
      _ = ((thinR (k - t.level) t.X).bind (yStep (t.level + (k - t.level)) a)) U := by
          rw [← thinR_pick, PMF.bind_apply]
          simp only [map_some_apply]
      _ = _ := by
          rw [Nat.add_sub_cancel' hq, phi, if_pos hq, PMF.bind_map, PMF.bind_apply, PMF.bind_apply]
          refine tsum_congr fun V => ?_
          simp only [Function.comp, psi, map_some_apply]
  · rw [PMF.bind_apply]
    have hz : ∀ c : Bool, ((fun s => (if full thr s then
        (Esa22Copy.Interface.Pseudocode.throw s).map halve else PMF.pure s).bind (phi k)) ∘
        (fun c => if c then { drop a t with X := insert a (drop a t).X } else drop a t)) c
          (some U) = 0 := by
      intro c
      simp only [Function.comp]
      rw [tail_none thr k _ (by cases c <;> simpa [drop] using hq)]
      simp
    simp only [hz, mul_zero, tsum_zero]
    exact bot_le

/-- The level rises by at most one per step.
INTERNAL.
TEXLINE: esa22-final.tex:679 -/
theorem step2_level_le (L thr : ℕ) (s : State n) (a : Fin n) (t : State n)
    (ht : t ∈ (step2 L thr s a).support) : t.level ≤ s.level + 1 := by
  rw [step2, PMF.mem_support_bind_iff] at ht
  obtain ⟨u, hu, ht⟩ := ht
  rw [pick, PMF.mem_support_map_iff] at hu
  obtain ⟨bits, _, rfl⟩ := hu
  have hul : (if firstOnes (drop a s).level bits then
      { drop a s with X := insert a (drop a s).X } else drop a s).level = s.level := by
    split_ifs <;> rfl
  generalize (if firstOnes (drop a s).level bits then
      { drop a s with X := insert a (drop a s).X } else drop a s) = u at hul ht
  by_cases hf : full thr u = true
  · rw [if_pos hf, PMF.mem_support_map_iff] at ht
    obtain ⟨v, hv, rfl⟩ := ht
    unfold Esa22Copy.Interface.Pseudocode.throw at hv
    rw [PMF.mem_support_map_iff] at hv
    obtain ⟨h, _, rfl⟩ := hv
    simp [halve, hul]
  · rw [if_neg hf, PMF.support_pure, Set.mem_singleton_iff] at ht
    rw [ht, hul]; omega

/-- After `j` steps the level is at most `j` (so `p ≥ 2^{-m}`).
INTERNAL.
TEXLINE: esa22-final.tex:679 -/
theorem loop2_level_le (L thr : ℕ) (A : List (Fin n)) (t : State n)
    (ht : t ∈ (loop2 L thr A init).support) : t.level ≤ A.length := by
  induction A using List.reverseRecOn generalizing t with
  | nil =>
    rw [loop2, PMF.support_pure, Set.mem_singleton_iff] at ht
    rw [ht]; rfl
  | append_singleton A a ih =>
    rw [loop2_append, PMF.mem_support_bind_iff] at ht
    obtain ⟨u, hu, ht⟩ := ht
    have := step2_level_le L thr u a t ht
    have := ih u hu
    simp; omega

/-- **The domination invariant** `h_j(k,·) ≤ law(Y_{k,j})`.
INTERNAL: replaces the paper's asserted coupling.
TEXLINE: esa22-final.tex:678 -/
theorem loop2_phi_le (L thr k : ℕ) (A : List (Fin n)) (hL : A.length ≤ L) (U : Finset (Fin n)) :
    ((loop2 L thr A init).bind (phi k)) (some U) ≤ yLaw k A U := by
  induction A using List.reverseRecOn generalizing U with
  | nil =>
    rw [loop2, PMF.pure_bind, phi, if_pos (show (init : State n).level ≤ k from Nat.zero_le k)]
    simp only [init, Nat.sub_zero, thinR_empty, map_some_apply, yLaw, yRun]
    exact le_rfl
  | append_singleton A a ih =>
    have hL' : A.length ≤ L := by simp at hL; omega
    rw [loop2_append, PMF.bind_bind, PMF.bind_apply]
    calc _ ≤ ∑' t, (loop2 L thr A init) t * ((phi k t).bind (psi k a)) (some U) := by
          refine ENNReal.tsum_le_tsum fun t => ?_
          by_cases h0 : (loop2 L thr A init) t = 0
          · rw [h0, zero_mul, zero_mul]
          · refine mul_le_mul' le_rfl (step_bound L thr k t a ?_ U)
            have := loop2_level_le L thr A t ((PMF.mem_support_iff _ _).2 h0)
            simp at hL; omega
      _ = (((loop2 L thr A init).bind (phi k)).bind (psi k a)) (some U) := by
          rw [PMF.bind_bind, PMF.bind_apply]
      _ = ∑ V, ((loop2 L thr A init).bind (phi k)) (some V) * yStep k a V U := by
          rw [PMF.bind_apply, tsum_fintype, Fintype.sum_option]
          simp only [psi, PMF.pure_apply, if_neg (Option.some_ne_none U), mul_zero, zero_add,
            map_some_apply]
      _ ≤ ∑ V, yLaw k A V * yStep k a V U :=
          Finset.sum_le_sum fun V _ => mul_le_mul' (ih hL' V) le_rfl
      _ = yLaw k (A ++ [a]) U := by
          rw [show yLaw k (A ++ [a]) = (yLaw k A).bind (yStep k a) from yRun_append k A a ∅,
            PMF.bind_apply, tsum_fintype]

/-- INTERNAL. -/
theorem phi_of_level_eq (k : ℕ) (t : State n) (ht : t.level = k) :
    phi k t = PMF.pure (some t.X) := by
  rw [phi, if_pos ht.le, ht, Nat.sub_self, thinR, PMF.pure_map]

/-- Summing a test function of the sample over the states at level `k` is dominated by the
same sum under `Y_{k}`.
INTERNAL. -/
theorem dom_tsum (L thr k : ℕ) (A : List (Fin n)) (hL : A.length ≤ L)
    (h : Finset (Fin n) → ENNReal) :
    ∑' t, (loop2 L thr A init) t * (if t.level = k then h t.X else 0)
      ≤ ∑' U, yLaw k A U * h U := by
  set P := loop2 L thr A init
  calc _ ≤ ∑' t, ∑' U, P t * ((phi k t) (some U) * h U) := by
        refine ENNReal.tsum_le_tsum fun t => ?_
        rw [ENNReal.tsum_mul_left]
        refine mul_le_mul' le_rfl ?_
        split_ifs with ht
        · refine le_trans ?_ (ENNReal.le_tsum t.X)
          rw [phi_of_level_eq k t ht, PMF.pure_apply, if_pos rfl, one_mul]
        · exact bot_le
    _ = ∑' U, ∑' t, P t * ((phi k t) (some U) * h U) := ENNReal.tsum_comm
    _ = ∑' U, (P.bind (phi k)) (some U) * h U := by
        refine tsum_congr fun U => ?_
        rw [PMF.bind_apply, ← ENNReal.tsum_mul_right]
        refine tsum_congr fun t => ?_
        rw [mul_assoc]
    _ ≤ _ := ENNReal.tsum_le_tsum fun U => mul_le_mul' (loop2_phi_le L thr k A hL U) le_rfl

/-- After the full-test at level `k`, the level passes `k` only if the sample was full.
INTERNAL. -/
theorem tail_escape_le (thr k : ℕ) (u : State n) (hu : u.level = k) :
    (if full thr u then (Esa22Copy.Interface.Pseudocode.throw u).map halve else PMF.pure u
      ).toOuterMeasure {s | k < s.level} ≤ if u.X.card = thr then 1 else 0 := by
  by_cases hf : full thr u = true
  · have hc : u.X.card = thr := by simpa [full] using hf
    rw [if_pos hc]
    exact (MeasureTheory.measure_mono (Set.subset_univ _)).trans
      (le_of_eq ((PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _)))
  · rw [if_neg hf, PMF.toOuterMeasure_pure_apply, if_neg (by simp [hu])]
    exact bot_le

/-- From level `k ≤ L`, one step of Algorithm 2 moves above `k` only when the post-pick
sample is full, which has the probability that one arrival of `Y_k` makes `|Y_k| = thresh`.
INTERNAL: `Pr[Bad_j] ≤ Pr[|Y_{ℓ,j}| = thresh]`, one step.
TEXLINE: esa22-final.tex:728-731 -/
theorem step2_escape_le (L thr k : ℕ) (t : State n) (a : Fin n) (hk : t.level = k) (hL : k ≤ L) :
    (step2 L thr t a).toOuterMeasure {s | k < s.level}
      ≤ (yStep k a t.X).toOuterMeasure {U | U.card = thr} := by
  rw [step2, pick_eq_bern L a (drop a t) (by simpa [drop, hk] using hL), PMF.bind_map,
    PMF.toOuterMeasure_bind_apply, yStep, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_apply]
  subst hk
  refine ENNReal.tsum_le_tsum fun c => ?_
  cases c
  · have h := tail_escape_le thr t.level (drop a t) rfl
    by_cases hc : (drop a t).X.card = thr
    · rw [if_pos hc] at h
      rw [Set.indicator_of_mem (show false ∈ (fun c : Bool =>
        if c = true then insert a (t.X.erase a) else t.X.erase a) ⁻¹' {U | U.card = thr} from hc)]
      exact (mul_le_mul' le_rfl h).trans (le_of_eq (mul_one _))
    · rw [if_neg hc] at h
      rw [Set.indicator_of_notMem (show false ∉ (fun c : Bool =>
        if c = true then insert a (t.X.erase a) else t.X.erase a) ⁻¹' {U | U.card = thr} from hc)]
      exact (mul_le_mul' le_rfl h).trans (le_of_eq (mul_zero _))
  · have h := tail_escape_le thr t.level { drop a t with X := insert a (drop a t).X } rfl
    by_cases hc : (insert a (drop a t).X).card = thr
    · rw [if_pos hc] at h
      rw [Set.indicator_of_mem (show true ∈ (fun c : Bool =>
        if c = true then insert a (t.X.erase a) else t.X.erase a) ⁻¹' {U | U.card = thr} from hc)]
      exact (mul_le_mul' le_rfl h).trans (le_of_eq (mul_one _))
    · rw [if_neg hc] at h
      rw [Set.indicator_of_notMem (show true ∉ (fun c : Bool =>
        if c = true then insert a (t.X.erase a) else t.X.erase a) ⁻¹' {U | U.card = thr} from hc)]
      exact (mul_le_mul' le_rfl h).trans (le_of_eq (mul_zero _))


/-- **Per-level domination.**  Algorithm 2 ends at level `k` with a sample in `𝓑`
no more often than Algorithm 3's `Y_{k,m}` lies in `𝓑`.
PAPER: esa22-final.tex:678, 748-751 -/
theorem loop2_level_eq_le_yLaw (L thr : ℕ) (A : List (Fin n)) (hL : A.length ≤ L) (k : ℕ)
    (𝓑 : Set (Finset (Fin n))) :
    (loop2 L thr A init).toOuterMeasure {t | t.level = k ∧ t.X ∈ 𝓑}
      ≤ (yLaw k A).toOuterMeasure 𝓑 := by
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
  calc _ = ∑' t, (loop2 L thr A init) t * (if t.level = k then 𝓑.indicator 1 t.X else 0) := by
        refine tsum_congr fun t => ?_
        by_cases h1 : t.level = k <;> by_cases h2 : t.X ∈ 𝓑 <;>
          simp [h1, h2]
    _ ≤ ∑' U, yLaw k A U * 𝓑.indicator 1 U := dom_tsum L thr k A hL _
    _ = _ := by
        refine tsum_congr fun U => ?_
        by_cases h : U ∈ 𝓑 <;> simp [h]

/-- **`Pr[Bad] ≤ Σ_j Pr[Bad_j]`, with `Bad_j ⊆ {|Y_{k,j}| = thresh}`.**  Algorithm 2's
final level exceeds `k` with probability at most the sum over prefixes
`A.take (j+1)` of the probability that `Y_k` on that prefix has size `thresh`.
PAPER: esa22-final.tex:719-735 -/
theorem loop2_level_gt_le (L thr : ℕ) (A : List (Fin n)) (hL : A.length ≤ L) (k : ℕ) :
    (loop2 L thr A init).toOuterMeasure {t | k < t.level}
      ≤ ∑ j ∈ Finset.range A.length,
          (yLaw k (A.take (j + 1))).toOuterMeasure {U | U.card = thr} := by
  induction A using List.reverseRecOn with
  | nil =>
    rw [loop2, PMF.toOuterMeasure_pure_apply, if_neg (by simp [init])]
    exact bot_le
  | append_singleton A a ih =>
    have hL' : A.length ≤ L := by simp at hL; omega
    set P := loop2 L thr A init
    set g : Finset (Fin n) → ENNReal := fun V => (yStep k a V).toOuterMeasure {U | U.card = thr}
    have hpt : ∀ t, P t * (step2 L thr t a).toOuterMeasure {s | k < s.level}
        ≤ P t * ({s : State n | k < s.level}.indicator 1 t) + P t * (if t.level = k then g t.X else 0) := by
      intro t
      rw [← mul_add]
      by_cases h0 : P t = 0
      · rw [h0, zero_mul, zero_mul]
      refine mul_le_mul' le_rfl ?_
      have htL : t.level ≤ A.length := loop2_level_le L thr A t ((PMF.mem_support_iff _ _).2 h0)
      rcases lt_trichotomy t.level k with hlt | heq | hgt
      · have : (step2 L thr t a).toOuterMeasure {s | k < s.level} = 0 := by
          rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
          intro s hs hks
          have := step2_level_le L thr t a s hs
          simp only [Set.mem_setOf_eq] at hks; omega
        rw [this]; exact bot_le
      · rw [if_pos heq, Set.indicator_of_notMem (by simp [heq]), zero_add]
        exact step2_escape_le L thr k t a heq (by omega)
      · rw [Set.indicator_of_mem (show t ∈ {s : State n | k < s.level} from hgt), Pi.one_apply]
        exact (MeasureTheory.measure_mono (Set.subset_univ _)).trans
          ((le_of_eq ((PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _))).trans
            le_self_add)
    rw [loop2_append, PMF.toOuterMeasure_bind_apply]
    calc _ ≤ ∑' t, (P t * ({s : State n | k < s.level}.indicator 1 t)
            + P t * (if t.level = k then g t.X else 0)) := ENNReal.tsum_le_tsum hpt
      _ = P.toOuterMeasure {t | k < t.level} + ∑' t, P t * (if t.level = k then g t.X else 0) := by
          rw [ENNReal.tsum_add, PMF.toOuterMeasure_apply]
          congr 1
          refine tsum_congr fun t => ?_
          by_cases h : k < t.level <;> simp [h]
      _ ≤ (∑ j ∈ Finset.range A.length,
              (yLaw k (A.take (j + 1))).toOuterMeasure {U | U.card = thr})
            + ∑' U, yLaw k A U * g U := add_le_add (ih hL') (dom_tsum L thr k A hL' g)
      _ = _ := by
          rw [List.length_append, List.length_singleton, Finset.sum_range_succ]
          congr 1
          · refine Finset.sum_congr rfl fun j hj => ?_
            rw [List.take_append_of_le_length (by simp at hj; omega)]
          · rw [List.take_of_length_le (by simp),
              show yLaw k (A ++ [a]) = (yLaw k A).bind (yStep k a) from yRun_append k A a ∅,
              PMF.toOuterMeasure_bind_apply]

end Esa22Copy.Analysis.Alg2

end
