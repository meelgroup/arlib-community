import Nfa.Analysis.SpiritLaw
import Mathlib.Data.Set.Finite.List

/-!
# From `N*` to `N^s`: the first bad state (eq. from_N_to_Ns)

`star_bad_le_spirit` is eq. from_N_to_Ns (analysis.tex:115-154) in the `ε/2` form:
the probability that `countNFAcore*` ends with some `p(q^ℓ)` outside
`goodWindow ε |L(q^ℓ)|` is at most the sum, over the listed states `q^i` of
`corePairs A n`, of `Pr_{N^s}[median(Y_q) ∉ (1 ± ε/2)|L(q)|]` (`spiritLooseProb`).

Route (no conditional expectations needed; it is bookkeeping on the fold):
* `p(q^0_I) = 1 = 1/|L(q_I^0)|` is never overwritten (every listed state has `i ≥ 1`),
  `layerSet A 0 = {q_I}`, and each listed `p(q^i)` is written only at its own step, so
  the bad event is the disjoint union over `k` of "the `k`-th listed state is the first
  bad one", an event of the state after `k+1` steps.
* On "all earlier listed states good", `ρ(q) = min_{q' ∈ pred q} p(q') ≥
  1/((1+ε/2)|L(q)|)` (predecessors are earlier or `q_I^0`, and `|L(q')| ≤ |L(q)|`), so
  `p(q) = min(ρ, 1/med)` leaves the window only if `med ∉ (1 ± ε/2)|L(q)|`
  (prop:hat_rho_is_enough at `ε/2`).
* The floor `(1−ε)/|L|` lies strictly below `1/((1+ε/2)|L|)`, so `spiritStep` and
  `estimateAndSample` give every output state whose `p(q)` is in the window the same
  mass; by induction along the list, the laws of `N*` and `N^s` after `k` steps agree on
  every state all of whose first `k` listed estimates are good (analysis.tex:129-140).
* Hence `Pr_{N*}[first bad at k] ≤ E_{t ∼ spiritPrefix k}[Pr[med ∉ …]] = spiritLooseProb k`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nfa.Analysis.StarBadLeSpiritAux
open Nfa.Pseudocode
variable {Q : Type} [Fintype Q] [LinearOrder Q]

/-- The state written by one estimate step: `p(q^i)` and `S^·(q^i)` updated.

INTERNAL: names the record update shared by `estimateAndSample` and `spiritStep`.
TEXLINE: algorithm.tex:64-84 -/
def writeState (st : CoreState Q) (i : ℕ) (q : Q) (p : ℝ) (S' : ℕ → Finset (List Bool)) :
    CoreState Q :=
  { st with
    p := Function.update st.p i (Function.update (st.p i) q p)
    S := Function.update st.S i (Function.update (st.S i) q S') }

/-- A step at `q^i` leaves every other estimate alone.

INTERNAL: frame bookkeeping.
TEXLINE: analysis.tex:126-128 -/
theorem writeState_p_ne (st : CoreState Q) (i : ℕ) (q : Q) (p : ℝ) (S' : ℕ → Finset (List Bool))
    (ℓ : ℕ) (q' : Q) (h : (ℓ, q') ≠ (i, q)) : (writeState st i q p S').p ℓ q' = st.p ℓ q' := by
  unfold writeState
  by_cases hℓ : ℓ = i
  · subst hℓ
    have hq : q' ≠ q := fun hq => h (by rw [hq])
    simp [Function.update_of_ne hq]
  · simp [Function.update_of_ne hℓ]

/-- A step at `q^i` writes `p(q^i)`.

INTERNAL: frame bookkeeping.
TEXLINE: analysis.tex:126-128 -/
theorem writeState_p_self (st : CoreState Q) (i : ℕ) (q : Q) (p : ℝ)
    (S' : ℕ → Finset (List Bool)) : (writeState st i q p S').p i q = p := by
  simp [writeState]

/-- `estimateAndSample` through `writeState`.

INTERNAL: unfolding.
TEXLINE: algorithm.tex:64-84 -/
theorem estimateAndSample_eq (A : PaperNFA Q) (σ : Selector A) (P : Params) (i : ℕ)
    (st : CoreState Q) (q : Q) :
    estimateAndSample A σ P i st q =
      (hatSamples A σ P st i q (rho A st i q)).bind fun hatS =>
        (finalReduce P hatS (rho A st i q)
          (takeMin (rho A st i q) (blockMedian P (rho A st i q) hatS))).map
          (writeState st i q (takeMin (rho A st i q) (blockMedian P (rho A st i q) hatS))) := rfl

/-- `spiritStep` through `writeState`.

INTERNAL: unfolding.
TEXLINE: analysis.tex:88-111 -/
theorem spiritStep_eq (A : PaperNFA Q) (σ : Selector A) (P : Params) (ε : ℝ) (i : ℕ)
    (st : CoreState Q) (q : Q) :
    spiritStep A σ P ε i st q =
      (hatSamples A σ P st i q (rho A st i q)).bind fun hatS =>
        (finalReduce P hatS (rho A st i q)
          (max (takeMin (rho A st i q) (blockMedian P (rho A st i q) hatS))
            (spiritFloor A ε i q))).map
          (writeState st i q (max (takeMin (rho A st i q) (blockMedian P (rho A st i q) hatS))
            (spiritFloor A ε i q))) := rfl

/-- Every outcome of a step at `q^i` agrees with its input off `q^i`.

INTERNAL: frame bookkeeping.
TEXLINE: analysis.tex:126-128 -/
theorem estimateAndSample_frame (A : PaperNFA Q) (σ : Selector A) (P : Params) (i : ℕ)
    (st : CoreState Q) (q : Q) (u : CoreState Q)
    (hu : u ∈ (estimateAndSample A σ P i st q).support) (ℓ : ℕ) (q' : Q) (h : (ℓ, q') ≠ (i, q)) :
    u.p ℓ q' = st.p ℓ q' := by
  rw [estimateAndSample_eq, PMF.mem_support_bind_iff] at hu
  obtain ⟨_, _, hu⟩ := hu
  rw [PMF.mem_support_map_iff] at hu
  obtain ⟨_, _, rfl⟩ := hu
  exact writeState_p_ne _ _ _ _ _ _ _ h

/-- Every outcome of a spirited step at `q^i` agrees with its input off `q^i`.

INTERNAL: frame bookkeeping.
TEXLINE: analysis.tex:126-128 -/
theorem spiritStep_frame (A : PaperNFA Q) (σ : Selector A) (P : Params) (ε : ℝ) (i : ℕ)
    (st : CoreState Q) (q : Q) (u : CoreState Q)
    (hu : u ∈ (spiritStep A σ P ε i st q).support) (ℓ : ℕ) (q' : Q) (h : (ℓ, q') ≠ (i, q)) :
    u.p ℓ q' = st.p ℓ q' := by
  rw [spiritStep_eq, PMF.mem_support_bind_iff] at hu
  obtain ⟨_, _, hu⟩ := hu
  rw [PMF.mem_support_map_iff] at hu
  obtain ⟨_, _, rfl⟩ := hu
  exact writeState_p_ne _ _ _ _ _ _ _ h

/-- `N*` never touches the estimate of an unlisted state.

INTERNAL: frame bookkeeping.
TEXLINE: analysis.tex:126-128 -/
theorem runStar_frame (A : PaperNFA Q) (σ : Selector A) (P : Params) :
    ∀ (ys : List (ℕ × Q)) (st t : CoreState Q), t ∈ (runStar A σ P st ys).support →
      ∀ ℓ q', (ℓ, q') ∉ ys → t.p ℓ q' = st.p ℓ q'
  | [], st, t, ht, ℓ, q', _ => by
      simp only [runStar, PMF.support_pure, Set.mem_singleton_iff] at ht
      rw [ht]
  | x :: ys, st, t, ht, ℓ, q', hy => by
      rw [runStar, PMF.mem_support_bind_iff] at ht
      obtain ⟨u, hu, ht⟩ := ht
      rw [List.mem_cons, not_or] at hy
      rw [runStar_frame A σ P ys u t ht ℓ q' hy.2]
      exact estimateAndSample_frame A σ P x.1 st x.2 u hu ℓ q' hy.1

/-- `N^s` never touches the estimate of an unlisted state.

INTERNAL: frame bookkeeping.
TEXLINE: analysis.tex:126-128 -/
theorem runSpirit_frame (A : PaperNFA Q) (σ : Selector A) (P : Params) (ε : ℝ) :
    ∀ (ys : List (ℕ × Q)) (st t : CoreState Q), t ∈ (runSpirit A σ P ε st ys).support →
      ∀ ℓ q', (ℓ, q') ∉ ys → t.p ℓ q' = st.p ℓ q'
  | [], st, t, ht, ℓ, q', _ => by
      simp only [runSpirit, PMF.support_pure, Set.mem_singleton_iff] at ht
      rw [ht]
  | x :: ys, st, t, ht, ℓ, q', hy => by
      rw [runSpirit, PMF.mem_support_bind_iff] at ht
      obtain ⟨u, hu, ht⟩ := ht
      rw [List.mem_cons, not_or] at hy
      rw [runSpirit_frame A σ P ε ys u t ht ℓ q' hy.2]
      exact spiritStep_frame A σ P ε x.1 st x.2 u hu ℓ q' hy.1

/-- Running `as ++ bs` is running `as`, then `bs`.

INTERNAL: fold bookkeeping.
TEXLINE: analysis.tex:126-128 -/
theorem runStar_append (A : PaperNFA Q) (σ : Selector A) (P : Params) :
    ∀ (as bs : List (ℕ × Q)) (st : CoreState Q),
      runStar A σ P st (as ++ bs) = (runStar A σ P st as).bind fun s => runStar A σ P s bs
  | [], bs, st => by simp [runStar]
  | x :: as, bs, st => by
      simp only [List.cons_append, runStar, PMF.bind_bind]
      congr 1
      funext s
      exact runStar_append A σ P as bs s


/-- `p(q^i)` is good: inside `goodWindow ε |L(q^i)|`.

INTERNAL: the complement of the bad event of Lemma proba_p(q), per state.
TEXLINE: analysis.tex:115-118 -/
def good (A : PaperNFA Q) (ε : ℝ) (x : ℕ × Q) (t : CoreState Q) : Prop :=
  t.p x.1 x.2 ∈ goodWindow ε (langCount A x.1 x.2 : ℝ)

/-- A PMF gives every set mass at most `1`.

INTERNAL: measure bookkeeping.
TEXLINE: analysis.tex:129-140 -/
theorem toOuterMeasure_le_one {α : Type} (p : PMF α) (s : Set α) : p.toOuterMeasure s ≤ 1 :=
  (MeasureTheory.measure_mono (Set.subset_univ s)).trans
    (le_of_eq ((PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _)))

/-- A step that writes `p` cannot produce a state whose `p(q^i)` differs.

INTERNAL: support bookkeeping.
TEXLINE: analysis.tex:129-140 -/
theorem map_writeState_apply_eq_zero (R : PMF (ℕ → Finset (List Bool))) (st s : CoreState Q)
    (i : ℕ) (q : Q) (p : ℝ) (h : s.p i q ≠ p) : (R.map (writeState st i q p)) s = 0 := by
  rw [PMF.apply_eq_zero_iff, PMF.mem_support_map_iff]
  rintro ⟨S', _, rfl⟩
  exact h (writeState_p_self _ _ _ _ _)

/-- The floor `(1−ε)/L` is below the window: `(1−ε)(1+ε/2) < 1`.

INTERNAL: the spirit is inert on good estimates (`ε/2` window).
TEXLINE: analysis.tex:80-82 -/
theorem floor_lt_lower {ε L : ℝ} (hε0 : 0 < ε) (hL : 0 < L) :
    (1 - ε) / L < 1 / ((1 + ε / 2) * L) := by
  rw [div_lt_div_iff₀ hL (by positivity)]
  nlinarith [mul_pos hε0 hL, mul_pos (mul_pos hε0 hε0) hL]

/-- The floor is never a good value.

INTERNAL: the spirit is inert on good estimates (`ε/2` window).
TEXLINE: analysis.tex:80-82 -/
theorem floor_not_mem {ε L : ℝ} (hε0 : 0 < ε) (hL : 0 < L) : (1 - ε) / L ∉ goodWindow ε L :=
  fun h => absurd h.1 (not_le.2 (floor_lt_lower hε0 hL))

/-- On outputs whose `p(q)` is good, `N*` and `N^s` take one step with the same mass.

INTERNAL: the one-step form of the coupling.
TEXLINE: analysis.tex:129-140 -/
theorem step_agree (A : PaperNFA Q) (σ : Selector A) (P : Params) (ε : ℝ) (hε0 : 0 < ε)
    (i : ℕ) (q : Q) (hL : 0 < (langCount A i q : ℝ)) (st s : CoreState Q)
    (hs : s.p i q ∈ goodWindow ε (langCount A i q : ℝ)) :
    estimateAndSample A σ P i st q s = spiritStep A σ P ε i st q s := by
  rw [estimateAndSample_eq, spiritStep_eq, PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun hatS => ?_
  congr 1
  set p := takeMin (rho A st i q) (blockMedian P (rho A st i q) hatS)
  have hfl : spiritFloor A ε i q = (1 - ε) / (langCount A i q : ℝ) := rfl
  by_cases hp : p ∈ goodWindow ε (langCount A i q : ℝ)
  · have : max p (spiritFloor A ε i q) = p :=
      max_eq_left (by rw [hfl]; exact (floor_lt_lower hε0 hL).le.trans hp.1)
    rw [this]
  · rw [map_writeState_apply_eq_zero _ st s i q p (fun h => hp (by rw [← h]; exact hs)),
      map_writeState_apply_eq_zero _ st s i q _ ?_]
    intro h
    rcases le_total p (spiritFloor A ε i q) with h' | h'
    · rw [max_eq_right h', hfl] at h
      exact floor_not_mem hε0 hL (h ▸ hs)
    · rw [max_eq_left h'] at h
      exact hp (h ▸ hs)

/-- **The coupling** (analysis.tex:129-140): on states all of whose listed estimates are
good, the laws of `N*` and `N^s` agree.

INTERNAL: the paper's "`Ω*_q = Ω^s_q` with equal probabilities", as an equality of laws.
TEXLINE: analysis.tex:129-140 -/
theorem runStar_eq_runSpirit (A : PaperNFA Q) (σ : Selector A) (P : Params) (ε : ℝ)
    (hε0 : 0 < ε) :
    ∀ (ys : List (ℕ × Q)), ys.Nodup → (∀ y ∈ ys, 0 < (langCount A y.1 y.2 : ℝ)) →
      ∀ (st t : CoreState Q), (∀ y ∈ ys, good A ε y t) →
        runStar A σ P st ys t = runSpirit A σ P ε st ys t
  | [], _, _, st, t, _ => rfl
  | x :: ys, hnd, hL, st, t, ht => by
      rw [List.nodup_cons] at hnd
      rw [runStar, runSpirit, PMF.bind_apply, PMF.bind_apply]
      refine tsum_congr fun u => ?_
      have ih := runStar_eq_runSpirit A σ P ε hε0 ys hnd.2 (fun y hy => hL y (by simp [hy])) u t
        (fun y hy => ht y (by simp [hy]))
      rw [ih]
      by_cases hu : good A ε x u
      · rw [step_agree A σ P ε hε0 x.1 x.2 (hL x (by simp)) st u hu]
      · have h0 : runSpirit A σ P ε u ys t = 0 := by
          rw [PMF.apply_eq_zero_iff]
          intro hts
          apply hu
          have := runSpirit_frame A σ P ε ys u t hts x.1 x.2 hnd.1
          unfold good
          rw [← this]
          exact ht x (by simp)
        rw [h0, mul_zero, mul_zero]

/-- A good `ρ` and a median inside `(1 ± ε/2)L` put `p(q) = min(ρ, 1/med)` in the window.

INTERNAL: prop:hat_rho_is_enough at the `ε/2` window.
TEXLINE: analysis.tex:381-388 -/
theorem takeMin_mem_goodWindow {ε L ρ med : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hL : 0 < L)
    (hρ : 1 / ((1 + ε / 2) * L) ≤ ρ)
    (hmed : med ∈ Set.Icc ((1 - ε / 2) * L) ((1 + ε / 2) * L)) :
    takeMin ρ med ∈ goodWindow ε L := by
  have hlo : 0 < (1 - ε / 2) * L := mul_pos (by linarith) hL
  have hmed0 : 0 < med := hlo.trans_le hmed.1
  unfold takeMin
  rw [if_neg (not_le.2 hmed0)]
  have h1 : 1 / ((1 + ε / 2) * L) ≤ 1 / med := one_div_le_one_div_of_le hmed0 hmed.2
  have h2 : 1 / med ≤ 1 / ((1 - ε / 2) * L) := one_div_le_one_div_of_le hlo hmed.1
  exact ⟨le_min hρ h1, (min_le_right _ _).trans h2⟩

/-- One step of `N*` from a state with a good `ρ(q)` leaves `p(q)` bad only if the median
of the block means is loose.

INTERNAL: prop:hat_rho_is_enough, as a bound on one step.
TEXLINE: analysis.tex:381-411 -/
theorem step_bad_le (A : PaperNFA Q) (σ : Selector A) (P : Params) (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1) (i : ℕ) (q : Q) (hL : 0 < (langCount A i q : ℝ)) (st : CoreState Q)
    (hρ : 1 / ((1 + ε / 2) * (langCount A i q : ℝ)) ≤ rho A st i q) :
    (estimateAndSample A σ P i st q).toOuterMeasure
        {s | s.p i q ∉ goodWindow ε (langCount A i q : ℝ)}
      ≤ ((hatSamples A σ P st i q (rho A st i q)).map
          fun hatS (b : Fin P.γ) => blockMean P (rho A st i q) hatS b).toOuterMeasure
        {Y : Fin P.γ → ℝ | Arlib.Probability.medianOf Y ∉
          Set.Icc ((1 - ε / 2) * (langCount A i q : ℝ)) ((1 + ε / 2) * (langCount A i q : ℝ))} := by
  rw [estimateAndSample_eq, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_apply]
  refine ENNReal.tsum_le_tsum fun hatS => ?_
  by_cases hmed : Arlib.Probability.medianOf (fun b : Fin P.γ => blockMean P (rho A st i q) hatS b)
      ∈ Set.Icc ((1 - ε / 2) * (langCount A i q : ℝ)) ((1 + ε / 2) * (langCount A i q : ℝ))
  · rw [Set.indicator_of_notMem (by simp only [Set.mem_preimage, Set.mem_ofPred_eq]; exact not_not.2 hmed)]
    have hgood : takeMin (rho A st i q) (blockMedian P (rho A st i q) hatS) ∈
        goodWindow ε (langCount A i q : ℝ) :=
      takeMin_mem_goodWindow hε0 hε1 hL hρ hmed
    have : ((finalReduce P hatS (rho A st i q)
          (takeMin (rho A st i q) (blockMedian P (rho A st i q) hatS))).map
          (writeState st i q (takeMin (rho A st i q) (blockMedian P (rho A st i q) hatS)))).toOuterMeasure
        {s | s.p i q ∉ goodWindow ε (langCount A i q : ℝ)} = 0 := by
      rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
      intro s hs hbad
      rw [PMF.mem_support_map_iff] at hs
      obtain ⟨S', _, rfl⟩ := hs
      exact hbad (by rw [writeState_p_self]; exact hgood)
    rw [this, mul_zero]
  · rw [Set.indicator_of_mem (by simp only [Set.mem_preimage, Set.mem_ofPred_eq]; exact hmed)]
    calc _ ≤ hatSamples A σ P st i q (rho A st i q) hatS * 1 := by
          gcongr; exact toOuterMeasure_le_one _ _
      _ = _ := mul_one _

/-- The listed states are the `q^i` with `1 ≤ i ≤ n`, `q ∈ Q^i`.

INTERNAL: list bookkeeping.
TEXLINE: algorithm.tex:97-100 -/
theorem mem_corePairs (A : PaperNFA Q) (n i : ℕ) (q : Q) :
    (i, q) ∈ corePairs A n ↔ 1 ≤ i ∧ i ≤ n ∧ q ∈ layerSet A i := by
  unfold corePairs layerList
  simp only [List.mem_flatMap, List.mem_range'_1, List.mem_map, Finset.mem_sort, Prod.mk.injEq]
  constructor
  · rintro ⟨j, ⟨hj1, hj2⟩, q', hq', rfl, rfl⟩
    exact ⟨hj1, by omega, hq'⟩
  · rintro ⟨h1, h2, hq⟩
    exact ⟨i, ⟨h1, by omega⟩, q, hq, rfl, rfl⟩

/-- Each unrolled state is listed once.

INTERNAL: list bookkeeping.
TEXLINE: algorithm.tex:97-100 -/
theorem corePairs_nodup (A : PaperNFA Q) (n : ℕ) : (corePairs A n).Nodup := by
  unfold corePairs layerList
  rw [List.nodup_flatMap]
  refine ⟨fun i _ => (Finset.sort_nodup _ _).map fun a b h => (Prod.mk.inj h).2, ?_⟩
  refine List.Pairwise.imp ?_ (List.nodup_range' (s := 1) (n := n))
  intro a b hab
  simp only [Function.onFun, List.disjoint_left, List.mem_map]
  rintro x ⟨q, _, rfl⟩ ⟨q', _, h⟩
  exact hab (Prod.mk.inj h).1.symm

/-- States are listed layer by layer.

INTERNAL: list bookkeeping.
TEXLINE: algorithm.tex:97-100 -/
theorem corePairs_sorted (A : PaperNFA Q) (n : ℕ) :
    (corePairs A n).Pairwise fun a b => a.1 ≤ b.1 := by
  unfold corePairs layerList
  rw [List.pairwise_flatMap]
  refine ⟨fun i _ => ?_, ?_⟩
  · exact List.pairwise_of_forall_mem_list (by
      intro a ha b hb
      simp only [List.mem_map] at ha hb
      obtain ⟨_, _, rfl⟩ := ha
      obtain ⟨_, _, rfl⟩ := hb
      exact le_rfl)
  · refine List.Pairwise.imp ?_ (List.pairwise_lt_range' (s := 1) (n := n))
    intro a b hab x hx y hy
    simp only [List.mem_map] at hx hy
    obtain ⟨_, _, rfl⟩ := hx
    obtain ⟨_, _, rfl⟩ := hy
    exact hab.le

/-- Every listed state of a lower layer comes before the `k`-th one.

INTERNAL: predecessors are visited first.
TEXLINE: analysis.tex:118-120 -/
theorem mem_take_of_lt (A : PaperNFA Q) (n k : ℕ) (x y : ℕ × Q)
    (hx : (corePairs A n)[k]? = some x) (hy : y ∈ corePairs A n) (hlt : y.1 < x.1) :
    y ∈ (corePairs A n).take k := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.1 hx
  have hsort := List.pairwise_iff_getElem.1 (corePairs_sorted A n)
  have hjk : j < k := by
    by_contra h
    rcases (not_lt.1 h).lt_or_eq with h' | rfl
    · exact absurd (hsort k j hk hj h') (not_le.2 hlt)
    · exact lt_irrefl _ hlt
  rw [List.mem_take_iff_getElem]
  exact ⟨j, by omega, rfl⟩

/-- A state of `Q^ℓ` has a nonempty language.

INTERNAL: duplicate of `langCount_pos` (CoreRunFailLe.lean), which imports this file.
TEXLINE: analysis.tex:86 -/
theorem langCount_pos' (A : PaperNFA Q) (ℓ : ℕ) (q : Q)
    (hq : q ∈ layerSet A ℓ) : 0 < langCount A ℓ q := by
  unfold layerSet at hq
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
  obtain ⟨w, hw, hqw⟩ := hq
  unfold langCount
  rw [Set.ncard_pos ((List.finite_length_eq Bool ℓ).subset fun x hx => hx.1)]
  exact ⟨w, hw, hqw⟩

/-- `|L(q_I^0)| = 1`.

INTERNAL: `p(q_I) = 1` is the correct value.
TEXLINE: analysis.tex:120 -/
theorem langCount_zero (A : PaperNFA Q) (q : Q) (hq : q ∈ layerSet A 0) :
    langCount A 0 q = 1 := by
  unfold layerSet at hq
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
  obtain ⟨w, hw, hqw⟩ := hq
  rw [List.length_eq_zero_iff] at hw
  subst hw
  unfold langCount
  have : {w : List Bool | w.length = 0 ∧ q ∈ A.toNFA.eval w} = {[]} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, List.length_eq_zero_iff]
    constructor
    · exact fun h => h.1
    · rintro rfl; exact ⟨rfl, hqw⟩
  rw [this, Set.ncard_singleton]

/-- `|L(q')| ≤ |L(q)|` for a predecessor `q'` of `q`.

INTERNAL: every word reaching `q'` extends to one reaching `q`.
TEXLINE: analysis.tex:84-86 -/
theorem langCount_pred_le (A : PaperNFA Q) (i : ℕ) (hi : 1 ≤ i) (q q' : Q)
    (hq' : q' ∈ pred A i q) : langCount A (i - 1) q' ≤ langCount A i q := by
  unfold pred at hq'
  rw [Finset.mem_filter] at hq'
  obtain ⟨b, hb⟩ := hq'.2
  have hb' : A.delta q' b q = true := by simpa [labels] using hb
  unfold langCount
  refine Set.ncard_le_ncard_of_injOn (fun w => w ++ [b]) ?_ ?_
    ((List.finite_length_eq Bool i).subset fun x hx => hx.1)
  · rintro w ⟨hw, hqw⟩
    refine ⟨by simp [hw]; omega, ?_⟩
    rw [NFA.eval_append_singleton, NFA.mem_stepSet]
    exact ⟨q', hqw, hb'⟩
  · intro w₁ _ w₂ _ h
    exact List.append_cancel_right h

/-- Good predecessors give `ρ(q) ≥ 1/((1+ε/2)|L(q)|)`.

INTERNAL: the lower half of prop:hat_rho_is_enough, without the spirit.
TEXLINE: analysis.tex:381-388 -/
theorem rho_lower (A : PaperNFA Q) (ε : ℝ) (hε0 : 0 < ε) (i : ℕ) (hi : 1 ≤ i) (q : Q)
    (hq : q ∈ layerSet A i) (t : CoreState Q)
    (hgood : ∀ q' ∈ pred A i q,
      1 / ((1 + ε / 2) * (langCount A (i - 1) q' : ℝ)) ≤ t.p (i - 1) q') :
    1 / ((1 + ε / 2) * (langCount A i q : ℝ)) ≤ rho A t i q := by
  have hL : (1 : ℝ) ≤ langCount A i q := by exact_mod_cast langCount_pos' A i q hq
  unfold rho
  split_ifs with h
  · rw [Finset.le_inf'_iff]
    intro q' hq'
    refine le_trans ?_ (hgood q' hq')
    have hq'L : (1 : ℝ) ≤ langCount A (i - 1) q' := by
      have : q' ∈ layerSet A (i - 1) := (Finset.mem_filter.1 hq').1
      exact_mod_cast langCount_pos' A (i - 1) q' this
    apply one_div_le_one_div_of_le (by positivity)
    have := langCount_pred_le A i hi q q' hq'
    gcongr
  · rw [div_le_one (by positivity)]
    nlinarith


/-- An event read off the estimates of `as` is no likelier after the further steps `bs`.

INTERNAL: later steps do not rewrite earlier estimates.
TEXLINE: analysis.tex:126-128 -/
theorem runStar_append_le (A : PaperNFA Q) (σ : Selector A) (P : Params)
    (as bs : List (ℕ × Q)) (st : CoreState Q) (T : Set (CoreState Q))
    (hT : ∀ s t : CoreState Q, (∀ y ∈ as, s.p y.1 y.2 = t.p y.1 y.2) → s ∈ T → t ∈ T)
    (hdisj : ∀ y ∈ as, y ∉ bs) :
    (runStar A σ P st (as ++ bs)).toOuterMeasure T ≤ (runStar A σ P st as).toOuterMeasure T := by
  rw [runStar_append, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply]
  refine ENNReal.tsum_le_tsum fun s => ?_
  by_cases hs : s ∈ T
  · rw [Set.indicator_of_mem hs]
    calc _ ≤ runStar A σ P st as s * 1 := by gcongr; exact toOuterMeasure_le_one _ _
      _ = _ := mul_one _
  · rw [Set.indicator_of_notMem hs]
    have : (runStar A σ P s bs).toOuterMeasure T = 0 := by
      rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
      intro t ht htT
      exact hs (hT t s (fun y hy =>
        runStar_frame A σ P bs s t ht y.1 y.2 (hdisj y hy)) htT)
    rw [this, mul_zero]

end Nfa.Analysis.StarBadLeSpiritAux

namespace Nfa.Analysis

open Nfa.Pseudocode
open StarBadLeSpiritAux

/-- **eq. from_N_to_Ns** (analysis.tex:115-154), `ε/2` form: the bad event of
Lemma proba_p(q) in `N*` is bounded by the sum over the listed states of the
probability, in `N^s`, that the median of the block means is loose.

PAPER: analysis.tex:115-154 (first bad state, coupling of `N*` with `N^s`), with
prop:hat_rho_is_enough (analysis.tex:381-388) at the `ε/2` window. -/
theorem star_bad_le_spirit {Q : Type} [Fintype Q] [LinearOrder Q]
    (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (P : Nfa.Params) (n : ℕ) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    (coreLawStar A σ P n).toOuterMeasure
      {st | ∃ ℓ ≤ n, ∃ q ∈ layerSet A ℓ, st.p ℓ q ∉ goodWindow ε (langCount A ℓ q : ℝ)}
      ≤ ∑ k ∈ Finset.range (corePairs A n).length, spiritLooseProb A σ P ε n k := by
  classical
  set xs := corePairs A n
  have hnd : xs.Nodup := corePairs_nodup A n
  have hLxs : ∀ y ∈ xs, 0 < (langCount A y.1 y.2 : ℝ) := by
    intro y hy
    have := (mem_corePairs A n y.1 y.2).1 hy
    exact_mod_cast langCount_pos' A y.1 y.2 this.2.2
  have hnot0 : ∀ q', ((0 : ℕ), q') ∉ xs := fun q' h => by
    have := (mem_corePairs A n 0 q').1 h; omega
  -- states reached from `initState` keep `p(q^0) = 1`
  have hinit : ∀ ys : List (ℕ × Q), ys ⊆ xs → ∀ t ∈ (runStar A σ P (initState A P) ys).support,
      ∀ q', t.p 0 q' = 1 := fun ys hys t ht q' =>
    runStar_frame A σ P ys _ t ht 0 q' (fun h => hnot0 q' (hys h))
  -- the first bad listed state
  let E : ℕ → Set (CoreState Q) := fun k =>
    {t | (∀ y ∈ xs.take k, good A ε y t) ∧ ∃ x, xs[k]? = some x ∧ ¬ good A ε x t}
  have hcover : {st : CoreState Q | ∃ ℓ ≤ n, ∃ q ∈ layerSet A ℓ,
        st.p ℓ q ∉ goodWindow ε (langCount A ℓ q : ℝ)} ⊆
      (⋃ k ∈ Finset.range xs.length, E k) ∪ {t | ∃ q', t.p 0 q' ≠ 1} := by
    rintro t ⟨ℓ, hℓ, q, hq, hbad⟩
    by_cases h0 : ∃ q', t.p 0 q' ≠ 1
    · exact Or.inr h0
    left
    push Not at h0
    have hℓ0 : ℓ ≠ 0 := by
      rintro rfl
      apply hbad
      rw [h0 q, langCount_zero A q hq]
      constructor <;> rw [Nat.cast_one, mul_one, one_div]
      · exact inv_le_one_of_one_le₀ (by linarith)
      · exact one_le_inv₀ (by linarith) |>.2 (by linarith)
    have hmem : (ℓ, q) ∈ xs := (mem_corePairs A n ℓ q).2 ⟨by omega, hℓ, hq⟩
    have hex : ∃ m : ℕ, ∃ x : ℕ × Q, xs[m]? = some x ∧ ¬ good A ε x t := by
      obtain ⟨m, hm, hmx⟩ := List.getElem_of_mem hmem
      exact ⟨m, (ℓ, q), by rw [List.getElem?_eq_getElem hm, hmx], hbad⟩
    set k := Nat.find hex
    obtain ⟨x, hx, hxbad⟩ := Nat.find_spec hex
    have hk : k < xs.length := by
      by_contra h
      rw [List.getElem?_eq_none (not_lt.1 h)] at hx
      exact absurd hx (by simp)
    simp only [Set.mem_iUnion, Finset.mem_range]
    refine ⟨k, hk, fun y hy => ?_, x, hx, hxbad⟩
    rw [List.mem_take_iff_getElem] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    have hjk : j < k := by omega
    by_contra hy
    exact Nat.find_min hex hjk ⟨_, List.getElem?_eq_getElem (by omega), hy⟩
  have hzero : (coreLawStar A σ P n).toOuterMeasure {t | ∃ q', t.p 0 q' ≠ 1} = 0 := by
    rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
    rintro t ht ⟨q', hq'⟩
    exact hq' (hinit xs (List.Subset.refl _) t ht q')
  have hk : ∀ k ∈ Finset.range xs.length,
      (coreLawStar A σ P n).toOuterMeasure (E k) ≤ spiritLooseProb A σ P ε n k := by
    intro k hk
    rw [Finset.mem_range] at hk
    obtain ⟨⟨i, q⟩, hx⟩ : ∃ x : ℕ × Q, xs[k]? = some x := ⟨xs[k], List.getElem?_eq_getElem hk⟩
    have hxmem : (i, q) ∈ xs := List.mem_of_getElem? hx
    obtain ⟨hi1, hin, hq⟩ := (mem_corePairs A n i q).1 hxmem
    have hLq : 0 < (langCount A i q : ℝ) := hLxs (i, q) hxmem
    have hxnot : (i, q) ∉ xs.take k := by
      intro h
      have hd : (i, q) ∈ xs.drop k := by
        apply List.mem_of_getElem? (i := 0)
        rw [List.getElem?_drop, Nat.add_zero, hx]
      exact List.disjoint_take_drop hnd le_rfl h hd
    -- membership in `E k` is read off the estimates of `take (k+1)`
    have hEk : E k = {t | (∀ y ∈ xs.take k, good A ε y t) ∧ ¬ good A ε (i, q) t} := by
      ext t
      simp only [E, Set.mem_ofPred_eq, hx, Option.some.injEq, exists_eq_left']
    have htake : xs.take (k + 1) = xs.take k ++ [(i, q)] := by
      rw [List.take_add_one, hx, Option.toList_some]
    -- step 1: drop the steps after `k`
    have h1 : (coreLawStar A σ P n).toOuterMeasure (E k) ≤
        (runStar A σ P (initState A P) (xs.take (k + 1))).toOuterMeasure (E k) := by
      have := runStar_append_le A σ P (xs.take (k + 1)) (xs.drop (k + 1)) (initState A P) (E k)
        (by
          intro s t hst hs
          rw [hEk] at hs ⊢
          refine ⟨fun y hy => ?_, ?_⟩
          · unfold good; rw [← hst y (List.take_subset_take_left _ (by omega) hy)]
            exact hs.1 y hy
          · unfold good; rw [← hst (i, q) (by rw [htake]; simp)]
            exact hs.2)
        (fun y hy hy' => List.disjoint_take_drop hnd le_rfl hy hy')
      rwa [List.take_append_drop] at this
    -- step 2: the `k`-th step, against `N^s`
    have h2 : (runStar A σ P (initState A P) (xs.take (k + 1))).toOuterMeasure (E k) ≤
        spiritLooseProb A σ P ε n k := by
      rw [htake, runStar_append, PMF.toOuterMeasure_bind_apply]
      unfold spiritLooseProb
      rw [hx]
      simp only
      unfold spiritMeans spiritPrefix
      rw [PMF.toOuterMeasure_bind_apply]
      refine ENNReal.tsum_le_tsum fun t => ?_
      have hstep : runStar A σ P t [(i, q)] = estimateAndSample A σ P i t q := by
        simp [runStar, PMF.bind_pure]
      rw [hstep]
      by_cases ht : t ∈ (runStar A σ P (initState A P) (xs.take k)).support
      swap
      · rw [(PMF.apply_eq_zero_iff _ _).2 ht, zero_mul]; exact zero_le
      by_cases hG : ∀ y ∈ xs.take k, good A ε y t
      · rw [runStar_eq_runSpirit A σ P ε hε0 (xs.take k) (hnd.sublist (List.take_sublist _ _))
          (fun y hy => hLxs y (List.take_subset _ _ hy)) _ t hG]
        gcongr
        calc (estimateAndSample A σ P i t q).toOuterMeasure (E k)
            ≤ (estimateAndSample A σ P i t q).toOuterMeasure
                {s | s.p i q ∉ goodWindow ε (langCount A i q : ℝ)} := by
              apply MeasureTheory.measure_mono
              rw [hEk]
              exact fun s hs => hs.2
          _ ≤ _ := step_bad_le A σ P ε hε0 hε1 i q hLq t (by
              refine rho_lower A ε hε0 i hi1 q hq t fun q' hq' => ?_
              have hq'L : q' ∈ layerSet A (i - 1) := (Finset.mem_filter.1 hq').1
              by_cases hi0 : i - 1 = 0
              · rw [hi0] at hq'L ⊢
                rw [hinit _ (List.take_subset _ _) t ht q', langCount_zero A q' hq'L,
                  Nat.cast_one, mul_one, one_div]
                exact inv_le_one_of_one_le₀ (by linarith)
              · have hmem' : (i - 1, q') ∈ xs :=
                  (mem_corePairs A n (i - 1) q').2 ⟨by omega, by omega, hq'L⟩
                exact (hG _ (mem_take_of_lt A n k (i, q) _ hx hmem' (by simp; omega))).1)
      · have : (estimateAndSample A σ P i t q).toOuterMeasure (E k) = 0 := by
          rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
          intro s hs hsE
          rw [hEk] at hsE
          apply hG
          intro y hy
          have hne : (y.1, y.2) ≠ (i, q) := fun h => hxnot (by rw [← h]; exact hy)
          unfold good
          rw [← estimateAndSample_frame A σ P i t q s hs y.1 y.2 hne]
          exact hsE.1 y hy
        rw [this, mul_zero]; exact zero_le
    exact h1.trans h2
  calc (coreLawStar A σ P n).toOuterMeasure
        {st | ∃ ℓ ≤ n, ∃ q ∈ layerSet A ℓ, st.p ℓ q ∉ goodWindow ε (langCount A ℓ q : ℝ)}
      ≤ (coreLawStar A σ P n).toOuterMeasure
          ((⋃ k ∈ Finset.range xs.length, E k) ∪ {t | ∃ q', t.p 0 q' ≠ 1}) :=
        MeasureTheory.measure_mono hcover
    _ ≤ (coreLawStar A σ P n).toOuterMeasure (⋃ k ∈ Finset.range xs.length, E k) +
          (coreLawStar A σ P n).toOuterMeasure {t | ∃ q', t.p 0 q' ≠ 1} :=
        MeasureTheory.measure_union_le _ _
    _ ≤ ∑ k ∈ Finset.range xs.length, (coreLawStar A σ P n).toOuterMeasure (E k) := by
        rw [hzero, add_zero]
        exact MeasureTheory.measure_biUnion_finset_le _ _
    _ ≤ _ := Finset.sum_le_sum hk


end Nfa.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · first bad state + coupling `runStar_eq_runSpirit`, as routed above
* r1 · open · stated for `proba_p_star`; route in the module docstring
-/
