import Nfa.Analysis.CoreLawStar

/-!
# The real core run against `countNFAcore*`

`coreLaw_le_star` is the coupling step of Lemma main_result_core's proof
(analysis.tex:24-37): for every event `E` on the final state of a core run,

  `Pr_N[E] ≤ Pr_{N*}[Σ_{r,q}|S^r(q)| ≥ θ] + Pr_{N*}[E]`,

where `N = countNFAcore` (`Pseudocode.coreLaw`) and `N* = countNFAcore*`
(`coreLawStar`).  Proof: flatten `N`'s nested loops into one list of states
(`runPairs`, `coreLaw_eq`); step through it alongside `N*`.  Before the interrupt
fires the two make identical draws; when it fires, `N*` has already stored `θ`
samples, and its stored total only grows afterwards (`runStar_dominates`, since every
state is processed once, from empty sample sets).
-/

set_option autoImplicit false

namespace Nfa.Analysis.CoreLawLeStarAux

open Nfa.Pseudocode

variable {Q : Type} [Fintype Q] [LinearOrder Q]

/-- `countNFAcore` with its two nested loops flattened into one list of states.

INTERNAL: the real core loop in the shape `runStar` has, so the two can be compared step by step.
TEXLINE: algorithm.tex:97-102 -/
noncomputable def runPairs (A : PaperNFA Q) (σ : Selector A) (P : Params) (n : ℕ) :
    CoreState Q → List (ℕ × Q) → PMF (CoreState Q)
  | st, [] => PMF.pure st
  | st, x :: xs => if st.stopped then PMF.pure st else
      (estimateAndSample A σ P x.1 st x.2).bind fun st' =>
        runPairs A σ P n (interrupt A n P st') xs

/-- Once line:interrupt has fired, nothing more happens.

INTERNAL: flattening bookkeeping.
TEXLINE: algorithm.tex:101 -/
theorem runPairs_stopped (A : PaperNFA Q) (σ : Selector A) (P : Params) (n : ℕ)
    (st : CoreState Q) (h : st.stopped = true) (xs : List (ℕ × Q)) :
    runPairs A σ P n st xs = PMF.pure st := by
  cases xs with
  | nil => rfl
  | cons x xs => simp [runPairs, h]

/-- One layer of `processLayer` followed by the flattened rest is the flattened run.

INTERNAL: flattening bookkeeping.
TEXLINE: algorithm.tex:97-102 -/
theorem processLayer_bind (A : PaperNFA Q) (σ : Selector A) (P : Params) (n i : ℕ)
    (rest : List (ℕ × Q)) :
    ∀ (qs : List Q) (st : CoreState Q),
      (processLayer A σ P n i st qs).bind (fun s => runPairs A σ P n s rest) =
        runPairs A σ P n st (qs.map (fun q => (i, q)) ++ rest)
  | [], st => by simp [processLayer]
  | q :: qs, st => by
      by_cases h : st.stopped = true
      · simp [processLayer, h, runPairs_stopped A σ P n st h]
      · simp only [processLayer, h, if_false, Bool.false_eq_true, List.map_cons,
          List.cons_append, runPairs, PMF.bind_bind]
        congr 1
        funext st'
        exact processLayer_bind A σ P n i rest qs _

/-- `runLayers` is the flattened run over the listed layers.

INTERNAL: flattening bookkeeping.
TEXLINE: algorithm.tex:97-102 -/
theorem runLayers_eq (A : PaperNFA Q) (σ : Selector A) (P : Params) (n : ℕ) :
    ∀ (is : List ℕ) (st : CoreState Q),
      runLayers A σ P n st is =
        runPairs A σ P n st (is.flatMap fun i => (layerList A i).map fun q => (i, q))
  | [], st => rfl
  | i :: is, st => by
      rw [runLayers, List.flatMap_cons]
      simp_rw [runLayers_eq A σ P n is]
      unfold layerStep
      by_cases h : st.stopped = true
      · simp [h, runPairs_stopped A σ P n st h]
      · simp only [h, Bool.false_eq_true, if_false]
        exact processLayer_bind A σ P n i _ _ st

/-- `coreLaw` is the flattened run over `corePairs`.

INTERNAL: flattening bookkeeping.
TEXLINE: algorithm.tex:94-102 -/
theorem coreLaw_eq (A : PaperNFA Q) (σ : Selector A) (P : Params) (n : ℕ) :
    coreLaw A σ P n = runPairs A σ P n (initState A P) (corePairs A n) :=
  runLayers_eq A σ P n _ _


/-- `estimateAndSample` at `q^i` writes `p(q^i)` and `S^r(q^i)` and nothing else.

INTERNAL: support of one step.
TEXLINE: algorithm.tex:64-84 -/
theorem eAS_support (A : PaperNFA Q) (σ : Selector A) (P : Params) (i : ℕ) (st : CoreState Q)
    (q : Q) (s : CoreState Q) (hs : s ∈ (estimateAndSample A σ P i st q).support) :
    ∃ (pv : ℝ) (S' : ℕ → Finset (List Bool)),
      s = { st with p := Function.update st.p i (Function.update (st.p i) q pv)
                    S := Function.update st.S i (Function.update (st.S i) q S') } := by
  unfold estimateAndSample at hs
  simp only [PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hs
  obtain ⟨hatS, -, S', -, rfl⟩ := hs
  exact ⟨_, S', rfl⟩

/-- Every remaining state still has empty sample sets.

INTERNAL: invariant making the stored-sample count monotone.
TEXLINE: algorithm.tex:94 -/
def Fresh (st : CoreState Q) (xs : List (ℕ × Q)) : Prop :=
  ∀ x ∈ xs, ∀ r, st.S x.1 x.2 r = ∅

/-- `s` holds at least as many samples as `st` in every slot.

INTERNAL: invariant making the stored-sample count monotone.
TEXLINE: algorithm.tex:101 -/
def Dominates (st s : CoreState Q) : Prop :=
  ∀ ℓ q r, (st.S ℓ q r).card ≤ (s.S ℓ q r).card

omit [LinearOrder Q] in
/-- More samples in every slot means a larger stored total.

INTERNAL: monotonicity of `Σ|S^r(q)|`.
TEXLINE: algorithm.tex:101 -/
theorem storedTotal_mono (A : PaperNFA Q) (n : ℕ) (P : Params) {st s : CoreState Q}
    (h : Dominates st s) : storedTotal A n P st ≤ storedTotal A n P s := by
  unfold storedTotal
  exact Finset.sum_le_sum fun ℓ _ => Finset.sum_le_sum fun q _ =>
    Finset.sum_le_sum fun r _ => h ℓ q r

/-- Processing a fresh state only adds samples.

INTERNAL: monotonicity of `Σ|S^r(q)|`.
TEXLINE: algorithm.tex:101 -/
theorem eAS_dominates (A : PaperNFA Q) (σ : Selector A) (P : Params) (i : ℕ) (st : CoreState Q)
    (q : Q) (hfresh : ∀ r, st.S i q r = ∅) (s : CoreState Q)
    (hs : s ∈ (estimateAndSample A σ P i st q).support) : Dominates st s := by
  obtain ⟨pv, S', rfl⟩ := eAS_support A σ P i st q s hs
  intro ℓ q' r
  by_cases h : ℓ = i ∧ q' = q
  · obtain ⟨rfl, rfl⟩ := h
    simp [hfresh r]
  · have : Function.update st.S i (Function.update (st.S i) q S') ℓ q' = st.S ℓ q' := by
      by_cases hℓ : ℓ = i
      · subst hℓ
        have hq : q' ≠ q := fun hq => h ⟨rfl, hq⟩
        simp [Function.update_of_ne hq]
      · simp [Function.update_of_ne hℓ]
    simp only [this, le_refl]

/-- Processing one state leaves the other remaining states fresh.

INTERNAL: invariant preservation.
TEXLINE: algorithm.tex:94 -/
theorem eAS_fresh (A : PaperNFA Q) (σ : Selector A) (P : Params) (x : ℕ × Q) (st : CoreState Q)
    (xs : List (ℕ × Q)) (hx : x ∉ xs) (hfresh : Fresh st xs) (s : CoreState Q)
    (hs : s ∈ (estimateAndSample A σ P x.1 st x.2).support) : Fresh s xs := by
  obtain ⟨pv, S', rfl⟩ := eAS_support A σ P x.1 st x.2 s hs
  intro y hy r
  have hne : y ≠ x := fun h => hx (h ▸ hy)
  have : Function.update st.S x.1 (Function.update (st.S x.1) x.2 S') y.1 y.2 = st.S y.1 y.2 := by
    by_cases h1 : y.1 = x.1
    · have h2 : y.2 ≠ x.2 := fun h2 => hne (Prod.ext h1 h2)
      rw [h1]
      simp [Function.update_of_ne h2]
    · simp [Function.update_of_ne h1]
  simp only [this]
  exact hfresh y hy r

omit [Fintype Q] [LinearOrder Q] in
/-- Domination is transitive.

INTERNAL: monotonicity bookkeeping.
TEXLINE: algorithm.tex:101 -/
theorem dominates_trans {a b c : CoreState Q} (h1 : Dominates a b) (h2 : Dominates b c) :
    Dominates a c := fun ℓ q r => (h1 ℓ q r).trans (h2 ℓ q r)

/-- Along `countNFAcore*` the stored samples only grow.

INTERNAL: monotonicity of `Σ|S^r(q)|` in `N*`, used by the coupling.
TEXLINE: analysis.tex:24-37 -/
theorem runStar_dominates (A : PaperNFA Q) (σ : Selector A) (P : Params) :
    ∀ (xs : List (ℕ × Q)) (st : CoreState Q), xs.Nodup → Fresh st xs →
      ∀ s ∈ (Nfa.Analysis.runStar A σ P st xs).support, Dominates st s
  | [], st, _, _, s, hs => by
      simp only [Nfa.Analysis.runStar, PMF.support_pure, Set.mem_singleton_iff] at hs
      subst hs
      exact fun _ _ _ => le_refl _
  | x :: xs, st, hnd, hfresh, s, hs => by
      rw [List.nodup_cons] at hnd
      simp only [Nfa.Analysis.runStar, PMF.mem_support_bind_iff] at hs
      obtain ⟨st', hst', hs⟩ := hs
      have h1 := eAS_dominates A σ P x.1 st x.2 (hfresh x (List.mem_cons_self ..)) st' hst'
      have hfresh' : Fresh st' xs := eAS_fresh A σ P x st xs hnd.1
        (fun y hy => hfresh y (List.mem_cons_of_mem _ hy)) st' hst'
      exact dominates_trans h1 (runStar_dominates A σ P xs st' hnd.2 hfresh' s hs)


omit [LinearOrder Q] in
/-- A PMF gives every set mass at most `1`.

INTERNAL: PMF bookkeeping.
TEXLINE: analysis.tex:24-37 -/
theorem toOuterMeasure_le_one {α : Type} (p : PMF α) (s : Set α) : p.toOuterMeasure s ≤ 1 :=
  (MeasureTheory.measure_mono (Set.subset_univ s)).trans
    (le_of_eq ((PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _)))

/-- The coupling of analysis.tex:24-37, step by step: the real run lands in `E` no more
often than the uninterrupted run lands in `E` or overflows.

INTERNAL: the inductive form of `coreLaw_le_star`.
TEXLINE: analysis.tex:24-37 -/
theorem runPairs_le (A : PaperNFA Q) (σ : Selector A) (P : Params) (n : ℕ)
    (E : Set (CoreState Q)) :
    ∀ (xs : List (ℕ × Q)) (st : CoreState Q), xs.Nodup → Fresh st xs → st.stopped = false →
      (runPairs A σ P n st xs).toOuterMeasure E ≤
        (Nfa.Analysis.runStar A σ P st xs).toOuterMeasure
          (E ∪ {s | P.θ ≤ storedTotal A n P s})
  | [], st, _, _, _ => MeasureTheory.measure_mono Set.subset_union_left
  | x :: xs, st, hnd, hfresh, hst => by
      rw [List.nodup_cons] at hnd
      simp only [runPairs, hst, Bool.false_eq_true, if_false, Nfa.Analysis.runStar,
        PMF.toOuterMeasure_bind_apply]
      refine ENNReal.tsum_le_tsum fun a => ?_
      by_cases ha : a ∈ (estimateAndSample A σ P x.1 st x.2).support
      · refine mul_le_mul_right ?_ _
        have hfresh' : Fresh a xs := eAS_fresh A σ P x st xs hnd.1
          (fun y hy => hfresh y (List.mem_cons_of_mem _ hy)) a ha
        have hstop : a.stopped = false := by
          obtain ⟨pv, S', rfl⟩ := eAS_support A σ P x.1 st x.2 a ha
          exact hst
        by_cases hθ : P.θ ≤ storedTotal A n P a
        · have hint : (interrupt A n P a).stopped = true := by
            simp [interrupt, hθ]
          rw [runPairs_stopped A σ P n _ hint]
          refine (toOuterMeasure_le_one _ _).trans (le_of_eq ?_)
          symm
          rw [PMF.toOuterMeasure_apply_eq_one_iff]
          intro s hs
          right
          exact hθ.trans (storedTotal_mono A n P
            (runStar_dominates A σ P xs a hnd.2 hfresh' s hs))
        · have hint : interrupt A n P a = a := by
            cases a
            simp only [interrupt, hθ, decide_false] at hstop ⊢
            simp [hstop]
          rw [hint]
          exact runPairs_le A σ P n E xs a hnd.2 hfresh' hstop
      · rw [(PMF.apply_eq_zero_iff _ _).2 ha, zero_mul, zero_mul]


/-- No unrolled state is visited twice.

INTERNAL: invariant for the coupling.
TEXLINE: algorithm.tex:97-99 -/
theorem corePairs_nodup (A : PaperNFA Q) (n : ℕ) : (corePairs A n).Nodup := by
  unfold corePairs
  rw [List.nodup_flatMap]
  refine ⟨fun i _ => (Finset.sort_nodup _ _).map (fun a b h => (Prod.mk.inj h).2), ?_⟩
  refine List.Pairwise.imp (fun {i j} hij => ?_) (List.nodup_range' (s := 1) (n := n))
  rw [Function.onFun, List.disjoint_left]
  intro y hy hy'
  simp only [List.mem_map] at hy hy'
  obtain ⟨a, -, rfl⟩ := hy
  obtain ⟨b, -, hb⟩ := hy'
  exact hij (Prod.mk.inj hb).1.symm

/-- Every state of layers `1..n` starts with empty sample sets.

INTERNAL: invariant for the coupling.
TEXLINE: algorithm.tex:94-96 -/
theorem initState_fresh (A : PaperNFA Q) (P : Params) (n : ℕ) :
    Fresh (initState A P) (corePairs A n) := by
  intro x hx r
  unfold corePairs at hx
  simp only [List.mem_flatMap, List.mem_map, List.mem_range'] at hx
  obtain ⟨i, ⟨k, -, rfl⟩, q, -, rfl⟩ := hx
  simp [initState]

end Nfa.Analysis.CoreLawLeStarAux

namespace Nfa.Analysis

open Nfa.Pseudocode CoreLawLeStarAux

/-- **The real core run against `countNFAcore*`** (analysis.tex:24-37): for any event
`E` on the final state, `Pr_N[E] ≤ Pr_{N*}[Σ_{r,q}|S^r(q)| ≥ θ] + Pr_{N*}[E]`.  Until
line:interrupt fires the two runs make the same draws, and once it fires the
uninterrupted run has already stored `θ` samples, a count that only grows.

PAPER: analysis.tex:24-37 (the first two lines of the display; stated here for every
event on the final state, not only `p(q_F) ∉ (1 ± ε)|L(q_F)|⁻¹`). -/
theorem coreLaw_le_star {Q : Type} [Fintype Q] [LinearOrder Q] (A : PaperNFA Q)
    (σ : Selector A) (P : Params) (n : ℕ) (E : Set (CoreState Q)) :
    (coreLaw A σ P n).toOuterMeasure E ≤
      (coreLawStar A σ P n).toOuterMeasure {st | P.θ ≤ storedTotal A n P st} +
        (coreLawStar A σ P n).toOuterMeasure E := by
  rw [coreLaw_eq]
  refine (runPairs_le A σ P n E (corePairs A n) (initState A P) (corePairs_nodup A n)
    (initState_fresh A P n) rfl).trans ?_
  rw [Set.union_comm]
  exact MeasureTheory.measure_union_le _ _

end Nfa.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `coreLaw_le_star` via flattening and a step-by-step coupling
-/
