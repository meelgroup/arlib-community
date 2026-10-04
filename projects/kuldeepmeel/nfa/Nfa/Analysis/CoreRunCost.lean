import Nfa.Analysis.TimeBudget
import Nfa.Analysis.EstimateAndSampleCost

/-!
# The cost of one core run

`m` times the steps of `Nfa.Program.coreRun` (countNFA.4-13, algorithm.tex:94-105)
is at most `coreBound m n W P`, `m = |Q|`, `W = max 1 (MM m)` the price of one
witness product, for any layer array of at most `n + 1` duplicate-free layers of
at most `m` states each, and for every tape.

The argument is the paper's (analysis.tex:40-55), made amortized.  Before layer `i`
the run is not interrupted, so the running total `t` of stored samples is at most
`θ + α` (`totalCap`); the samples `D` of layer `i-1` were all counted in `t`.  Layer
`i` costs, times `m`, at most `layerFixed + sampleCoef·D + cacheCoef·D'`, where `D'`
is what layer `i` stores, and `t` grows by at least `D'`.  The potential
`sampleCoef·(cap − t + D) + cacheCoef·(cap − t)` therefore pays for every layer
beyond `layerFixed`, including the layer whose last call fires the interrupt (that
layer skips updateCache, and its calls only read the previous layer's samples).
-/

set_option autoImplicit false

namespace Nfa.Analysis

open Arlib.Computation (Charged Roster)
open Nfa.Model.Operations

variable {Q : Type} [Fintype Q] [LinearOrder Q]

omit [Fintype Q] [LinearOrder Q] in
/-- INTERNAL: an index read by `getD` from an array of duplicate-free layers of at most
`m` states is one too (an index past the end reads `[]`).
TEXLINE: background.tex:32 -/
theorem layers_getD_length_le (layers : Array (List Q)) (m : ℕ)
    (hL : ∀ L ∈ layers.toList, L.Nodup ∧ L.length ≤ m) (ℓ : ℕ) :
    (layers.getD ℓ []).Nodup ∧ (layers.getD ℓ []).length ≤ m := by
  unfold Array.getD
  split
  · exact hL _ (Array.getElem_mem_toList _)
  · simp

/-- INTERNAL: **the in-layer loop** (countNFA.9-11): each state of the layer not yet
interrupted costs one `estimateAndSample` call and one interrupt test.  The loop
keeps `prevS` and the cache, keeps the total at most `cap` while it is not
interrupted, and the samples it stores for the layer's states are at most what it
adds to the total.
TEXLINE: algorithm.tex:90-112 -/
theorem layerLoop_cost (MM : ℕ → ℕ) (A : PaperNFA Q) (σ : Selector A) (P : Params)
    (tape : Tape Q) (j : ℕ) (prev cur : List Q) (one zero θs : Scalar)
    (hθ : θs.get = (P.θ : ℚ)) (Sx : Q → Nfa.Program.Samples)
    (c0 : Roster (List Bool)) (t0 cap : ℚ) (hcap : (P.θ : ℚ) ≤ cap)
    (x0 : Nfa.Program.CoreState Q)
    (h0 : x0.prevS = Sx ∧ x0.cache = c0 ∧ (x0.stopped = false → x0.total.get ≤ cap) ∧
      (∑ q ∈ cur.toFinset, (samplesSize (x0.curS q) : ℚ)) + t0 ≤ x0.total.get) :
    let res := Charged.foldl (fun (x : Nfa.Program.CoreState Q) (q : Q) =>
        if x.stopped then pure x else do
          let x ← Nfa.Program.estimateAndSample A σ P tape j prev one zero x q
          let over ← Scalar.le θs x.total
          pure { x with stopped := over }) cur x0
    Charged.steps (rate MM (Fintype.card Q)) res ≤
      cur.length * (4 * prev.length + 14 * (prev.map fun q' => samplesSize (Sx q')).sum +
        easFixed P + 1) ∧
    (res.val.prevS = Sx ∧ res.val.cache = c0 ∧ (res.val.stopped = false → res.val.total.get ≤ cap) ∧
      (∑ q ∈ cur.toFinset, (samplesSize (res.val.curS q) : ℚ)) + t0 ≤ res.val.total.get) := by
  intro res
  have := foldl_inv_le (rate MM (Fintype.card Q)) (fun (x : Nfa.Program.CoreState Q) (q : Q) =>
        if x.stopped then pure x else do
          let x ← Nfa.Program.estimateAndSample A σ P tape j prev one zero x q
          let over ← Scalar.le θs x.total
          pure { x with stopped := over })
      (fun x => x.prevS = Sx ∧ x.cache = c0 ∧ (x.stopped = false → x.total.get ≤ cap) ∧
        (∑ q ∈ cur.toFinset, (samplesSize (x.curS q) : ℚ)) + t0 ≤ x.total.get)
      (fun _ => 0)
      (fun _ => 4 * prev.length + 14 * (prev.map fun q' => samplesSize (Sx q')).sum +
        easFixed P + 1) (fun _ => 0) cur ?_ x0 h0
  · obtain ⟨hI, hk, -⟩ := this
    refine ⟨le_trans hk (le_of_eq ?_), hI⟩
    simp [List.map_const', mul_comm]
  · intro x q hq hx
    obtain ⟨hpS, hc, hstop, hsum⟩ := hx
    by_cases hxs : x.stopped = true
    · rw [if_pos hxs, Charged.val_pure, Charged.steps_pure]
      exact ⟨⟨hpS, hc, hstop, hsum⟩, Nat.zero_le _, le_refl _⟩
    · rw [if_neg hxs]
      obtain ⟨hcost, p, X, tot, hval, htot⟩ :=
        estimateAndSample_cost MM A σ P tape j prev one zero x q
      simp only [Charged.steps_bind, Charged.steps_pure, Charged.val_bind, Charged.val_pure, hval]
      refine ⟨⟨hpS, hc, ?_, ?_⟩, ?_, le_refl _⟩
      · intro hover
        simp only [Nfa.Interface.val_le, decide_eq_false_iff_not, not_le] at hover
        rw [hθ] at hover
        exact hover.le.trans hcap
      · have hfun : ∀ y, (samplesSize (Function.update x.curS q X y) : ℚ) =
            Function.update (fun y => (samplesSize (x.curS y) : ℚ)) q (samplesSize X : ℚ) y := by
          intro y
          by_cases hy : y = q
          · subst hy; simp
          · simp [Function.update_of_ne hy]
        simp only [hfun]
        rw [Finset.sum_update_of_mem (List.mem_toFinset.2 hq), htot]
        have h1 : (∑ q' ∈ cur.toFinset \ {q}, (samplesSize (x.curS q') : ℚ)) ≤
            ∑ q' ∈ cur.toFinset, (samplesSize (x.curS q') : ℚ) :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun _ _ _ => by positivity)
        linarith
      · rw [hpS] at hcost
        simp only [Scalar.le, Charged.steps_op, ne_eq, reduceCtorEq, not_false_eq_true,
          rate_cost_of_ne]
        unfold easFixed
        omega

omit [LinearOrder Q] in
/-- INTERNAL: **updateCache** (countNFA.12) costs at most `|cur| + 2` steps per stored
word of the layer, and the cache it builds has at most one row per stored word.
TEXLINE: algorithm.tex:129-161 -/
theorem cacheUpdate_cost (MM : ℕ → ℕ) (cur : List Q) (xS : Q → Nfa.Program.Samples)
    (c : Roster (List Bool)) :
    Charged.steps (rate MM (Fintype.card Q)) (Charged.foldl (fun (c : Roster (List Bool)) (q : Q) =>
          Charged.foldl (fun (c : Roster (List Bool)) (T : List (List Bool)) =>
              Charged.foldl (fun (c : Roster (List Bool)) (u : List Bool) => do
                  let present ← Roster.mem u c
                  if present then pure c else do
                    let _ ← Charged.foldl (fun (_ : Unit) (_ : Q) => cacheEntry) cur ()
                    Roster.insert u c) T c)
            (xS q).toList c) cur c) ≤
      (cur.length + 2) * (cur.map fun q => samplesSize (xS q)).sum ∧
    (Charged.foldl (fun (c : Roster (List Bool)) (q : Q) =>
          Charged.foldl (fun (c : Roster (List Bool)) (T : List (List Bool)) =>
              Charged.foldl (fun (c : Roster (List Bool)) (u : List Bool) => do
                  let present ← Roster.mem u c
                  if present then pure c else do
                    let _ ← Charged.foldl (fun (_ : Unit) (_ : Q) => cacheEntry) cur ()
                    Roster.insert u c) T c)
            (xS q).toList c) cur c).val.card ≤
      c.card + (cur.map fun q => samplesSize (xS q)).sum := by
  set m := Fintype.card Q
  -- one word
  have hword : ∀ (c : Roster (List Bool)) (u : List Bool),
      Charged.steps (rate MM m) (do
          let present ← Roster.mem u c
          if present then pure c else do
            let _ ← Charged.foldl (fun (_ : Unit) (_ : Q) => cacheEntry) cur ()
            Roster.insert u c : Charged Op Cell (Roster (List Bool))) ≤ cur.length + 2 ∧
      (do
          let present ← Roster.mem u c
          if present then pure c else do
            let _ ← Charged.foldl (fun (_ : Unit) (_ : Q) => cacheEntry) cur ()
            Roster.insert u c : Charged Op Cell (Roster (List Bool))).val.card ≤ c.card + 1 := by
    intro c u
    have hmem : Charged.steps (rate MM m) (Roster.mem u c : Charged Op Cell Bool) = 1 := by
      simp [Charged.steps, Roster.cost_mem]
    have hins : Charged.steps (rate MM m) (Roster.insert u c : Charged Op Cell _) = 1 := by
      simp [Charged.steps, Roster.cost_insert]
    have hent : Charged.steps (rate MM m)
        (Charged.foldl (fun (_ : Unit) (_ : Q) => (cacheEntry : Charged Op Cell Unit)) cur ()) ≤
          cur.length := by
      have := Charged.steps_foldl_le (k := 1) (rate MM m)
        (f := fun (_ : Unit) (_ : Q) => (cacheEntry : Charged Op Cell Unit))
        (by intro b a; simp [cacheEntry]) cur ()
      simpa using this
    simp only [Charged.steps_bind, Charged.val_bind, hmem]
    split
    · simp
    · simp only [Charged.steps_bind, Charged.val_bind, hins]
      refine ⟨by omega, ?_⟩
      rw [← Roster.card_toFinset, ← Roster.card_toFinset, Roster.toFinset_insert]
      exact Finset.card_insert_le _ _
  have hT : ∀ (c : Roster (List Bool)) (T : List (List Bool)),
      Charged.steps (rate MM m) (Charged.foldl (fun (c : Roster (List Bool)) (u : List Bool) => do
                  let present ← Roster.mem u c
                  if present then pure c else do
                    let _ ← Charged.foldl (fun (_ : Unit) (_ : Q) => cacheEntry) cur ()
                    Roster.insert u c) T c) ≤ (cur.length + 2) * T.length ∧
      (Charged.foldl (fun (c : Roster (List Bool)) (u : List Bool) => do
                  let present ← Roster.mem u c
                  if present then pure c else do
                    let _ ← Charged.foldl (fun (_ : Unit) (_ : Q) => cacheEntry) cur ()
                    Roster.insert u c) T c).val.card ≤ c.card + T.length := by
    intro c T
    have := foldl_inv_le (rate MM m) _ (fun _ => True) Roster.card (fun _ => cur.length + 2)
      (fun _ => 1) T (fun c u _ _ => ⟨trivial, (hword c u).1, (hword c u).2⟩) c trivial
    simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_one] at this
    exact ⟨this.2.1.trans (by rw [mul_comm]), this.2.2⟩
  have hX : ∀ (c : Roster (List Bool)) (L : List (List (List Bool))),
      Charged.steps (rate MM m) (Charged.foldl (fun (c : Roster (List Bool)) (T : List (List Bool)) =>
              Charged.foldl (fun (c : Roster (List Bool)) (u : List Bool) => do
                  let present ← Roster.mem u c
                  if present then pure c else do
                    let _ ← Charged.foldl (fun (_ : Unit) (_ : Q) => cacheEntry) cur ()
                    Roster.insert u c) T c) L c) ≤ (cur.length + 2) * (L.map List.length).sum ∧
      (Charged.foldl (fun (c : Roster (List Bool)) (T : List (List Bool)) =>
              Charged.foldl (fun (c : Roster (List Bool)) (u : List Bool) => do
                  let present ← Roster.mem u c
                  if present then pure c else do
                    let _ ← Charged.foldl (fun (_ : Unit) (_ : Q) => cacheEntry) cur ()
                    Roster.insert u c) T c) L c).val.card ≤ c.card + (L.map List.length).sum := by
    intro c L
    have := foldl_inv_le (rate MM m) _ (fun _ => True) Roster.card
      (fun T => (cur.length + 2) * T.length) List.length L
      (fun c T _ _ => ⟨trivial, (hT c T).1, (hT c T).2⟩) c trivial
    rw [List.sum_map_mul_left] at this
    exact ⟨this.2.1, this.2.2⟩
  have := foldl_inv_le (rate MM m) _ (fun _ => True) Roster.card
      (fun q => (cur.length + 2) * samplesSize (xS q)) (fun q => samplesSize (xS q)) cur
      (fun c q _ _ => ⟨trivial, (hX c (xS q).toList).1, (hX c (xS q).toList).2⟩) c trivial
  rw [List.sum_map_mul_left] at this
  exact ⟨this.2.1, this.2.2⟩

/-- INTERNAL: the number of samples stored, in `curS`, for the states of layer `ℓ`.
TEXLINE: analysis.tex:40-55 -/
def layerSamples (layers : Array (List Q)) (x : Nfa.Program.CoreState Q) (ℓ : ℕ) : ℕ :=
  ((layers.getD ℓ []).map fun q => samplesSize (x.curS q)).sum

/-- INTERNAL: **one layer** (countNFA.7-12) costs, times `m`, at most
`layerFixed + sampleCoef·D + cacheCoef·D'`, `D` the samples of the previous layer
and `D'` those of this one (the last term only if the layer was not interrupted);
if it was not interrupted, its total is at most `cap`, grew by at least `D'`, and
its cache has at most `D'` rows.
TEXLINE: analysis.tex:40-55 -/
theorem layerStep_cost (MM : ℕ → ℕ) (A : PaperNFA Q) (σ : Selector A) (P : Params)
    (tape : Tape Q) (j : ℕ) (layers : Array (List Q)) (one zero θs : Scalar)
    (hθ : θs.get = (P.θ : ℚ))
    (hL : ∀ ℓ, (layers.getD ℓ []).Nodup ∧ (layers.getD ℓ []).length ≤ Fintype.card Q)
    (s : Nfa.Program.CoreState Q) (k : ℕ) (hs : s.stopped = false)
    (hcap : s.total.get ≤ (totalCap P : ℚ))
    (hcache : s.cache.card ≤ layerSamples layers s (k - 1) + 1) :
    Fintype.card Q * Charged.steps (rate MM (Fintype.card Q))
        (Nfa.Program.layerStep A σ P tape j layers one zero θs s k) ≤
      layerFixed (Fintype.card Q) (max 1 (MM (Fintype.card Q))) P +
        sampleCoef (Fintype.card Q) (max 1 (MM (Fintype.card Q))) * layerSamples layers s (k - 1) +
        (if (Nfa.Program.layerStep A σ P tape j layers one zero θs s k).val.stopped then 0
          else cacheCoef (Fintype.card Q) *
            layerSamples layers (Nfa.Program.layerStep A σ P tape j layers one zero θs s k).val k) ∧
    ((Nfa.Program.layerStep A σ P tape j layers one zero θs s k).val.stopped = false →
      (Nfa.Program.layerStep A σ P tape j layers one zero θs s k).val.total.get ≤
          (totalCap P : ℚ) ∧
      (layerSamples layers (Nfa.Program.layerStep A σ P tape j layers one zero θs s k).val k : ℚ) +
          s.total.get ≤ (Nfa.Program.layerStep A σ P tape j layers one zero θs s k).val.total.get ∧
      (Nfa.Program.layerStep A σ P tape j layers one zero θs s k).val.cache.card ≤
          layerSamples layers (Nfa.Program.layerStep A σ P tape j layers one zero θs s k).val k) := by
  unfold Nfa.Program.layerStep
  rw [hs]
  simp only [Bool.false_eq_true, if_false, Charged.steps_bind, Charged.val_bind]
  set m := Fintype.card Q
  set W := max 1 (MM m)
  set prev := layers.getD (k - 1) []
  set cur := layers.getD k []
  have hloop := layerLoop_cost MM A σ P tape j prev cur one zero θs hθ s.curS s.cache s.total.get
    (totalCap P) (by simp [totalCap])
    { prevP := s.curP, prevS := s.curS, curP := fun _ => one, curS := fun _ => #[],
      layerIdx := k, total := s.total, cache := s.cache, stopped := false }
    ⟨rfl, rfl, fun _ => hcap, by simp⟩
  simp only at hloop
  generalize hR : Charged.foldl (fun (x : Nfa.Program.CoreState Q) (q : Q) =>
        if x.stopped then pure x else do
          let x ← Nfa.Program.estimateAndSample A σ P tape j prev one zero x q
          let over ← Scalar.le θs x.total
          pure { x with stopped := over }) cur
    { prevP := s.curP, prevS := s.curS, curP := fun _ => one, curS := fun _ => #[],
      layerIdx := k, total := s.total, cache := s.cache, stopped := false } = R at hloop ⊢
  obtain ⟨hsteps, hpS, hc, hstop, hsum⟩ := hloop
  have hcur : cur.length ≤ m := (hL k).2
  have hprev : prev.length ≤ m := (hL (k - 1)).2
  have h1 : Charged.steps (rate MM m) (Roster.size s.cache : Charged Op Cell ℕ) = 1 := by
    simp [Charged.steps, Roster.cost_size]
  have h2 : ∀ a b, Charged.steps (rate MM m) (ceilDiv a b) = 1 := by
    intro a b; simp [ceilDiv]
  have h3 : ∀ B : ℕ, Charged.steps (rate MM m) (Charged.foldl (fun (_ : Unit) (_ : Bool) =>
        Charged.foldl (fun (_ : Unit) (_ : ℕ) => witnessProduct) (List.range B) ()) [false, true] ())
        ≤ 2 * (B * W) := by
    intro B
    have := Charged.steps_foldl_le (k := B * W) (rate MM m)
      (f := fun (_ : Unit) (_ : Bool) =>
        Charged.foldl (fun (_ : Unit) (_ : ℕ) => (witnessProduct : Charged Op Cell Unit))
          (List.range B) ())
      (by
        intro b a
        have := Charged.steps_foldl_le (k := W) (rate MM m)
          (f := fun (_ : Unit) (_ : ℕ) => (witnessProduct : Charged Op Cell Unit))
          (by intro b a; simp [witnessProduct, W]) (List.range B) ()
        simpa using this) [false, true] ()
    simpa using this
  have hblocks : m * (ceilDiv (Roster.size s.cache : Charged Op Cell ℕ).val m).val ≤
      layerSamples layers s (k - 1) + m := by
    rw [Nfa.Interface.val_ceilDiv, Roster.val_size]
    have := Nat.mul_div_le (s.cache.card + m - 1) m
    omega
  have hD : (prev.map fun q' => samplesSize (s.curS q')).sum = layerSamples layers s (k - 1) := rfl
  rw [hD] at hsteps
  rw [h1, h2]
  have e1 : m * (2 * ((ceilDiv (Roster.size s.cache : Charged Op Cell ℕ).val m).val * W)) ≤
      2 * W * layerSamples layers s (k - 1) + 2 * W * m := by
    have := Nat.mul_le_mul_left (2 * W) hblocks
    calc _ = 2 * W * (m * (ceilDiv (Roster.size s.cache : Charged Op Cell ℕ).val m).val) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have e2 : m * Charged.steps (rate MM m) R ≤
      m ^ 2 * (4 * m + easFixed P + 1) + 14 * m ^ 2 * layerSamples layers s (k - 1) := by
    calc m * Charged.steps (rate MM m) R
        ≤ m * (cur.length * (4 * prev.length + 14 * layerSamples layers s (k - 1) +
            easFixed P + 1)) := Nat.mul_le_mul_left _ hsteps
      _ ≤ m * (m * (4 * m + 14 * layerSamples layers s (k - 1) + easFixed P + 1)) := by
          gcongr
      _ = _ := by ring
  have e3 := h3 (ceilDiv (Roster.size s.cache : Charged Op Cell ℕ).val m).val
  by_cases hst : R.val.stopped = true
  · simp only [hst, if_true, Charged.val_pure, Charged.steps_pure, add_zero]
    refine ⟨?_, fun h => absurd h (by simp)⟩
    unfold layerFixed sampleCoef
    have e3' := Nat.mul_le_mul_left m e3
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, mul_one]
    linarith
  · simp only [hst, Bool.false_eq_true, if_false, Charged.steps_bind, Charged.val_bind,
      Charged.val_pure, Charged.steps_pure, add_zero]
    obtain ⟨hcs, hcc⟩ := cacheUpdate_cost MM cur R.val.curS Roster.empty
    have hD' : ∀ c : Roster (List Bool), layerSamples layers
        { prevP := R.val.prevP, prevS := R.val.prevS, curP := R.val.curP, curS := R.val.curS,
          layerIdx := R.val.layerIdx, total := R.val.total, cache := c,
          stopped := false } k =
        (cur.map fun q => samplesSize (R.val.curS q)).sum := fun _ => rfl
    have hnd : (cur.map fun q => (samplesSize (R.val.curS q) : ℚ)).sum =
        ∑ q ∈ cur.toFinset, (samplesSize (R.val.curS q) : ℚ) :=
      (List.sum_toFinset _ (hL k).1).symm
    simp only [hD']
    refine ⟨?_, ?_⟩
    · have e4 : m * Charged.steps (rate MM m) (Charged.foldl (fun (c : Roster (List Bool)) (q : Q) =>
          Charged.foldl (fun (c : Roster (List Bool)) (T : List (List Bool)) =>
              Charged.foldl (fun (c : Roster (List Bool)) (u : List Bool) => do
                  let present ← Roster.mem u c
                  if present then pure c else do
                    let _ ← Charged.foldl (fun (_ : Unit) (_ : Q) => cacheEntry) cur ()
                    Roster.insert u c) T c)
            (R.val.curS q).toList c) cur Roster.empty) ≤
          m * (m + 2) * (cur.map fun q => samplesSize (R.val.curS q)).sum := by
        calc _ ≤ m * ((cur.length + 2) * (cur.map fun q => samplesSize (R.val.curS q)).sum) :=
              Nat.mul_le_mul_left _ hcs
          _ ≤ m * ((m + 2) * (cur.map fun q => samplesSize (R.val.curS q)).sum) := by gcongr
          _ = _ := by ring
      unfold layerFixed sampleCoef cacheCoef
      have e3' := Nat.mul_le_mul_left m e3
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add, mul_one]
      linarith
    · intro _
      refine ⟨hstop (by simpa using hst), ?_, ?_⟩
      · push_cast
        have hmm : ((cur.map fun q => samplesSize (R.val.curS q)).map (Nat.cast : ℕ → ℚ)).sum =
            (cur.map fun q => (samplesSize (R.val.curS q) : ℚ)).sum := by
          rw [List.map_map]; rfl
        rw [hmm, hnd]
        exact hsum
      · simpa [Roster.card_empty] using hcc

/-- INTERNAL: once interrupted, the remaining layers take no steps.
TEXLINE: algorithm.tex:90-112 -/
theorem layers_fold_stopped (A : PaperNFA Q) (σ : Selector A) (P : Params)
    (tape : Tape Q) (j : ℕ) (layers : Array (List Q)) (one zero θs : Scalar) (MM : ℕ → ℕ)
    (l : List ℕ) (s : Nfa.Program.CoreState Q) (hs : s.stopped = true) :
    Charged.steps (rate MM (Fintype.card Q))
      (Charged.foldl (Nfa.Program.layerStep A σ P tape j layers one zero θs) l s) = 0 := by
  induction l with
  | nil => simp
  | cons k l ih =>
      have h : Nfa.Program.layerStep A σ P tape j layers one zero θs s k = pure s := by
        unfold Nfa.Program.layerStep; rw [if_pos hs]
      rw [steps_foldl_cons, h, Charged.steps_pure, Charged.val_pure, ih]

/-- INTERNAL: **the amortized layer loop**: from a non-interrupted state with total at
most `cap` and a cache of at most `D + 1` rows, `len` layers cost, times `m`, at most
`len·layerFixed + sampleCoef·(cap − t + D) + cacheCoef·(cap − t)`.
TEXLINE: analysis.tex:40-55 -/
theorem layers_fold_cost (MM : ℕ → ℕ) (A : PaperNFA Q) (σ : Selector A) (P : Params)
    (tape : Tape Q) (j : ℕ) (layers : Array (List Q)) (one zero θs : Scalar)
    (hθ : θs.get = (P.θ : ℚ))
    (hL : ∀ ℓ, (layers.getD ℓ []).Nodup ∧ (layers.getD ℓ []).length ≤ Fintype.card Q) :
    ∀ (len k : ℕ) (s : Nfa.Program.CoreState Q), s.stopped = false →
      s.total.get ≤ (totalCap P : ℚ) →
      s.cache.card ≤ layerSamples layers s (k - 1) + 1 →
      ((Fintype.card Q * Charged.steps (rate MM (Fintype.card Q))
          (Charged.foldl (Nfa.Program.layerStep A σ P tape j layers one zero θs)
            (List.range' k len) s) : ℕ) : ℚ) ≤
        len * (layerFixed (Fintype.card Q) (max 1 (MM (Fintype.card Q))) P : ℚ) +
        (sampleCoef (Fintype.card Q) (max 1 (MM (Fintype.card Q))) : ℚ) *
          ((totalCap P : ℚ) - s.total.get + layerSamples layers s (k - 1)) +
        (cacheCoef (Fintype.card Q) : ℚ) * ((totalCap P : ℚ) - s.total.get) := by
  set m := Fintype.card Q
  set W := max 1 (MM m)
  intro len
  induction len with
  | zero =>
      intro k s _ hcap _
      simp only [List.range'_zero, steps_foldl_nil, mul_zero, Nat.cast_zero, Nat.cast_zero,
        zero_mul, zero_add]
      have h1 : (0 : ℚ) ≤ (totalCap P : ℚ) - s.total.get := by linarith
      positivity
  | succ len ih =>
      intro k s hs hcap hcache
      rw [List.range'_succ, steps_foldl_cons]
      obtain ⟨ha, hb⟩ := layerStep_cost MM A σ P tape j layers one zero θs hθ hL s k hs hcap
        hcache
      generalize hS : Nfa.Program.layerStep A σ P tape j layers one zero θs s k = S at ha hb ⊢
      have hcapt : (0 : ℚ) ≤ (totalCap P : ℚ) - s.total.get := by linarith
      by_cases hst : S.val.stopped = true
      · rw [layers_fold_stopped A σ P tape j layers one zero θs MM _ _ hst, add_zero]
        rw [if_pos hst, add_zero] at ha
        have ha' : ((m * Charged.steps (rate MM m) S : ℕ) : ℚ) ≤
            (layerFixed m W P : ℚ) + (sampleCoef m W : ℚ) * layerSamples layers s (k - 1) := by
          exact_mod_cast ha
        have e1 : (0 : ℚ) ≤ (sampleCoef m W : ℚ) * ((totalCap P : ℚ) - s.total.get) := by positivity
        have e2 : (0 : ℚ) ≤ (cacheCoef m : ℚ) * ((totalCap P : ℚ) - s.total.get) := by positivity
        have e3 : (0 : ℚ) ≤ len * (layerFixed m W P : ℚ) := by positivity
        rw [Nat.cast_succ]
        linarith
      · have hst' : S.val.stopped = false := by simpa using hst
        rw [if_neg hst] at ha
        obtain ⟨hcap', hD', hcache'⟩ := hb hst'
        have hrest := ih (k + 1) S.val hst' hcap' (by simpa using hcache'.trans (Nat.le_succ _))
        simp only [Nat.add_sub_cancel] at hrest
        have ha' : ((m * Charged.steps (rate MM m) S : ℕ) : ℚ) ≤
            (layerFixed m W P : ℚ) + (sampleCoef m W : ℚ) * layerSamples layers s (k - 1) +
              (cacheCoef m : ℚ) * layerSamples layers S.val k := by
          exact_mod_cast ha
        have e1 : (sampleCoef m W : ℚ) * (layerSamples layers S.val k + s.total.get - S.val.total.get) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
        have e2 : (cacheCoef m : ℚ) * (layerSamples layers S.val k + s.total.get - S.val.total.get) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
        rw [Nat.mul_add, Nat.cast_add, Nat.cast_succ]
        linarith

/-- INTERNAL: **`m` times the steps of one core run is at most `coreBound`**, for
any tape and any layer array of at most `n + 1` duplicate-free layers of at most
`m` states.
TEXLINE: analysis.tex:40-55 -/
theorem coreRun_cost (MM : ℕ → ℕ) (A : PaperNFA Q) (σ : Selector A) (P : Params)
    (tape : Tape Q) (n : ℕ) (layers : Array (List Q)) (j : ℕ)
    (hsize : layers.size ≤ n + 1)
    (hL : ∀ L ∈ layers.toList, L.Nodup ∧ L.length ≤ Fintype.card Q) :
    Fintype.card Q *
        Charged.steps (rate MM (Fintype.card Q))
          (Nfa.Program.coreRun A σ P tape n layers j) ≤
      coreBound (Fintype.card Q) n (max 1 (MM (Fintype.card Q))) P := by
  set m := Fintype.card Q
  set W := max 1 (MM m)
  have hL' := layers_getD_length_le layers m hL
  unfold Nfa.Program.coreRun
  simp only [Charged.steps_bind]
  -- the sample sets of `q_I`
  obtain ⟨-, hSIsteps, hSIsize⟩ := foldl_inv_le (rate MM m) (fun (acc : Nfa.Program.Samples) (_ : ℕ) => do
      let T ← addWord [] []
      pure (acc.push T)) (fun _ => True) samplesSize (fun _ => 1) (fun _ => 1) (List.range P.α)
    (by intro acc _ _ _; refine ⟨trivial, by simp [addWord], by simp [addWord]⟩) #[] trivial
  simp only [List.map_const', List.length_range, List.sum_replicate, smul_eq_mul, mul_one,
    samplesSize_empty, zero_add] at hSIsteps hSIsize
  generalize hSI : Charged.foldl (fun (acc : Nfa.Program.Samples) (_ : ℕ) => do
      let T ← addWord [] []
      pure (acc.push T)) (List.range P.α) #[] = SI at hSIsteps hSIsize ⊢
  -- the store loop
  have hstore : Charged.steps (rate MM m) (Charged.foldl (fun (_ : Unit) (layer : List Q) =>
      Charged.foldl (fun (_ : Unit) (_ : Q) =>
          Charged.foldl (fun (_ : Unit) (_ : ℕ) => store) (List.range P.α) ()) layer ())
      layers.toList ()) ≤ (n + 1) * (m * P.α) := by
    refine (steps_foldl_le_sum (rate MM m) _ (fun _ => m * P.α) _ ?_ ()).trans ?_
    · intro b L hLm
      have := Charged.steps_foldl_le (k := P.α) (rate MM m)
        (f := fun (_ : Unit) (_ : Q) =>
          Charged.foldl (fun (_ : Unit) (_ : ℕ) => (store : Charged Op Cell Unit)) (List.range P.α) ())
        (by
          intro b a
          have := Charged.steps_foldl_le (k := 1) (rate MM m)
            (f := fun (_ : Unit) (_ : ℕ) => (store : Charged Op Cell Unit))
            (by intro b a; simp [store]) (List.range P.α) ()
          simpa using this) L ()
      exact this.trans (Nat.mul_le_mul_right _ (hL L hLm).2)
    · simp only [List.map_const', List.sum_replicate, smul_eq_mul, Array.length_toList]
      exact Nat.mul_le_mul_right _ hsize
  -- the layer loop
  have hcard : (Roster.insert ([] : List Bool) Roster.empty : Charged Op Cell _).val.card ≤ 1 := by
    rw [← Roster.card_toFinset, Roster.toFinset_insert, Roster.toFinset_empty]; simp
  have hD0 : layerSamples layers
      { prevP := fun _ => (Scalar.lit 1).val, prevS := fun _ => #[],
        curP := fun _ => (Scalar.lit 1).val,
        curS := Function.update (fun _ => #[]) A.qI SI.val,
        layerIdx := 0, total := (Scalar.lit (P.α : ℚ)).val,
        cache := (Roster.insert ([] : List Bool) Roster.empty : Charged Op Cell (Roster (List Bool))).val,
        stopped := false } (1 - 1) ≤ P.α := by
    unfold layerSamples
    simp only [Nat.sub_self]
    rw [← List.sum_toFinset _ (hL' 0).1]
    have : ∀ q, samplesSize (Function.update (fun _ => (#[] : Nfa.Program.Samples)) A.qI SI.val q) =
        if q = A.qI then samplesSize SI.val else 0 := by
      intro q; by_cases hq : q = A.qI
      · subst hq; simp
      · simp [hq]
    simp only [this, Finset.sum_ite_eq']
    split <;> omega
  have hfold := layers_fold_cost MM A σ P tape j layers (Scalar.lit 1).val (Scalar.lit 0).val
    (Scalar.lit (P.θ : ℚ)).val (by simp) hL' n 1
    { prevP := fun _ => (Scalar.lit 1).val, prevS := fun _ => #[],
      curP := fun _ => (Scalar.lit 1).val,
      curS := Function.update (fun _ => #[]) A.qI SI.val,
      layerIdx := 0, total := (Scalar.lit (P.α : ℚ)).val,
      cache := (Roster.insert ([] : List Bool) Roster.empty : Charged Op Cell (Roster (List Bool))).val,
        stopped := false } rfl
    (by simp [totalCap]) (hcard.trans (Nat.le_add_left _ _))
  have hlit : ∀ a : ℚ, Charged.steps (rate MM m) (Scalar.lit a) = 1 := by
    intro a; simp [Scalar.lit]
  have hdiv : ∀ x y : Scalar, Charged.steps (rate MM m) (Scalar.div x y) = 1 := by
    intro x y; simp [Scalar.div]
  have hins : Charged.steps (rate MM m)
      (Roster.insert ([] : List Bool) Roster.empty : Charged Op Cell _) = 1 := by
    simp [Charged.steps, Roster.cost_insert]
  rw [hlit, hlit, hlit, hins, hlit, hdiv]
  simp only [Nat.sub_self] at hfold
  have hα : (Scalar.lit (P.α : ℚ)).val.get = P.α := by simp
  rw [hα] at hfold
  generalize Charged.steps (rate MM (Fintype.card Q)) (Charged.foldl _ (List.range' 1 n) _) = F
    at hfold ⊢
  simp only [Nat.sub_self] at hD0
  generalize layerSamples layers _ 0 = D0 at hD0 hfold
  generalize Charged.steps (rate MM m) SI = a at hSIsteps ⊢
  generalize Charged.steps (rate MM m) (Charged.foldl _ layers.toList ()) = b at hstore ⊢
  rw [← Nat.cast_le (α := ℚ)]
  have hb' : (m : ℚ) * b ≤ m * ((n + 1) * (m * P.α)) := by
    have : (b : ℚ) ≤ (n + 1) * (m * P.α) := by exact_mod_cast hstore
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
  have ha' : (m : ℚ) * a ≤ m * P.α := by
    have : (a : ℚ) ≤ P.α := by exact_mod_cast hSIsteps
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
  have hD0' : (D0 : ℚ) ≤ P.α := by exact_mod_cast hD0
  have hH : (sampleCoef m W : ℚ) * ((totalCap P : ℚ) - P.α + D0) ≤
      (sampleCoef m W : ℚ) * (totalCap P : ℚ) :=
    mul_le_mul_of_nonneg_left (by linarith only [hD0']) (Nat.cast_nonneg _)
  have hH' : (cacheCoef m : ℚ) * ((totalCap P : ℚ) - P.α) ≤ (cacheCoef m : ℚ) * (totalCap P : ℚ) :=
    mul_le_mul_of_nonneg_left (by linarith only [show (0 : ℚ) ≤ P.α from Nat.cast_nonneg _])
      (Nat.cast_nonneg _)
  have hmQ : Fintype.card Q = m := rfl
  have hWd : max 1 (MM m) = W := rfl
  rw [hmQ, hWd] at hfold
  unfold coreBound
  push_cast at hfold ⊢
  have hmα : (0 : ℚ) ≤ (m : ℚ) * P.α := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  linarith only [hfold, hH, hH', ha', hb', hmα]


end Nfa.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `coreRun_cost` by the amortized potential `sampleCoef·(cap − t + D) + cacheCoef·(cap − t)` over `layerStep_cost`
-/
