import Nfa.Interface.Pseudocode

/-!
# One pseudocode layer only touches its own layer

`layerStep_frame`: the pseudocode's `layerStep A σ P n st i` (countNFA.9–11) changes
`p(q^i)`, `S^r(q^i)` and the interrupt flag and nothing else, so its law is the law of
its layer-`i` projection, re-inserted into `st`.  The program–pseudocode bridge for
`runLayers` uses it to rebuild the full pseudocode state from the projection the
`layerStep` bridge controls.
-/

set_option autoImplicit false

namespace Nfa.Analysis

open Nfa.Pseudocode

variable {Q : Type} [Fintype Q] [LinearOrder Q]

/-- `estimateAndSample` at layer `i`, as a frame: only `p i` and `S i` change.

INTERNAL: frame bookkeeping for the `runLayers` bridge.
TEXLINE: algorithm.tex:64-84 -/
theorem estimateAndSample_frame (A : PaperNFA Q) (σ : Selector A) (P : Params) (i : ℕ)
    (st : CoreState Q) (q : Q) :
    estimateAndSample A σ P i st q = (estimateAndSample A σ P i st q).map (fun st' =>
      ({ p := Function.update st.p i (st'.p i), S := Function.update st.S i (st'.S i),
         stopped := st'.stopped } : CoreState Q)) := by
  unfold estimateAndSample
  simp only [PMF.map_bind, PMF.map_comp]
  congr 1; funext hatS
  congr 1; funext S'
  simp only [Function.comp_apply, Function.update_self]

omit [Fintype Q] [LinearOrder Q] in
/-- Writing a state's layer `i` back into a base it already agrees with off layer `i`
changes nothing.

INTERNAL: frame bookkeeping. -/
theorem frame_self (i : ℕ) (b st0 : CoreState Q) (hp : ∀ ℓ, ℓ ≠ i → st0.p ℓ = b.p ℓ)
    (hS : ∀ ℓ, ℓ ≠ i → st0.S ℓ = b.S ℓ) :
    ({ p := Function.update b.p i (st0.p i), S := Function.update b.S i (st0.S i),
       stopped := st0.stopped } : CoreState Q) = st0 := by
  cases st0 with
  | mk p S stopped =>
    simp only [CoreState.mk.injEq, and_true]
    constructor
    · funext ℓ; by_cases h : ℓ = i
      · subst h; simp
      · rw [Function.update_of_ne h]; exact (hp ℓ h).symm
    · funext ℓ; by_cases h : ℓ = i
      · subst h; simp
      · rw [Function.update_of_ne h]; exact (hS ℓ h).symm

/-- `processLayer` at layer `i`, started from a state agreeing with `b` off layer `i`,
is a frame on `b`.

INTERNAL: induction step for `layerStep_frame`. -/
theorem processLayer_frame (A : PaperNFA Q) (σ : Selector A) (P : Params) (n i : ℕ)
    (b : CoreState Q) (qs : List Q) : ∀ st0 : CoreState Q,
    (∀ ℓ, ℓ ≠ i → st0.p ℓ = b.p ℓ) → (∀ ℓ, ℓ ≠ i → st0.S ℓ = b.S ℓ) →
    processLayer A σ P n i st0 qs = (processLayer A σ P n i st0 qs).map (fun st' =>
      ({ p := Function.update b.p i (st'.p i), S := Function.update b.S i (st'.S i),
         stopped := st'.stopped } : CoreState Q)) := by
  induction qs with
  | nil =>
    intro st0 hp hS
    simp only [processLayer, PMF.pure_map, frame_self i b st0 hp hS]
  | cons q qs ih =>
    intro st0 hp hS
    simp only [processLayer]
    split_ifs with hst
    · simp only [PMF.pure_map, frame_self i b st0 hp hS]
    · rw [estimateAndSample_frame, PMF.bind_map, PMF.map_bind]
      congr 1; funext st'
      simp only [Function.comp_apply]
      apply ih
      · intro ℓ hℓ; simp only [interrupt, Function.update_of_ne hℓ]; exact hp ℓ hℓ
      · intro ℓ hℓ; simp only [interrupt, Function.update_of_ne hℓ]; exact hS ℓ hℓ

/-- **The pseudocode's layer step is a frame on layer `i`.**  `layerStep A σ P n st i`
has the same law as its layer-`i` projection `(p i, S i, stopped)` written back into
`st`.

INTERNAL: frame bookkeeping for the `runLayers` bridge; the paper's countNFA.9–11
writes only `p(q^i)`, `S^r(q^i)` for `q ∈ Q^i` and the interrupt flag.
TEXLINE: algorithm.tex:90-112 -/
theorem layerStep_frame (A : PaperNFA Q) (σ : Selector A) (P : Params) (n : ℕ)
    (st : CoreState Q) (i : ℕ) :
    layerStep A σ P n st i = (layerStep A σ P n st i).map (fun st' =>
      ({ p := Function.update st.p i (st'.p i), S := Function.update st.S i (st'.S i),
         stopped := st'.stopped } : CoreState Q)) := by
  unfold layerStep
  split_ifs with hst
  · simp only [PMF.pure_map, frame_self i st st (fun _ _ => rfl) (fun _ _ => rfl)]
  · exact processLayer_frame A σ P n i st _ st (fun _ _ => rfl) (fun _ _ => rfl)

end Nfa.Analysis
