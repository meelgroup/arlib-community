import Auditable.Model.Program
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.ByContra

/-!
# The semantics of the `BForm` combinators `auditQuery` is built from

`Interface/ProgramModel.lean`'s `auditQuery_holds_iff_mergedCheck` needs to read
the truth of `auditQuery F' K` (a syntactic `Pi2Query`) off as the semantic
`poscheck ∧ negcheck` (`Pseudocode.mergedCheck`). That requires knowing what each
combinator `Program.lean` builds `auditQuery`'s matrix from actually evaluates to:
`bAll`, `bAny`, `bImp`, `cnfForm`, `hashBitForm`, `neqForm`, `eqForm`. None of that
is in `Model/Program.lean` itself (it only needs the combinators to *build* the
query, not to read one back), so it is proved here, once, as plain facts about
`BForm.eval`.

`exists_forall_iff_forall_tuple` is the one genuinely combinatorial fact the
stock half of the query's correctness depends on: the paper's `∃` hash index
`stockWith` existentially quantifies, read against a formula whose matrix
instead takes the `∨` of one disjunct per index over an independently
*universally* quantified tuple of candidates (one `z₂` per index `i < c_high`).
These are classically equivalent (`Classical.choice`), and it is this
equivalence, not anything about `CNF` or `AffHash`, that turns `stockPart`'s
syntax into `stockWith`.

**PAPER:** none of these are results the paper states; it writes `auditQuery`'s
encoding directly as the merged `Σ₂ᴾ` query (finalaudit.tex:107, 136) and never
re-derives its semantics. **INTERNAL:** every lemma here is needed to prove that
encoding correct and the paper proves no part of it.
-/

set_option autoImplicit false

namespace Auditable.Program

/-- `bAll`'s truth is exactly `List.all` of its components' truth. -/
theorem bAll_eval {V : Type} (fs : List (BForm V)) (x : V → Bool) :
    (bAll fs).eval x = fs.all (fun f => f.eval x) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      show (f.eval x && (bAll fs).eval x) = _
      rw [ih]; simp [List.all_cons]

/-- `bAny`'s truth is exactly `List.any` of its components' truth. -/
theorem bAny_eval {V : Type} (fs : List (BForm V)) (x : V → Bool) :
    (bAny fs).eval x = fs.any (fun f => f.eval x) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      show (f.eval x || (bAny fs).eval x) = _
      rw [ih]; simp [List.any_cons]

/-- `bImp`'s truth is material implication. -/
theorem bImp_eval {V : Type} (f g : BForm V) (x : V → Bool) :
    (bImp f g).eval x = (!f.eval x || g.eval x) := by
  simp [bImp, BForm.eval]

/-- `cnfForm G z` reads a CNF `G` back through the renaming `z`: it is true under
`x` exactly when `G` is satisfied by the assignment `x` gives each of `G`'s
variables through `z`. -/
theorem cnfForm_eval {N : ℕ} {V : Type} (G : CNF N) (z : Fin N → V) (x : V → Bool) :
    (cnfForm G z).eval x = G.eval (fun v => x (z v)) := by
  unfold cnfForm CNF.eval
  rw [bAll_eval, List.all_map]
  refine List.all_congr rfl fun c => ?_
  show (bAny (c.map fun l =>
      if l.pos then BForm.var (z l.var) else BForm.not (BForm.var (z l.var)))).eval x = _
  rw [bAny_eval, List.any_map]
  refine List.any_congr rfl fun l => ?_
  cases h : l.pos <;> simp [BForm.eval, h]

/-- `BForm.eval` commutes with a `foldl` of nested `BForm.xor`: the syntactic fold
reads back as the same fold over `Bool.xor` of each step's evaluated formula. -/
theorem foldl_xor_eval {V ι : Type} (f : ι → BForm V) (lst : List ι) (init : BForm V)
    (x : V → Bool) :
    (lst.foldl (fun acc j => BForm.xor acc (f j)) init).eval x
      = lst.foldl (fun acc j => Bool.xor acc ((f j).eval x)) (init.eval x) := by
  induction lst generalizing init with
  | nil => rfl
  | cons a l ih =>
      show (l.foldl (fun acc j => BForm.xor acc (f j)) (BForm.xor init (f a))).eval x = _
      rw [ih]; rfl

/-- `hashBitForm h z i` reads back as output bit `i` of `h.apply`, applied to the
assignment `x` gives `h`'s domain through `z`: the formula is a faithful
transcription of `AffHash.apply`'s fold. -/
theorem hashBitForm_eval {N m : ℕ} {V : Type} (h : AffHash N m) (z : Fin N → V) (i : Fin m)
    (x : V → Bool) :
    (hashBitForm h z i).eval x = h.apply (fun v => x (z v)) i := by
  unfold hashBitForm AffHash.apply
  show BForm.eval (BForm.xor _ _) x = _
  simp only [BForm.eval]
  rw [foldl_xor_eval]
  simp [BForm.eval]

/-- `neqForm p q` is true exactly when some coordinate of the two bit-vectors of
formulas disagrees. -/
theorem neqForm_eval {k : ℕ} {V : Type} (p q : Fin k → BForm V) (x : V → Bool) :
    (neqForm p q).eval x = decide (∃ i, (p i).eval x ≠ (q i).eval x) := by
  unfold neqForm
  rw [bAny_eval, List.any_map]
  unfold Function.comp
  dsimp only [BForm.eval]
  rw [Bool.eq_iff_iff, decide_eq_true_eq, List.any_eq_true]
  constructor
  · rintro ⟨i, -, hi⟩
    exact ⟨i, by simpa [Bool.xor_iff_ne] using hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, List.mem_finRange i, by simpa [Bool.xor_iff_ne, ne_comm] using hi⟩

/-- `eqForm p q` is true exactly when every coordinate of the two bit-vectors of
formulas agrees. -/
theorem eqForm_eval {k : ℕ} {V : Type} (p q : Fin k → BForm V) (x : V → Bool) :
    (eqForm p q).eval x = decide (∀ i, (p i).eval x = (q i).eval x) := by
  unfold eqForm bIff
  rw [bAll_eval, List.all_map]
  unfold Function.comp
  dsimp only [BForm.eval]
  rw [Bool.eq_iff_iff, decide_eq_true_eq, List.all_eq_true]
  constructor
  · intro h i
    have := h i (List.mem_finRange i)
    simpa [Bool.xor_iff_ne] using this
  · intro h i _
    simp [h i]

/-- The combinatorial fact the stock half of `auditQuery` is built on: a single
witnessing index `i` with `Φ i` true of every `z` is, classically, exactly the
same thing as `Φ` holding of `f i` at `i` for every assignment `f` to the
independently-quantified tuple `(z_i)_i`. The forward direction is trivial
(evaluate the fixed witness at `f i`); the reverse is a contrapositive argument
by choice: if every index had a counterexample, assembling them into one tuple
`f` would violate the hypothesis at that `f`. -/
theorem exists_forall_iff_forall_tuple {ι Z : Type} (Φ : ι → Z → Prop) :
    (∃ i, ∀ z, Φ i z) ↔ (∀ f : ι → Z, ∃ i, Φ i (f i)) := by
  constructor
  · rintro ⟨i, hi⟩ f
    exact ⟨i, hi (f i)⟩
  · intro h
    apply Classical.byContradiction
    intro hc
    have hc' : ∀ i : ι, ∃ z : Z, ¬ Φ i z := by
      intro i
      apply Classical.byContradiction
      intro hz
      exact hc ⟨i, fun z => Classical.byContradiction (fun hnz => hz ⟨z, hnz⟩)⟩
    choose f hf using hc'
    obtain ⟨i, hi⟩ := h f
    exact hf i hi

/-- Assemble an element of `Fin (N + chigh * N + clow) → Bool` from its three
independent blocks: the `z₁`-block (`p1`), the `z₂`-blocks (`p2`), and the
`α`-block (`a`). This is the joint surjectivity witness `auditQuery`'s three
disjoint universal blocks need: any choice of the three components extends to
some `x : Fin nU → Bool`, which is what lets the `∀x` of `Pi2Query.holds` be
read apart into the three separate quantifiers `poscheck`/`negcheck` use. -/
noncomputable def assemble {N chigh clow : ℕ} (p1 : Fin N → Bool) (p2 : Fin chigh → Fin N → Bool)
    (a : Fin clow → Bool) : Fin (N + chigh * N + clow) → Bool :=
  Fin.addCases
    (fun i => Fin.addCases (fun j => p1 j)
      (fun k => p2 (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) i)
    (fun t => a t)

theorem assemble_z1 {N chigh clow : ℕ} (p1 : Fin N → Bool) (p2 : Fin chigh → Fin N → Bool)
    (a : Fin clow → Bool) (j : Fin N) :
    assemble p1 p2 a (Fin.castAdd clow (Fin.castAdd (chigh * N) j)) = p1 j := by
  unfold assemble; rw [Fin.addCases_left, Fin.addCases_left]

theorem assemble_z2 {N chigh clow : ℕ} (p1 : Fin N → Bool) (p2 : Fin chigh → Fin N → Bool)
    (a : Fin clow → Bool) (i : Fin chigh) (j : Fin N) :
    assemble p1 p2 a (Fin.castAdd clow (Fin.natAdd N (finProdFinEquiv (i, j)))) = p2 i j := by
  unfold assemble; rw [Fin.addCases_left, Fin.addCases_right]; simp

theorem assemble_alpha {N chigh clow : ℕ} (p1 : Fin N → Bool) (p2 : Fin chigh → Fin N → Bool)
    (a : Fin clow → Bool) (t : Fin clow) :
    assemble p1 p2 a (Fin.natAdd (N + chigh * N) t) = a t := by
  unfold assemble; rw [Fin.addCases_right]

/-- A function inequality read as a witnessed pointwise difference: the form
`neqForm_eval` and `stockWith`/`holesWith` disagree on (the former per-bit, the
latter on the whole hash output), so the bridge crosses between them here. -/
theorem func_ne_iff {A B : Type} (f g : A → B) : f ≠ g ↔ ∃ x, f x ≠ g x := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hc
    exact h (funext fun x => Classical.byContradiction (fun hne => hc ⟨x, hne⟩))
  · rintro ⟨x, hx⟩ heq
    exact hx (congrFun heq x)

end Auditable.Program
