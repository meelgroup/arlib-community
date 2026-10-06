import Auditable.Model.Prior
import Auditable.Model.Run
import Auditable.Meta.ModelClosure
import Auditable.Analysis.TheoremSoundProof
import Auditable.Analysis.TheoremCompleteProof
import Auditable.Analysis.TheoremOneQueryProof
import Auditable.Analysis.TheoremQuerySizeProof
import Auditable.Interface.Encoding
import Auditable.Interface.Pseudocode
import Auditable.Interface.ProgramModel

open Auditable.Model.Operations
open Arlib.Computation (Charged CostVec)

/-- **INTERNAL**: a `foldlWhile` loop charges at most `k` per round in a single
coordinate `o` of the cost vector, so its total at `o` is at most `length * k`.
Not in the paper — pure cost bookkeeping about `Arlib.Computation.Charged`, needed
because `Charged.foldlWhile`'s only public cost fact (`steps_foldlWhile_le`) is
stated for the *scalar* step count under a `Rate`, not for one coordinate of the
vector-valued `cost`; this is that same induction specialised to one coordinate. -/
theorem Auditable.Analysis.cost_apply_foldlWhile_le {κ κₛ : Type} [DecidableEq κ]
    {β ι : Type} {f : β → ι → Charged κ κₛ (Option β)} (o : κ) {k : ℕ}
    (h : ∀ b a, (f b a).cost o ≤ k) :
    ∀ (l : List ι) (b : β), (Charged.foldlWhile f l b).cost o ≤ l.length * k := by
  intro l
  induction l with
  | nil => intro b; simp
  | cons a l ih =>
      intro b
      have hstep := h b a
      show (Charged.foldlWhile f (a :: l) b).cost o ≤ (a :: l).length * k
      unfold Charged.foldlWhile
      rcases heq : f b a with ⟨v, c, s⟩
      rw [heq] at hstep
      simp only [Charged.cost] at hstep
      rcases v with _ | b'
      · simp only [List.length_cons]
        show c o ≤ (l.length + 1) * k
        calc c o ≤ k := hstep
          _ ≤ (l.length + 1) * k := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
      · have hrest := ih b'
        simp only [List.length_cons]
        show c o + (Charged.foldlWhile f l b').cost o ≤ (l.length + 1) * k
        calc c o + (Charged.foldlWhile f l b').cost o
            ≤ k + l.length * k := Nat.add_le_add hstep hrest
          _ = (l.length + 1) * k := by ring

/-- **INTERNAL**: one round of the holes loop (AFC-4..10, combined.tex:28-37) charges
exactly one `holesQuery` and nothing else — `holesOracle` is the only call, and both
of `holesStep`'s branches are a bare `pure` afterwards. -/
theorem Auditable.Analysis.holesStep_cost {N : ℕ} (G : CNF N) (reg : Program.HolesReg N)
    (m : ℕ) : (Program.holesStep G reg m).cost = CostVec.one Op.holesQuery := by
  unfold Program.holesStep
  simp only [Charged.cost_bind]
  cases (holesOracle G m).val <;> simp [holesOracle, Charged.cost_op]

/-- **INTERNAL**: one round of the stock loop (AFC-11..17, combined.tex:38-49) charges
at most one `stockQuery` and never a `holesQuery` or `sigma2Query` — a recorded
witness makes the round a free `pure none`, and otherwise the only call is
`stockOracle`, again followed by a bare `pure`. -/
theorem Auditable.Analysis.stockStep_cost {N : ℕ} (G : CNF N) (reg : Program.StockReg N)
    (m : ℕ) : (Program.stockStep G reg m).cost Op.holesQuery = 0 ∧
      (Program.stockStep G reg m).cost Op.stockQuery ≤ 1 ∧
      (Program.stockStep G reg m).cost Op.sigma2Query = 0 := by
  unfold Program.stockStep
  cases reg with
  | some w => simp
  | none =>
      simp only [Charged.cost_bind]
      cases (stockOracle G m).val <;> simp [stockOracle, Charged.cost_op]

/-- Proof-side owner for `Auditable.afCounter_queries`; its statement is fixed by the proof charter.

`afCounter` is the holes loop (AFC-4..10) bound to the stock loop (AFC-11..17)
bound to an uncharged `pure`, so its cost is their sum (`Charged.cost_bind`). Each
loop is `Charged.foldlWhile` over `List.range' 1 (nPrime n)`, whose length is
`nPrime n`; `cost_apply_foldlWhile_le` bounds one coordinate of a loop's total by
its round count times the per-round bound from `holesStep_cost`/`stockStep_cost`.
The holes loop never touches `stockQuery`/`sigma2Query` and the stock loop never
touches `holesQuery`/`sigma2Query`, so each of the three totals comes from exactly
one loop. PAPER: combined.tex:23-52 (the two `for m = 1 to n'` loops of
Algorithm~\ref{algo:pigeons}); no call in either loop is a `sigma2Query`, which
belongs only to `CountAuditor` (finalaudit.tex:107, 136). -/
theorem Auditable.Analysis.afCounter_queries_proof (hprior : Prior) {n : ℕ} (F : CNF n) : (Program.afCounter F).cost Op.holesQuery ≤ nPrime n ∧ (Program.afCounter F).cost Op.stockQuery ≤ nPrime n ∧ (Program.afCounter F).cost Op.sigma2Query = 0 := by
  have hlen : (List.range' 1 (nPrime n)).length = nPrime n := by simp
  set F' := makeCopies F (copies n) with hF'
  set holesLoop := Charged.foldlWhile (Program.holesStep F') (List.range' 1 (nPrime n))
    (Program.emptyHolesReg (nPrime n)) with hholesLoop
  set stockLoop := Charged.foldlWhile (Program.stockStep F') (List.range' 1 (nPrime n))
    (none : Program.StockReg (nPrime n)) with hstockLoop
  have hcost : (Program.afCounter F).cost = holesLoop.cost + stockLoop.cost := by
    show (Program.afCounter F).cost = holesLoop.cost + stockLoop.cost
    unfold Program.afCounter
    simp only [Charged.cost_bind, Charged.cost_pure, add_zero, ← hF']
    rfl
  have hholesQ : holesLoop.cost Op.holesQuery ≤ nPrime n := by
    have := Auditable.Analysis.cost_apply_foldlWhile_le (f := Program.holesStep F')
      Op.holesQuery (k := 1) (fun b a => by rw [Auditable.Analysis.holesStep_cost]; simp)
      (List.range' 1 (nPrime n)) (Program.emptyHolesReg (nPrime n))
    simpa [hlen, hholesLoop] using this
  have hholesS : holesLoop.cost Op.stockQuery = 0 := by
    have := Auditable.Analysis.cost_apply_foldlWhile_le (f := Program.holesStep F')
      Op.stockQuery (k := 0) (fun b a => by rw [Auditable.Analysis.holesStep_cost]; simp)
      (List.range' 1 (nPrime n)) (Program.emptyHolesReg (nPrime n))
    simp only [hholesLoop]
    omega
  have hholesSig : holesLoop.cost Op.sigma2Query = 0 := by
    have := Auditable.Analysis.cost_apply_foldlWhile_le (f := Program.holesStep F')
      Op.sigma2Query (k := 0) (fun b a => by rw [Auditable.Analysis.holesStep_cost]; simp)
      (List.range' 1 (nPrime n)) (Program.emptyHolesReg (nPrime n))
    simp only [hholesLoop]
    omega
  have hstockQ : stockLoop.cost Op.stockQuery ≤ nPrime n := by
    have := Auditable.Analysis.cost_apply_foldlWhile_le (f := Program.stockStep F')
      Op.stockQuery (k := 1) (fun b a => (Auditable.Analysis.stockStep_cost F' b a).2.1)
      (List.range' 1 (nPrime n)) (none : Program.StockReg (nPrime n))
    simpa [hlen, hstockLoop] using this
  have hstockH : stockLoop.cost Op.holesQuery = 0 := by
    have := Auditable.Analysis.cost_apply_foldlWhile_le (f := Program.stockStep F')
      Op.holesQuery (k := 0) (fun b a => le_of_eq (Auditable.Analysis.stockStep_cost F' b a).1)
      (List.range' 1 (nPrime n)) (none : Program.StockReg (nPrime n))
    simp only [hstockLoop]
    omega
  have hstockSig : stockLoop.cost Op.sigma2Query = 0 := by
    have := Auditable.Analysis.cost_apply_foldlWhile_le (f := Program.stockStep F')
      Op.sigma2Query (k := 0) (fun b a => le_of_eq (Auditable.Analysis.stockStep_cost F' b a).2.2)
      (List.range' 1 (nPrime n)) (none : Program.StockReg (nPrime n))
    simp only [hstockLoop]
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hcost, CostVec.add_apply]; omega
  · rw [hcost, CostVec.add_apply]; omega
  · rw [hcost, CostVec.add_apply]; omega

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `afCounter_queries_proof` via `cost_apply_foldlWhile_le` (one-coordinate
  `foldlWhile` cost bound, proved by induction through `Charged`'s public `val`/`cost`
  API — its private constructor blocks a direct `simp` unfold, but `cases`/`rcases`
  on `f b a` still works since structure `cases` bypasses field privacy) applied to
  `holesStep_cost`/`stockStep_cost`'s per-round bounds.
-/
