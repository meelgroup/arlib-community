import Auditable.Model.Program
import Auditable.Interface.Pseudocode
import Auditable.Interface.Encoding
import Auditable.Model.Prior
import Auditable.Model.Prelude
import Auditable.Model.Operations
import Auditable.Model.Run
import Auditable.Analysis.BFormEncoding
import Arlib.Computation.Charged

/-!
# The program and the model are the same algorithm

`Auditable.Model.Program` is what the paper's claims are about: a charged
computation whose state is sealed and whose cost is an operator applied to it.
`Auditable.Interface.Pseudocode` is the same algorithm as mathematics for the
answer/output object the correctness theorem measures. Time and space stay over
`Auditable.Model.Program`; this file is only the transport for correctness.

It is a ladder. Each theorem below is proved from the ones above it, and
`countAuditor_afCounter_val_eq_verdict_result` is the top: it is the one lemma the analysis rewrites
through, and the only one anything outside this file should need.

Every rung is now climbed. The `BForm`-level semantics `auditQuery`'s matrix is
built on (`cnfForm`, `hashBitForm`, `neqForm`, `eqForm`, …) and the combinatorial
fact `auditQuery_holds_iff_mergedCheck` needs for its stock half live in
`Auditable.Analysis.BFormEncoding`, imported below.
-/

set_option autoImplicit false

namespace Auditable

/-- The cons case of `Charged.foldlWhile`, read off through `.val`: not stated in
`Arlib.Computation.Charged` (only the `nil` case is), so every induction over a
`foldlWhile` loop in this file goes through this one unfolding step first. -/
theorem val_foldlWhile_cons {κ κₛ : Type} {α β : Type}
    (f : β → α → Arlib.Computation.Charged κ κₛ (Option β)) (a : α) (l : List α) (b : β) :
    (Arlib.Computation.Charged.foldlWhile f (a :: l) b).val = match (f b a).val with
      | none => b
      | some b' => (Arlib.Computation.Charged.foldlWhile f l b').val := by
  rw [Arlib.Computation.Charged.val.eq_1, Arlib.Computation.Charged.foldlWhile.eq_2]
  cases h : (f b a).val
  · rw [Arlib.Computation.Charged.val.eq_1] at h
    simp [h]
  · rw [Arlib.Computation.Charged.val.eq_1] at h
    simp only [h, Arlib.Computation.Charged.val.eq_1]

/-- One iteration of the program's holes loop (line 5 of AFCounter) returns exactly what the pseudocode's 3QBFCheck on φ_holes(m) returns, packaged with the round index m. -/
theorem holesStep_val {N : ℕ} (G : Auditable.CNF N) (reg : Auditable.Program.HolesReg N) (m : ℕ) : (Auditable.Program.holesStep G reg m).val = (Auditable.Interface.Pseudocode.holesRet G m).map (fun hs => (⟨m, hs⟩ : Auditable.Program.HolesReg N)) := by
  show (Auditable.Model.Operations.holesOracle G m >>= fun ret =>
      match ret with
      | some hs => pure (some (⟨m, hs⟩ : Auditable.Program.HolesReg N))
      | none => pure none).val = (Auditable.Interface.Pseudocode.holesRet G m).map (fun hs => (⟨m, hs⟩ : Auditable.Program.HolesReg N))
  rw [Arlib.Computation.Charged.val_bind, Auditable.Interface.holesOracle_val]
  show (match Auditable.Interface.holesAnswer G m with
      | some hs => (pure (some (⟨m, hs⟩ : Auditable.Program.HolesReg N)) : Arlib.Computation.Charged Auditable.Model.Operations.Op Auditable.Model.Operations.Cell (Option (Auditable.Program.HolesReg N)))
      | none => pure none).val = (Auditable.Interface.holesAnswer G m).map (fun hs => (⟨m, hs⟩ : Auditable.Program.HolesReg N))
  cases Auditable.Interface.holesAnswer G m <;> rfl

/-- The program's initial holes register (c_low = 0, empty assignment) is the pseudocode's witness at index 0. -/
theorem emptyHolesReg_eq {N : ℕ} (G : Auditable.CNF N) : Auditable.Program.emptyHolesReg N = (⟨0, Auditable.Interface.Pseudocode.holesWitnessAt G 0⟩ : Auditable.Program.HolesReg N) := by
  unfold Auditable.Program.emptyHolesReg
  congr 1
  funext x
  cases (Auditable.Interface.Pseudocode.holesWitnessAt G 0) x with
  | mk A b =>
    congr 1 <;> (funext i; exact i.elim0)

/-- Generalized loop invariant for the break-on-failure holes loop: induction on k shows the fold stops at the first failing m and records c_low = m - 1. If no m fails, it records the last index. -/
theorem holesFold_range' {N : ℕ} (G : Auditable.CNF N) (a k : ℕ) : (Arlib.Computation.Charged.foldlWhile (Auditable.Program.holesStep G) (List.range' a k) (⟨a - 1, Auditable.Interface.Pseudocode.holesWitnessAt G (a - 1)⟩ : Auditable.Program.HolesReg N)).val = (match (List.range' a k).find? (Auditable.Interface.Pseudocode.holesFails G) with | some m => (⟨m - 1, Auditable.Interface.Pseudocode.holesWitnessAt G (m - 1)⟩ : Auditable.Program.HolesReg N) | none => ⟨a + k - 1, Auditable.Interface.Pseudocode.holesWitnessAt G (a + k - 1)⟩) := by
  induction k generalizing a with
  | zero =>
      simp [List.range']
  | succ k ih =>
      rw [List.range'_succ, Auditable.val_foldlWhile_cons, Auditable.holesStep_val]
      rw [show a + (k + 1) - 1 = a + k from by omega]
      cases hr : Auditable.Interface.Pseudocode.holesRet G a with
      | none =>
          have hfails : Auditable.Interface.Pseudocode.holesFails G a = true := by
            simp [Auditable.Interface.Pseudocode.holesFails, hr]
          simp [hr, List.find?_cons, hfails]
      | some hs =>
          have hfails : Auditable.Interface.Pseudocode.holesFails G a = false := by
            simp [Auditable.Interface.Pseudocode.holesFails, hr]
          have hw : Auditable.Interface.Pseudocode.holesWitnessAt G a = hs := by
            simp [Auditable.Interface.Pseudocode.holesWitnessAt, hr]
          simp only [hr, Option.map_some]
          have hih := ih (a + 1)
          rw [show a + 1 - 1 = a from by omega, hw] at hih
          rw [hih, show a + 1 + k - 1 = a + k from by omega]
          simp [List.find?_cons, hfails]

/-- The program's whole holes loop (m = 1 to n', starting from the empty register) computes the pseudocode's (c_low, hashassgn_holes). Low confidence that the loop bound is N = n' and that this fold is literally `Interface.holesLoop G`; adjust to match the actual definition. -/
theorem holesLoop_val {N : ℕ} (G : Auditable.CNF N) : (Arlib.Computation.Charged.foldlWhile (Auditable.Program.holesStep G) (List.range' 1 N) (Auditable.Program.emptyHolesReg N)).val = Auditable.Interface.Pseudocode.holesResult G := by
  rw [Auditable.emptyHolesReg_eq, Auditable.holesFold_range' G 1 N]
  unfold Auditable.Interface.Pseudocode.holesResult Auditable.Interface.Pseudocode.holesBreak
    Auditable.Interface.Pseudocode.loopRange
  rw [show (1:ℕ) + N - 1 = N from by omega]
  rfl

/-- Before c_high has been found, one iteration of the program's stock loop returns the pseudocode's 2QBFCheck answer on φ_stock(m), tagged with m. -/
theorem stockStep_none_val {N : ℕ} (G : Auditable.CNF N) (m : ℕ) : (Auditable.Program.stockStep G none m).val = some ((Auditable.Interface.Pseudocode.stockRet G m).map (fun hs => (⟨m, hs⟩ : Σ j : ℕ, (Fin j → Auditable.AffHash N j)))) := by
  show (Auditable.Model.Operations.stockOracle G m >>= fun ret =>
      match ret with
      | some hs => pure (some (some (⟨m, hs⟩ : Σ j : ℕ, (Fin j → Auditable.AffHash N j))))
      | none => pure (some none)).val = some ((Auditable.Interface.Pseudocode.stockRet G m).map (fun hs => (⟨m, hs⟩ : Σ j : ℕ, (Fin j → Auditable.AffHash N j))))
  rw [Arlib.Computation.Charged.val_bind, Auditable.Interface.stockOracle_val]
  show (match Auditable.Interface.stockAnswer G m with
      | some hs => (pure (some (some (⟨m, hs⟩ : Σ j : ℕ, (Fin j → Auditable.AffHash N j)))) : Arlib.Computation.Charged Auditable.Model.Operations.Op Auditable.Model.Operations.Cell (Option (Auditable.Program.StockReg N)))
      | none => pure (some none)).val = some ((Auditable.Interface.stockAnswer G m).map (fun hs => (⟨m, hs⟩ : Σ j : ℕ, (Fin j → Auditable.AffHash N j))))
  cases Auditable.Interface.stockAnswer G m <;> rfl

/-- Loop invariant for the break-on-success stock loop: the fold keeps a found register and otherwise records the first m whose φ_stock(m) holds, with its witness. -/
theorem stockFold_val {N : ℕ} (G : Auditable.CNF N) (l : List ℕ) (reg : Auditable.Program.StockReg N) : (Arlib.Computation.Charged.foldlWhile (Auditable.Program.stockStep G) l reg).val = reg.or ((l.find? (Auditable.Interface.Pseudocode.stockSucceeds G)).map (fun m => (⟨m, Auditable.Interface.Pseudocode.stockWitnessAt G m⟩ : Σ j : ℕ, (Fin j → Auditable.AffHash N j)))) := by
  induction l generalizing reg with
  | nil => cases reg <;> rfl
  | cons a l ih =>
      rw [Auditable.val_foldlWhile_cons]
      cases reg with
      | some w =>
          rw [Auditable.Interface.stockStep_some]
          rfl
      | none =>
          rw [Auditable.stockStep_none_val]
          cases hr : Auditable.Interface.Pseudocode.stockRet G a with
          | none =>
              have hsucc : Auditable.Interface.Pseudocode.stockSucceeds G a = false := by
                simp [Auditable.Interface.Pseudocode.stockSucceeds, hr]
              simp only [hr, Option.map_none]
              rw [ih none]
              simp [List.find?_cons, hsucc]
          | some hs =>
              have hsucc : Auditable.Interface.Pseudocode.stockSucceeds G a = true := by
                simp [Auditable.Interface.Pseudocode.stockSucceeds, hr]
              have hw : Auditable.Interface.Pseudocode.stockWitnessAt G a = hs := by
                simp [Auditable.Interface.Pseudocode.stockWitnessAt, hr]
              simp only [hr, Option.map_some]
              rw [ih (some ⟨a, hs⟩)]
              simp [List.find?_cons, hsucc, hw]

/-- The program's whole stock loop (m' = 1 to n', starting with nothing found) computes the pseudocode's (c_high, hashassgn_stock). Low confidence that this fold, with bound N and initial `none`, is literally `Interface.stockHigh G`; adjust to match. -/
theorem stockHigh_eq_stockResult {N : ℕ} (G : Auditable.CNF N) : Auditable.Interface.stockHigh G = Auditable.Interface.Pseudocode.stockResult G := by
  unfold Auditable.Interface.stockHigh Auditable.Interface.stockLoop
  rw [Auditable.stockFold_val]
  unfold Auditable.Interface.Pseudocode.stockResult Auditable.Interface.Pseudocode.stockBreak
    Auditable.Interface.Pseudocode.loopRange
  cases (List.range' 1 N).find? (Auditable.Interface.Pseudocode.stockSucceeds G) <;> rfl

/-- AFCounter as a program returns exactly the pseudocode's tuple (CntEst, c_low, c_high, hashassgn_stock, hashassgn_holes) on F' = MakeCopies(F, log n). -/
theorem afCounter_val_eq_result {n : ℕ} (F : Auditable.CNF n) : (Auditable.Program.afCounter F).val = Auditable.Interface.Pseudocode.result F := by
  rw [Auditable.Interface.afCounter_val]
  unfold Auditable.Interface.holesLoop
  rw [Auditable.holesLoop_val, Auditable.stockHigh_eq_stockResult]
  rfl

/-- The program's single Σ₂ᴾ audit query holds exactly when the pseudocode's poscheck ∧ negcheck holds, i.e. the paper's merging of lines zconpcheck and zconncheck. -/
theorem auditQuery_holds_iff_mergedCheck {n : ℕ} (F : Auditable.CNF n) (K : Auditable.Cert (Auditable.nPrime n)) : (Auditable.Program.auditQuery (Auditable.Interface.fPrime F) K).holds ↔ Auditable.Interface.Pseudocode.mergedCheck F K := by
  unfold Auditable.Pi2Query.holds Auditable.Program.auditQuery
  dsimp only
  simp only [Auditable.BForm.eval, Auditable.Program.bImp_eval, Auditable.Program.bAny_eval,
    Auditable.Program.cnfForm_eval, List.any_map]
  unfold Function.comp
  dsimp only
  simp only [Auditable.BForm.eval, Auditable.Program.bImp_eval, Auditable.Program.cnfForm_eval,
    Auditable.Program.neqForm_eval, Auditable.Program.hashBitForm_eval, Auditable.Program.eqForm_eval,
    Sum.elim_inl, Sum.elim_inr]
  simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', Bool.eq_false_iff, List.any_eq_true]
  unfold Auditable.Interface.Pseudocode.mergedCheck Auditable.Interface.Pseudocode.poscheck
    Auditable.Interface.Pseudocode.negcheck
  unfold Auditable.stockWith Auditable.holesWith
  constructor
  · intro hBig
    constructor
    · intro z1 hz1
      have key : ∀ f : Fin K.chigh → (Fin (Auditable.nPrime n) → Bool), ∃ i,
          ((Auditable.Interface.fPrime F).eval (f i) = true ∧ f i ≠ z1) →
            (K.hstock i).apply (f i) ≠ (K.hstock i).apply z1 := by
        intro f
        obtain ⟨y, hcase, -⟩ := hBig (Auditable.Program.assemble z1 f (fun _ => false))
        simp only [Auditable.Program.assemble_z1, Auditable.Program.assemble_z2] at hcase
        rcases hcase with h1 | ⟨i, -, hi⟩
        · exact absurd hz1 h1
        · refine ⟨i, ?_⟩
          rintro ⟨hG, hne⟩
          rcases hi with h | h
          · exact (h (by simp [hG, (Auditable.Program.func_ne_iff _ _).mp hne])).elim
          · exact (Auditable.Program.func_ne_iff _ _).mpr h
      obtain ⟨i, hi⟩ := (Auditable.Program.exists_forall_iff_forall_tuple
        (fun i (z2 : Fin (Auditable.nPrime n) → Bool) =>
          ((Auditable.Interface.fPrime F).eval z2 = true ∧ z2 ≠ z1) →
            (K.hstock i).apply z2 ≠ (K.hstock i).apply z1)).mpr key
      exact ⟨i, fun z2 hGz2 hne => hi z2 ⟨hGz2, hne⟩⟩
    · intro α
      obtain ⟨y, -, hBigR⟩ := hBig (Auditable.Program.assemble (fun _ => false) (fun _ _ => false) α)
      obtain ⟨i, -, hGy, hi⟩ := hBigR
      refine ⟨y, hGy, i, ?_⟩
      funext j
      have := hi j
      simpa [Auditable.Program.assemble_alpha] using this
  · rintro ⟨hpos, hneg⟩ x
    obtain ⟨z, hGz, i, hi⟩ := hneg (fun t => x (Fin.natAdd (Auditable.nPrime n + K.chigh * Auditable.nPrime n) t))
    refine ⟨z, ?_, ?_⟩
    · by_cases hz1 : (Auditable.Interface.fPrime F).eval
          (fun v => x (Fin.castAdd K.clow (Fin.castAdd (K.chigh * Auditable.nPrime n) v))) = true
      · obtain ⟨j, hj⟩ := hpos _ hz1
        refine Or.inr ⟨j, List.mem_finRange j, ?_⟩
        by_cases hcase : (Auditable.Interface.fPrime F).eval
            (fun v => x (Fin.castAdd K.clow (Fin.natAdd (Auditable.nPrime n) (finProdFinEquiv (j, v))))) = true ∧
          (fun v => x (Fin.castAdd K.clow (Fin.natAdd (Auditable.nPrime n) (finProdFinEquiv (j, v))))) ≠
            (fun v => x (Fin.castAdd K.clow (Fin.castAdd (K.chigh * Auditable.nPrime n) v)))
        · exact Or.inr ((Auditable.Program.func_ne_iff _ _).mp (hj _ hcase.1 hcase.2))
        · refine Or.inl (fun hA => ?_)
          obtain ⟨hA1, hA2⟩ := Bool.and_eq_true_iff.mp hA
          exact hcase ⟨hA1, (Auditable.Program.func_ne_iff _ _).mpr (of_decide_eq_true hA2)⟩
      · exact Or.inl hz1
    · exact ⟨i, List.mem_finRange i, hGz, fun j => congrFun hi j⟩

/-- On any certificate, CountAuditor as a program returns the pseudocode's verdict: the merged check together with c_high − c_low ≤ 7. -/
theorem countAuditor_val_eq_verdict {n : ℕ} (F : Auditable.CNF n) (K : Auditable.Cert (Auditable.nPrime n)) : (Auditable.Program.countAuditor F K).val = Auditable.Interface.Pseudocode.verdict F K := by
  rw [Auditable.Interface.countAuditor_eq]
  rw [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_bind]
  rw [Auditable.Interface.sigma2Oracle_val, Auditable.Interface.natLe_val]
  rw [apply_ite Arlib.Computation.Charged.val, Arlib.Computation.Charged.val_pure,
    Arlib.Computation.Charged.val_pure]
  unfold Auditable.Interface.Pseudocode.verdict Auditable.Interface.Pseudocode.gapCheck
  congr 1
  rw [show (decide (Auditable.Program.auditQuery (Auditable.Interface.fPrime F) K).holds &&
      decide (K.chigh ≤ K.clow + 7)) = decide ((Auditable.Program.auditQuery (Auditable.Interface.fPrime F) K).holds ∧
      K.chigh ≤ K.clow + 7) from by simp]
  simp [Auditable.auditQuery_holds_iff_mergedCheck]

/-- The top bridge: auditing AFCounter's actual output runs the pseudocode's verdict on the pseudocode's result. The audit-complexity analysis rewrites through this rung. -/
theorem countAuditor_afCounter_val_eq_verdict_result {n : ℕ} (F : Auditable.CNF n) : (Auditable.Program.countAuditor F (Auditable.Program.afCounter F).val).val = Auditable.Interface.Pseudocode.verdict F (Auditable.Interface.Pseudocode.result F) := by
  rw [Auditable.afCounter_val_eq_result]
  exact Auditable.countAuditor_val_eq_verdict F (Auditable.Interface.Pseudocode.result F)

end Auditable
