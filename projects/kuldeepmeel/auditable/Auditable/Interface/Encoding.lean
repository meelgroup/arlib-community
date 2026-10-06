import Auditable.Model.Program

/-!
# Interface encoding: the specification's handles on `AFCounter` and `CountAuditor`

This file holds only definitions and `rfl` lemmas. Nothing here is a claim about
either algorithm, and no headline statement mentions anything here. The bridge
that proves the programs compute the pseudocode answers below is
`Interface/ProgramModel.lean`, which is a later pass.

## The three jobs

* **Class indirection.** There is none to collapse. `Model/Program.lean` is
  written directly in the project-local currency `Charged Op Cell` of
  `Model/Operations.lean`, because arlib has no QBF oracle. It goes through no
  arlib operation class (`RosterOps`, `RandOps`, `SlotOps`), and
  `Operations.Cell` is an `abbrev` for `Arlib.Computation.Cell`. What a proof does
  meet is the four charged wrappers. The lemmas `holesOracle_val`,
  `stockOracle_val`, `sigma2Oracle_val` and `natLe_val` read off their values. Their
  costs stay on the program side and are not restated here.
* **Views of a run.** The only seal is `Charged` itself, which the noncomputable
  `Charged.val` reads. `holesLoop` (AFC-4..10) and `stockLoop` (AFC-11..17) name the
  two loops of `afCounter`. `stockHigh` names the stock register after its default
  (Deviation 2 of `Model/Program.lean`) is applied. `afCounter_val` expresses the
  counter's certificate in terms of these. `countAuditor_eq` opens the auditor's
  run onto `fPrime`. Its verdict is an open `if` that `Charged.val` cannot pass
  through by `rfl`.
* **Handles on `Model/` subterms.** `fPrime` is `F' = MakeCopies(F, log n)` (AFC-2).
  `holesAnswer` and `stockAnswer` are the two oracles' answers. `stockDefault` is
  the stock loop's default register.

## The pseudocode-side answers (restatement `algorithmTranscript`)

`afCounterSpec F` is the answer of Algorithm algo:pigeons read as pseudocode. It
uses `List.find?` over the loop range, *not* the program's register fold:

| step | `afCounterSpec` |
|---|---|
| AFC-1 `c_low ← 0; c_high ← n'; n' ← n log n` | `nPrime n`; the `none` branches of `holesSpec` and `stockSpec` |
| AFC-2 `F' ← MakeCopies(F, log n)` | `fPrime F` |
| AFC-4..10 first `m ∈ [1, n']` with `3QBFCheck(φ_holes(m))` false, then `c_low = m − 1` | `holesSpec`: the `find?` of a `none` answer, index `m − 1` with the answer at `m − 1` |
| (no failure) | `holesSpec`: index `n'` with the answer at `n'` (Deviation 1, `c_low := n'`) |
| AFC-11..17 first `m' ∈ [1, n']` with `2QBFCheck(φ_stock(m'))` true, `c_high = m'` | `stockSpec`: the `find?` of a `some` answer, with that answer |
| (no success) | `stockSpec`: `stockDefault` (Deviation 2, `c_high = n'` with identity hashes) |
| AFC-18 `CntEst ← 2^{c_high / log n}` | not here: `estimate` in `Model/Prelude.lean` |
| AFC-19 `return (…)` | the `Cert` built by `afCounterSpec` |

The witness fields fall back to `zeroHash` only where `find?` itself guarantees
the answer is `some`. The one exception is index `0`, where the program uses
`emptyHolesReg` and the hash type `AffHash N 0` has exactly one member. So the
fallback is never what the honest run reads. Proving that is the bridge's job.

`countAuditorSpec F K` is Algorithm algo:lonely-audit read semantically:
AUD-2 is `stockWith`, AUD-3 is `holesWith` with all `c_low + 1` hashes (Deviation 4),
and AUD-4 is the gap test. It does *not* mention the syntactic query
`auditQuery`. The equivalence `(auditQuery (fPrime F) K).holds ↔ stockWith … ∧ holesWith …`
is the encoding-correctness claim that the merged `Σ₂ᴾ` query (AUD-merged) stands for.
It belongs to `Interface/ProgramModel.lean`.

Neither spec counts anything. Oracle calls and query variables stay on the program
side (`Charged.cost` of `Program.afCounter` / `Program.countAuditor`).

No mismatch was found between the restatement's `algorithmTranscript` and
`Model/Program.lean`. The program's five disclosed deviations (in its docstring)
are the transcript's `omissionsOrChoices`, and the specs above follow them.
-/

set_option autoImplicit false

namespace Auditable.Interface

open Arlib.Computation (Charged)
open Auditable.Model.Operations
open Auditable.Program

/-! ## Values of the charged wrappers -/

/-- The answer of `3QBFCheck(φ_holes^G(m))`: the first tuple in the enumeration of
the hash family that witnesses `holesWith G m`, if one exists. -/
noncomputable def holesAnswer {N : ℕ} (G : CNF N) (m : ℕ) :
    Option (Fin (m + 1) → AffHash N m) :=
  (allHashTuples (m + 1) N m).find? fun hs => decide (holesWith G m hs)

/-- The answer of `2QBFCheck(φ_stock^G(m))`: the first tuple in the enumeration of
the hash family that witnesses `stockWith G m`, if one exists. -/
noncomputable def stockAnswer {N : ℕ} (G : CNF N) (m : ℕ) : Option (Fin m → AffHash N m) :=
  (allHashTuples m N m).find? fun hs => decide (stockWith G m hs)

@[simp] theorem holesOracle_val {N : ℕ} (G : CNF N) (m : ℕ) :
    (holesOracle G m).val = holesAnswer G m := rfl

@[simp] theorem stockOracle_val {N : ℕ} (G : CNF N) (m : ℕ) :
    (stockOracle G m).val = stockAnswer G m := rfl

@[simp] theorem sigma2Oracle_val (q : Pi2Query) : (sigma2Oracle q).val = decide q.holds := rfl

@[simp] theorem natLe_val (a b : ℕ) : (natLe a b).val = decide (a ≤ b) := rfl

/-! ## Handles on the subterms of `Program.afCounter` -/

/-- AFC-2: `F' = MakeCopies(F, log n)`, a CNF over `n' = nPrime n` variables. -/
def fPrime {n : ℕ} (F : CNF n) : CNF (nPrime n) := makeCopies F (copies n)

/-- AFC-4..10: the holes loop over `m ∈ [1, N]`, stopping at the first failure. -/
def holesLoop {N : ℕ} (G : CNF N) : Charged Op Cell (HolesReg N) :=
  Charged.foldlWhile (holesStep G) (List.range' 1 N) (emptyHolesReg N)

/-- AFC-11..17: the stock loop over `m' ∈ [1, N]`, which records the first success. -/
def stockLoop {N : ℕ} (G : CNF N) : Charged Op Cell (StockReg N) :=
  Charged.foldlWhile (stockStep G) (List.range' 1 N) none

/-- The stock register's unreachable default (Deviation 2): `c_high = N` with `N`
identity hashes. -/
def stockDefault (N : ℕ) : Σ m : ℕ, (Fin m → AffHash N m) :=
  ⟨N, fun _ => identityHash N⟩

/-- `(c_high, hashassgn_stock)` after the stock loop of a run, with the default applied. -/
noncomputable def stockHigh {N : ℕ} (G : CNF N) : Σ m : ℕ, (Fin m → AffHash N m) :=
  (stockLoop G).val.getD (stockDefault N)

/-- **The certificate a run of `AFCounter` returns**, as a view of its two loops. -/
@[simp] theorem afCounter_val {n : ℕ} (F : CNF n) :
    (afCounter F).val =
      { clow := (holesLoop (fPrime F)).val.1, chigh := (stockHigh (fPrime F)).1,
        hstock := (stockHigh (fPrime F)).2, hholes := (holesLoop (fPrime F)).val.2 } := rfl

/-- A stock round after a success is the `break` of AFC-16. -/
@[simp] theorem stockStep_some {N : ℕ} (G : CNF N) (w : Σ m : ℕ, (Fin m → AffHash N m))
    (m : ℕ) : stockStep G (some w) m = pure none := rfl

/-- **A run of `CountAuditor`**: the one `Σ₂ᴾ` call on the merged query about `F'`,
the gap test, then the verdict. The value does not reduce further by `rfl`, because
`Charged.val` does not pass through the open `if`.
`rw [countAuditor_eq]; simp [apply_ite Arlib.Computation.Charged.val]` turns
`(countAuditor F K).val = .verified` into `(auditQuery (fPrime F) K).holds ∧ K.chigh ≤ K.clow + 7`. -/
theorem countAuditor_eq {n : ℕ} (F : CNF n) (K : Cert (nPrime n)) :
    countAuditor F K =
      sigma2Oracle (auditQuery (fPrime F) K) >>= fun answer =>
        natLe K.chigh (K.clow + 7) >>= fun gapOk =>
          if answer && gapOk then pure Verdict.verified else pure Verdict.rejected := rfl

/-! ## The pseudocode-side answers -/

/-- An arbitrary member of `AffHash N m` (the zero map). It is used only as a fallback
that the honest run never reads. -/
def zeroHash (N m : ℕ) : AffHash N m := ⟨fun _ _ => false, fun _ => false⟩

/-- AFC-4..10 as pseudocode: `c_low = m − 1` for the first `m ∈ [1, N]` whose
`φ_holes` check fails, or `c_low = N` if none fails, with the witness found at `c_low`. -/
noncomputable def holesSpec {N : ℕ} (G : CNF N) : HolesReg N :=
  match (List.range' 1 N).find? (fun m => (holesAnswer G m).isNone) with
  | some m => ⟨m - 1, (holesAnswer G (m - 1)).getD fun _ => zeroHash N (m - 1)⟩
  | none => ⟨N, (holesAnswer G N).getD fun _ => zeroHash N N⟩

/-- AFC-11..17 as pseudocode: `c_high` is the first `m' ∈ [1, N]` whose `φ_stock` check
succeeds, with its witness. If none succeeds, it is `stockDefault N`. -/
noncomputable def stockSpec {N : ℕ} (G : CNF N) : Σ m : ℕ, (Fin m → AffHash N m) :=
  match (List.range' 1 N).find? (fun m => (stockAnswer G m).isSome) with
  | some m => ⟨m, (stockAnswer G m).getD fun _ => zeroHash N m⟩
  | none => stockDefault N

/-- **What Algorithm algo:pigeons answers**, as pseudocode (combined.tex:23-52, with
the disclosed deviations of `Model/Program.lean`). -/
noncomputable def afCounterSpec {n : ℕ} (F : CNF n) : Cert (nPrime n) :=
  { clow := (holesSpec (fPrime F)).1, chigh := (stockSpec (fPrime F)).1,
    hstock := (stockSpec (fPrime F)).2, hholes := (holesSpec (fPrime F)).2 }

/-- **What Algorithm algo:lonely-audit answers**, read semantically (finalaudit.tex:17-29):
`Verified` iff `φ_stock^{F'}(c_high)` holds with `hashassgn_stock` substituted
(isolation semantics), `φ_holes^{F'}(c_low)` holds with all `c_low + 1` holes hashes
substituted, and `c_high − c_low ≤ 7`. -/
noncomputable def countAuditorSpec {n : ℕ} (F : CNF n) (K : Cert (nPrime n)) : Verdict :=
  if stockWith (fPrime F) K.chigh K.hstock ∧ holesWith (fPrime F) K.clow K.hholes ∧
      K.chigh ≤ K.clow + 7
  then Verdict.verified else Verdict.rejected

end Auditable.Interface
