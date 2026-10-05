/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Machine-checks the audit surface: the statement of the headline theorem must
unfold only to constants defined under `ArlibCommunity.Algorithms.CV18/Model/`.

This is tooling, hence proof content, hence deliberately *outside* the surface
it checks.

Seeding from a theorem's **type** rather than its value is the crux: the proof
may use anything, and routinely should. Only the statement is constrained.
-/
import Lean

open Lean Elab Command

namespace ArlibCommunity.Algorithms.CV18.Meta

/-- All `ArlibCommunity.Algorithms.CV18` constants reachable from a seed, through both types and values. -/
private partial def closureAux (env : Environment) :
    NameSet → List Name → NameSet → NameSet
  | _, [], acc => acc
  | seen, c :: rest, acc =>
    if seen.contains c then closureAux env seen rest acc
    else
      let seen := seen.insert c
      let acc := if (`ArlibCommunity.Algorithms.CV18).isPrefixOf c then acc.insert c else acc
      match env.find? c with
      | none => closureAux env seen rest acc
      | some ci =>
        let next := ci.type.getUsedConstants.toList
          ++ (match ci.value? with | some v => v.getUsedConstants.toList | none => [])
        closureAux env seen (next ++ rest) acc

/-- Which module defines a constant.

    `getModuleIdxFor?` is the only route in current Lean: `getModuleFor?` was
    removed, and an index has to be looked up in the header's module table. A
    constant with no index is not imported at all — it belongs to the module
    being elaborated right now. -/
private def moduleOf (env : Environment) (c : Name) : Name :=
  match env.getModuleIdxFor? c with
  | some idx => (env.allImportedModuleNames[idx.toNat]?).getD `«unknown»
  | none => env.mainModule

/-- Constants not defined under `ArlibCommunity.Algorithms.CV18/Model/`, paired with the module defining them. -/
private def outsideModel (env : Environment) (cls : NameSet) : List (Name × Name) :=
  cls.toList.filterMap fun c =>
    let mod := moduleOf env c
    if (`ArlibCommunity.Algorithms.CV18.Model).isPrefixOf mod then none else some (c, mod)

/-- Seeded from a definition's own body — use this on the algorithm. -/
elab "#modelClosure " id:ident : command => do
  let env ← getEnv
  let n ← liftCoreM <| Lean.realizeGlobalConstNoOverload id
  let cls := (closureAux env {} [n] {}).erase n
  match outsideModel env cls with
  | [] => logInfo m!"OK — closure of {n} is defined entirely under Model/ ({cls.toList.length})"
  | bad => throwError m!"OUTSIDE Model/ in closure of {n}: {bad}"

/-- Seeded from a theorem's *type*, so the statement — not the proof — unfolds. -/
elab "#modelClosureOfType " id:ident : command => do
  let env ← getEnv
  let some ci := env.find? (← liftCoreM <| Lean.realizeGlobalConstNoOverload id)
    | throwError "unknown constant"
  let cls := closureAux env {} ci.type.getUsedConstants.toList {}
  match outsideModel env cls with
  | [] => logInfo m!"OK — the STATEMENT is defined entirely under Model/ ({cls.toList.length})"
  | bad => throwError m!"OUTSIDE Model/ in the statement: {bad}"

end ArlibCommunity.Algorithms.CV18.Meta
