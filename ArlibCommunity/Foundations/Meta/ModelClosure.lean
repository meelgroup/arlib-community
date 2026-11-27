/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
# Model-closure check for the surface theorems of `Foundations`

`#foundationsModelClosure thm` checks that the statement of `thm` is readable from the audit
surface alone.  It walks every constant reachable from the statement — definitions, their bodies,
and the proofs inside those bodies — and fails if it reaches a constant of this package defined
anywhere other than

* a module with a `Model` component (`Foundations/<Area>/<Theorem>/Model/…`), or
* an area prelude (`Foundations/Convex/Prelude.lean`, `Foundations/MarkovChainTheory/Prelude.lean`).

Constants of Mathlib and Lean are not inspected.  The proof of `thm` itself is not walked: the
check is about the statement.
-/

open Lean Elab Command

namespace ArlibCommunity.Foundations.Meta

private def moduleOf (env : Environment) (c : Name) : Name :=
  match env.getModuleIdxFor? c with
  | some idx => (env.allImportedModuleNames[idx.toNat]?).getD `«unknown»
  | none => env.mainModule

private def allowedModule (m : Name) : Bool :=
  m.components.contains `Model ||
    m == `ArlibCommunity.Foundations.Convex.Prelude ||
    m == `ArlibCommunity.Foundations.MarkovChainTheory.Prelude

private partial def walk (env : Environment) :
    NameSet → List Name → Array (Name × Name) → Array (Name × Name)
  | _, [], bad => bad
  | seen, c :: rest, bad =>
    if seen.contains c then walk env seen rest bad
    else
      let seen := seen.insert c
      let m := moduleOf env c
      if !(`ArlibCommunity).isPrefixOf m then walk env seen rest bad
      else
        let bad := if allowedModule m then bad else bad.push (c, m)
        match env.find? c with
        | none => walk env seen rest bad
        | some ci =>
          let next := ci.type.getUsedConstants.toList ++
            ((ci.value? (allowOpaque := true)).map (·.getUsedConstants.toList) |>.getD [])
          walk env seen (next ++ rest) bad

/-- Fail unless every package constant reachable from the statement of the given theorem is
defined under a `Model/` directory or in an area prelude. -/
elab "#foundationsModelClosure " id:ident : command => do
  let env ← getEnv
  let c ← liftCoreM <| Lean.realizeGlobalConstNoOverload id
  let some ci := env.find? c | throwError "unknown constant"
  let bad := walk env {} ci.type.getUsedConstants.toList #[]
  if bad.isEmpty then
    logInfo m!"OK — the statement of {c} is defined entirely in Model/ and the area preludes"
  else
    throwError m!"outside Model/ and the area preludes: {bad.toList}"

end ArlibCommunity.Foundations.Meta
