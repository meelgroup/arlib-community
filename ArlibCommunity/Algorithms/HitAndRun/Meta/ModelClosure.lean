/- Machine-check that the public theorem statement closes over `Model/`. -/
import Lean

open Lean Elab Command

namespace ArlibCommunity.Algorithms.HitAndRun.Meta

private partial def closureAux (env : Environment) :
    NameSet → List Name → NameSet → NameSet
  | _, [], acc => acc
  | seen, c :: rest, acc =>
    if seen.contains c then closureAux env seen rest acc
    else
      let seen := seen.insert c
      let acc := if (`ArlibCommunity.Algorithms.HitAndRun).isPrefixOf c then acc.insert c else acc
      match env.find? c with
      | none => closureAux env seen rest acc
      | some ci =>
        let next := ci.type.getUsedConstants.toList ++
          (match ci.value? with | some v => v.getUsedConstants.toList | none => [])
        closureAux env seen (next ++ rest) acc

private def moduleOf (env : Environment) (c : Name) : Name :=
  match env.getModuleIdxFor? c with
  | some idx => (env.allImportedModuleNames[idx.toNat]?).getD `«unknown»
  | none => env.mainModule

private def outsideModel (env : Environment) (cls : NameSet) : List (Name × Name) :=
  cls.toList.filterMap fun c =>
    let mod := moduleOf env c
    if (`ArlibCommunity.Algorithms.HitAndRun.Model).isPrefixOf mod then none else some (c, mod)

elab "#modelClosureOfType " id:ident : command => do
  let env ← getEnv
  let some ci := env.find? (← liftCoreM <| Lean.realizeGlobalConstNoOverload id)
    | throwError "unknown constant"
  let cls := closureAux env {} ci.type.getUsedConstants.toList {}
  match outsideModel env cls with
  | [] => logInfo m!"OK — the statement is defined entirely under HitAndRun/Model ({cls.toList.length})"
  | bad => throwError m!"OUTSIDE HitAndRun/Model in the statement: {bad}"

end ArlibCommunity.Algorithms.HitAndRun.Meta
