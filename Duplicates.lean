import Loogle.Find
import Lean

open Lean Loogle Find Meta

def printSet (n : NameSet) : String :=
  n.fold (init := "") fun s n => s ++ ", " ++ toString n

instance : ToString NameSet where
  toString := printSet

instance : ToString (RBTree Name Name.quickCmp) where
  toString s := (s.fold (init := "{") fun s n => s ++ " " ++ toString n) ++ "}"

def metaM : MetaM Unit := do
  let index ← Index.mk
  let env ← getEnv
  let (m₁, m₂) ← index.nameRelCache.get
  env.constants.map₁.forM fun name info => do
    try
      if (← Loogle.isBlackListed name) || !(← inferType info.type).isProp then
        return
      if Linter.deprecatedAttr.getParam? env name |>.isSome then
        return
      let needles := info.type.getUsedConstantsAsSet
      let hits := RBTree.intersects <| needles.toArray.map <| fun needle =>
        ((m₁.find needle).union (m₂.find needle)).insert needle
      let leftDocString ← findDocString? env name
      if leftDocString.isSome && leftDocString.get!.containsSubstr "Alias" then
        return
      for hit in hits do
        if Linter.deprecatedAttr.getParam? env hit |>.isSome then
          return
        let hitInfo := env.find? hit |>.get!
        -- TODO: `Expr.eqv`/`==` doesn't do the right thing here, as it ignores binder types
        -- `Expr.equal` is also bad because it considers binder names. We need something inbetween.
        if (Name.quickCmp name hit).isLE || !(info.type.eqv hitInfo.type) then
          continue
        let rightDocString ← findDocString? env hit
        if rightDocString.isSome && rightDocString.get!.containsSubstr "Alias" then
          continue
        IO.println s!"Hit: {name} {hit}"
      return ()
    catch
    | _ => return

def main : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env: Environment ← importModules
    (imports := #[`Init])
    (opts := {})
    (trustLevel := 1)
  let coreContext: Lean.Core.Context := {
    currNamespace := `Example
    openDecls := [],     -- No 'open' directives needed
    fileName := "<stdin>",
    fileMap := { source := "", positions := #[0] }
  }
  match ← (metaM.run'.run' coreContext { env }).toBaseIO with
  | .error exception =>
    IO.println s!"{← exception.toMessageData.toString}"
  | .ok _ => return ()
