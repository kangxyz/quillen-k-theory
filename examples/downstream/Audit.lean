import Consumer
import Lean.Util.CollectAxioms
/-! Audit exactly the downstream defining-origin declarations, including private
helpers. Name inventories avoid eagerly loading unrelated declaration bodies;
deduplication and the final actual-origin check preserve the original scope. -/

open Lean in
run_cmd do
  let env ← getEnv
  let selected (name : Name) : Bool :=
    match env.getModuleIdxFor? name with
    | some index => (`Consumer).isPrefixOf env.header.moduleNames[index.toNat]!
    | none => false
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if (`Consumer).isPrefixOf env.header.moduleNames[i]! then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  names := env.constants.foldStage2 (fun names name _ =>
    if selected name then names.insert name else names) names
  let mut count : Nat := 0
  for name in names.toArray do
    if selected name then
      count := count + 1
      for dependency in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} downstream declarations: only standard Lean logical foundations."
