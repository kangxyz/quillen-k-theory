import Quillen.Topology.Realization.ClassificationHomotopy
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let modules := #[`Quillen.Topology.Realization.Classification,
    `Quillen.Topology.Realization.ClassificationHomotopy]
  let mut total : Nat := 0
  let mut counts : NameMap Nat := {}
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless modules.contains origin do continue
    total := total + 1
    counts := counts.insert origin ((counts.find? origin).getD 0 + 1)
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  for origin in modules do
    let count := (counts.find? origin).getD 0
    unless count > 0 do throwError "No declarations from required origin {origin}"
    logInfo m!"MODULE {origin}: {count} declarations"
  logInfo m!"PASS: all {total} declarations in {modules.size} source modules; only standard Lean axioms."

noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open scoped Simplicial Topology

example (D : Type u) [Category.{v} D] :
    ContinuousMap.HomotopyEquiv |Quillen.Classification.sSet D| |nerve D| :=
  Quillen.Classification.realizationHomotopyEquiv D

example (D : Type u) [Category.{v} D] :
    (Quillen.Classification.realizationHomotopyEquiv D).toFun =
      (SSet.toTop.map (Quillen.Classification.evaluation D)).hom := rfl

example (D : Type u) [Category.{v} D] :
    SSet.Homotopy (𝟙 (Quillen.Classification.sSet D))
      (Quillen.Classification.evaluation D ≫ Quillen.Classification.constant D) :=
  Quillen.Classification.homotopy D

example (D : Type u) [Category.{v} D] (x : (nerve D) _⦋0⦌) (t : unitInterval) :
    Quillen.realizationSimplicialHomotopy (Quillen.Classification.homotopy D)
      (t, Quillen.realizationPoint ((Quillen.Classification.constant D).app _ x)) =
        Quillen.realizationPoint ((Quillen.Classification.constant D).app _ x) :=
  Quillen.Classification.realizationHomotopy_fixed_vertex D x t

#print axioms Quillen.Classification.realizationHomotopyEquiv
#print axioms Quillen.Classification.realizationHomotopy_fixed_vertex
#check @Quillen.Classification.realizationHomotopyEquiv
