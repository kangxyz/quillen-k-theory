import Quillen.CategoryTheory.QConstruction.Core
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let origin := `Quillen.CategoryTheory.QConstruction.Core
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[index.toNat]! == origin do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {name}: {axioms}"
  unless count > 0 do throwError "No declarations audited from {origin}"
  logInfo m!"PASS: all {count} declarations from {origin}, including private/generated constants, have only standard Lean axioms."

noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits

example {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
    (E : Quillen.ExactStructure C) (X Y : C) :
    Function.Bijective (E.qIsoOfIso : (X ≅ Y) → _) := E.qIsoOfIso_bijective

example {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
    (E : Quillen.ExactStructure C) :
    Core C ≌ Core (Quillen.Q E.deflation E.inflation) := E.qCoreEquivalence

example {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
    (E : Quillen.ExactStructure C) {X Y : Core C} (f : X ⟶ Y) :
    (E.qCoreEquivalence.functor.map f).iso = E.qIsoOfIso f.iso := rfl

#print axioms Quillen.ExactStructure.qIsoOfIso_bijective
#print axioms Quillen.ExactStructure.qCoreEquivalence
#check @Quillen.ExactStructure.qSpan_isIso_legs
