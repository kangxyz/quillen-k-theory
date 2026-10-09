import Quillen.Waldhausen.QuillenComparison.ReconstructedSpan
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let origin := `Quillen.Waldhausen.QuillenComparison.ReconstructedSpan
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
open scoped Simplicial
open Quillen.Waldhausen.QuillenComparison

example {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
    (E : Quillen.ExactStructure C) {n : ℕ} (F : Row E (Quillen.Edgewise.ε.obj ⦋n⦌))
    {P Z : C} (p : P ⟶ (initialFlag E F).obj (Fin.last (Quillen.Edgewise.ε.obj ⦋n⦌).len))
    (hp : E.deflation p) (r : P ⟶ Z) (hr : E.inflation r) :
    (reconstructedRow E F p hp r hr).diagram.obj
        (nestedToInterval (centralInterval ⦋n + 1⦌ (Fin.last (n + 1)))) ≅ Z :=
  reconstructedTopIso E F p hp r hr

#print axioms Quillen.Waldhausen.QuillenComparison.reconstructedRow_last_step
#print axioms Quillen.Waldhausen.QuillenComparison.reconstructedCentralIsoAt_last_top
#check @Quillen.Waldhausen.QuillenComparison.reconstructedRow_last_step
