import Quillen.Waldhausen.QuillenComparison.FlagExtension
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let modules := #[`Quillen.Waldhausen.QuillenComparison.FlagPullback,
    `Quillen.Waldhausen.QuillenComparison.FlagExtension]
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
open CategoryTheory CategoryTheory.Limits ZeroObject
open Quillen.Waldhausen.QuillenComparison

example {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
    (E : Quillen.ExactStructure C) {n : ℕ} (A : Fin (n + 1) ⥤ C)
    {P Z : C} (p : P ⟶ A.obj (Fin.last n)) (hp : E.deflation p)
    (r : P ⟶ Z) (hr : E.inflation r)
    (hA : ∀ {i j} (f : i ⟶ j), E.inflation (A.map f)) :
    ∃ B : Fin (n + 1 + 1 + 1) ⥤ C,
      B.obj 0 = (0 : C) ∧ B.obj (Fin.last (n + 1 + 1)) = Z ∧
      ∀ {i j} (f : i ⟶ j), E.inflation (B.map f) :=
  ⟨extendedPullbackFlag E A p hp r, extendedPullbackFlag_obj_zero E A p hp r,
    extendedPullbackFlag_obj_last E A p hp r,
    extendedPullbackFlag_inflation E A p hp r hA hr⟩

#print axioms Quillen.Waldhausen.QuillenComparison.extendedPullbackFlag_inflation
#print axioms Quillen.Waldhausen.QuillenComparison.pullbackFlagInitialKernel
#check @Quillen.Waldhausen.QuillenComparison.extendedPullbackFlag
#check @Quillen.Waldhausen.QuillenComparison.extendedPullbackFlagMiddleIso
#check @Quillen.Waldhausen.QuillenComparison.extendedPullbackFlag_middle_to_last
