import Quillen.Waldhausen.Fibration.RelativeRows.FiberFiltration
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels
import Quillen.PerfectComplexes.SingleComparison
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let target := `Quillen.Waldhausen.Fibration.RelativeRows.FiberFiltration
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[index.toNat]! == target do continue
    count := count + 1
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {name}: {axioms}"
  unless count == 4 do throwError "Expected4 original fiber-filtration origins, got {count}"
  logInfo m!"Audited all{count} original fiber-filtration origins."
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open Quillen.Waldhausen.Fibration.RelativeRows
open scoped Simplicial
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
section Generic
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)
example (n : SimplexCategory) : fiber N n ⋙ initialFiltrationFunctor N n =
    Functor.const (Fin (n.len+1)) := fiber_initialFiltrationFunctor N n
example (n : SimplexCategory) (X : C) (i : Fin (n.len+1)) :
    ((initialFiltrationFunctor N n).obj ((fiber N n).obj X)).obj i = X := rfl
example (n : SimplexCategory) (X : C) {i j : Fin (n.len+1)} (f : i ⟶ j) :
    ((initialFiltrationFunctor N n).obj ((fiber N n).obj X)).map f = 𝟙 X := rfl
example (n : SimplexCategory) {X Y : C} (f : X ⟶ Y) (i : Fin (n.len+1)) :
    ((initialFiltrationFunctor N n).map ((fiber N n).map f)).app i = f := rfl
example (X : C) : ((initialFiltrationFunctor N ⦋0⦌).obj ((fiber N ⦋0⦌).obj X)).obj 0 = X := rfl
example (n : SimplexCategory) (i : Fin (n.len+1)) :
    ((initialFiltrationFunctor N n).obj ((fiber N n).obj V.zero)).obj i = V.zero := rfl
example {m n : SimplexCategory} (α : m ⟶ n) {X Y : C} (f : X ⟶ Y) (i : Fin (m.len+1)) :
    (Functor.whiskerLeft (SimplexCategory.toCat.map α).toFunctor
      ((initialFiltrationFunctor N n).map ((fiber N n).map f))).app i = f := rfl
end Generic
section Scheme
attribute [local instance] Abelian.hasFiniteBiproducts
open GilletWaldhausen AlgebraicGeometry
example (X : Scheme.{u}) (n : SimplexCategory) :
    fiber (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)) n ⋙
      initialFiltrationFunctor (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)) n =
        Functor.const (Fin (n.len+1)) := fiber_initialFiltrationFunctor _ n
end Scheme
