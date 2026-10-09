import Quillen.Waldhausen.QuillenComparison.Functoriality
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let target := `Quillen.Waldhausen.QuillenComparison.Functoriality
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[index.toNat]! == target do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {name}: {axioms}"
  unless count = 11 do throwError "Expected frozen 11-declaration scope; audited {count}"
  logInfo m!"Audited all {count} Functoriality declaration origins."

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u v
namespace Quillen.Waldhausen.QuillenComparison
variable {C D T : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} T]
  [Preadditive C] [Preadditive D] [Preadditive T]
  [HasFiniteBiproducts C] [HasFiniteBiproducts D] [HasFiniteBiproducts T]
  {EC : Quillen.ExactStructure C} {ED : Quillen.ExactStructure D} {ET : Quillen.ExactStructure T}
  (F : Quillen.ExactFunctor EC ED) (G : Quillen.ExactFunctor ED ET)
example (n : SimplexCategoryᵒᵖ)
    (A : (sSet EC.inflation (MorphismProperty.isomorphisms C)).obj n) :
    ((exactSSetMap F).app n A).1 = A.1 ⋙ F.toFunctor := rfl
example : exactSSetMap (Quillen.ExactFunctor.id EC) = 𝟙 _ := exactSSetMap_id EC
example : exactSSetMap (F.comp G) = exactSSetMap F ≫ exactSSetMap G := exactSSetMap_comp F G
example (hF : IsExact EC.inflation (MorphismProperty.isomorphisms C)
    ED.inflation (MorphismProperty.isomorphisms D) F.toFunctor) :
    exactSSetMap F = sSetMap hF := exactSSetMap_eq_sSetMap F hF
example : Edgewise.subdivisionFunctor.map (exactSSetMap F) ≫ comparisonMap ED =
    comparisonMap EC ≫ CategoryTheory.nerveMap F.mapQ := comparisonMap_naturality F
end Quillen.Waldhausen.QuillenComparison
