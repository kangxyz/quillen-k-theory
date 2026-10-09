import Quillen.Waldhausen.QuillenComparison.BasedNaturality
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.QuillenComparison.ZeroNormalization,
    `Quillen.Waldhausen.QuillenComparison.BasedNaturality]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless targets.contains origin do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  unless count = 45 do throwError "Expected frozen 45-declaration scope; audited {count}"
  logInfo m!"Audited all {count} based Q/S naturality declaration origins."

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial ZeroObject
universe u v
namespace Quillen.Waldhausen.QuillenComparison
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {EC : Quillen.ExactStructure C} {ED : Quillen.ExactStructure D}
  (F : Quillen.ExactFunctor EC ED)
example : Quillen.ExactFunctor EC ED := F.zeroNormalized
example : F.zeroNormalized.toFunctor.obj (0 : C) = (0 : D) := F.zeroNormalized_obj_zero
example (n : ℕ) : F.zeroNormalized.KMap n = F.KMap n := F.zeroNormalized_KMap n
example (h : F.toFunctor.obj (0 : C) = (0 : D)) (n : ℕ) :
    (comparisonKEquiv ED n).toMonoidHom.comp (exactSKMapOfZeroEq F h n) =
      (F.KMap n).comp (comparisonKEquiv EC n).toMonoidHom :=
  comparisonKEquiv_naturality_of_zeroEq F h n
example (n : ℕ) : normalizedExactSKMap F n =
    piMap n (SSet.toTop.map (exactSSetMap F.zeroNormalized)).hom
      (exactSSetMap_basepoint_of_zeroEq F.zeroNormalized F.zeroNormalized_obj_zero) := rfl
example (n : ℕ) :
    (comparisonKEquiv ED n).toMonoidHom.comp (normalizedExactSKMap F n) =
      (F.KMap n).comp (comparisonKEquiv EC n).toMonoidHom := comparisonKEquiv_naturality F n
example (hF : IsExact (ofExactCategory EC).cof (ofExactCategory EC).weq
    (ofExactCategory ED).cof (ofExactCategory ED).weq F.toFunctor) (n : ℕ) :
    normalizedExactSKMap F n = Waldhausen.KMap hF n := normalizedExactSKMap_eq_KMap F hF n
example (hF : IsExact (ofExactCategory EC).cof (ofExactCategory EC).weq
    (ofExactCategory ED).cof (ofExactCategory ED).weq F.toFunctor) (n : ℕ) :
    (comparisonKEquiv ED n).toMonoidHom.comp (Waldhausen.KMap hF n) =
      (F.KMap n).comp (comparisonKEquiv EC n).toMonoidHom := comparisonKEquiv_naturality_KMap F hF n
end Quillen.Waldhausen.QuillenComparison
