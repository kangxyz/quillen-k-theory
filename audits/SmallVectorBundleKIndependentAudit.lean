import Lean.Util.CollectAxioms
import Quillen.Scheme.Comparison.SmallVectorBundleK
import Quillen.PerfectComplexes.KTheory

open Lean in
run_cmd do
  let env ← getEnv
  let modules := #[`Quillen.KTheory.Map.CommonAmbient,
    `Quillen.Scheme.Comparison.SmallVectorBundleK]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless modules.contains origin do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  unless count = 34 do throwError "Expected frozen 34-declaration scope; audited {count}"
  logInfo m!"Audited all {count} declarations from the common-ambient and small-vector-bundle bridge modules."

#print axioms Quillen.ExactFunctor.commonAmbientKEquiv
#print axioms Quillen.SchemeSheaf.smallVectorBundleKEquiv

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] Abelian.hasFiniteBiproducts

example (X : Scheme.{u}) : Category.{u} (Quillen.SchemeSheaf.FiniteLocallyFree X) := inferInstance
example (X : Scheme.{u}) : Category.{u + 1} (Quillen.SchemeSheaf.SmallVectorBundle X) := inferInstance
example (X : Scheme.{u}) : Category.{u + 1}
    (Quillen.SchemeSheaf.vectorBundleExactStructure X).QCategory := inferInstance
example (X : Scheme.{u}) : Category.{u + 1}
    (Quillen.SchemeSheaf.smallVectorBundleExactStructure X).QCategory := inferInstance
example (X : Scheme.{u}) : TopCat.{u + 1} :=
  (Quillen.SchemeSheaf.vectorBundleExactStructure X).KSpace
example (X : Scheme.{u}) : TopCat.{u + 1} :=
  (Quillen.SchemeSheaf.smallVectorBundleExactStructure X).KSpace
example (X : Scheme.{u}) (n : ℕ) : Quillen.Scheme.K X n ≃*
    (Quillen.SchemeSheaf.vectorBundleExactStructure X).K n :=
  Quillen.SchemeSheaf.smallVectorBundleKEquiv X n
example (X : Scheme.{u}) (n : ℕ) : Type (u + 1) := Quillen.PerfectComplexes.PerfectK X n

namespace Quillen.ExactFunctor
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D}
example (F : ExactFunctor EC ED) (n : ℕ) : F.commonAmbientKMap n = F.KMap n := rfl
end Quillen.ExactFunctor

namespace IndependentModelConsumer
open Quillen
example (X : Scheme.{u}) (n : ℕ) :
    (SchemeSheaf.smallVectorBundleKEquiv X n).toMonoidHom =
      SchemeSheaf.smallVectorBundleKMap X n := rfl
example (X : Scheme.{u}) :
    (SchemeSheaf.smallVectorBundleToOriginal X).mapQ.IsEquivalence := inferInstance
example (X : Scheme.{u}) (n : ℕ) :
    Function.Bijective (SchemeSheaf.smallVectorBundleKMap X n) :=
  (SchemeSheaf.smallVectorBundleKEquiv X n).bijective
example (X : Scheme.{u}) (n : ℕ) :
    SchemeSheaf.smallVectorBundleKMap X n = piMap n
      (classifyingSpaceMap
        (SchemeSheaf.smallVectorBundleToOriginal X).commonAmbientNormalizedQ).hom
      (SchemeSheaf.smallVectorBundleToOriginal X).commonAmbientNormalizedQ_map_point := rfl
end IndependentModelConsumer
