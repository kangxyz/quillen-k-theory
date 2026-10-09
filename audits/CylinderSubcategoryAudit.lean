import Quillen.Waldhausen.Cylinder.Subcategory
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless #[`Quillen.CategoryTheory.ExactCategory.SubcategoryCokernel,
      `Quillen.Waldhausen.Cylinder.Subcategory].contains origin do continue
    count := count + 1
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}"
  unless count == 11 do
    throwError "Expected 11 inherited-cylinder origins, found {count}"
  logInfo m!"Audited all {count} inherited cylinder declaration origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex
open Quillen Quillen.Waldhausen Quillen.Waldhausen.SplitFactorization
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L →
    ∀ f : K ⟶ L, P (mappingCone f))
  (hshift : ∀ K, P K → P (K⟦(1 : ℤ)⟧))

example (f : Arrow P.FullSubcategory) :
    (subcategoryJointInclusion P hcone f).hom = jointInclusion f.hom.hom := rfl
example (f : Arrow P.FullSubcategory) :
    (subcategoryJointSource P f).obj = (f.left.obj ⊞ f.right.obj) := rfl
example (f : Arrow P.FullSubcategory) :
    (splitComplexSubcategory P).cof (subcategoryJointInclusion P hcone f) :=
  subcategoryJointInclusion_cof P hcone hshift f

variable {f g : Arrow P.FullSubcategory} (α : f ⟶ g) {R : P.FullSubcategory}
  (i : (subcategoryMiddleFunctor P hcone).obj f ⟶ R)
  (j : subcategoryJointSource P g ⟶ R)
  (h : IsPushout (jointInclusion f.hom.hom) (biprod.map α.left.hom α.right.hom) i.hom j.hom)
  (k : R ⟶ (subcategoryMiddleFunctor P hcone).obj g)
  (hi : i ≫ k = (subcategoryMiddleFunctor P hcone).map α)
  (hj : j ≫ k = subcategoryJointInclusion P hcone g)

example (hα : (splitComplexSubcategory P).cof α.left) :
    (splitComplexSubcategory P).cof k :=
  subcategoryRelativeJoint_cof P hcone hshift α i j h k hi hj hα

#check @ExactSubcategory.cokernel_mem_of_inflation
#print axioms subcategoryRelativeJoint_cof
