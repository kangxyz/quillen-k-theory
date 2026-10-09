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
  unless count == 11 do throwError "Expected exactly 11 inherited-cylinder origins, got {count}"
  logInfo m!"Independently audited all {count} inherited cylinder declaration origins, including generated/private declarations."

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

-- Ordinary inherited pushouts suffice; their ambient universal property is derived.
example (hα : (splitComplexSubcategory P).cof α.left)
    (hp : IsPushout (subcategoryJointInclusion P hcone f)
      (P.homMk (biprod.map α.left.hom α.right.hom) :
        subcategoryJointSource P f ⟶ subcategoryJointSource P g) i j) :
    (splitComplexSubcategory P).cof k := by
  have hp' := fullSubcategory_map_pushout
    (abelianExactStructure (CochainComplex A ℤ)) P
    (subcategoryJointInclusion_cof P hcone hshift f).1 hp
  exact subcategoryRelativeJoint_cof P hcone hshift α i j hp' k hi hj hα

section MinimalCokernel
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (Q : ObjectProperty C)
  [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms] [E.IsExtensionClosed Q]
  [Q.IsClosedUnderFiniteProducts]

-- No abelian hypothesis, global cokernel existence, or arbitrary quotient closure.
example {X Y : Q.FullSubcategory} (f : X ⟶ Y) [HasCokernel f.hom]
    (hf : (ExactSubcategory.exactStructure E Q).inflation f) : Q (cokernel f.hom) :=
  ExactSubcategory.cokernel_mem_of_inflation E Q f hf
end MinimalCokernel
