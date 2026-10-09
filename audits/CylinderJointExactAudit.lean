import Quillen.Waldhausen.Cylinder.JointExact
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.Cylinder.SubcategoryPreservation,
    `Quillen.Waldhausen.Cylinder.JointFunctor, `Quillen.Waldhausen.Cylinder.JointExact]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless targets.contains origin do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {name}: {axioms}"
  unless count == 21 do throwError "Expected 21 joint-cylinder origins, got {count}"
  logInfo m!"Audited all {count} joint-cylinder exactness origins."
noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex Quillen Quillen.Waldhausen SplitFactorization
universe u v
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L → ∀ f : K ⟶ L, P (mappingCone f))
  (hshift : ∀ K, P K → P (K⟦(1 : ℤ)⟧))
example : IsExact (ArrowCategory.waldhausenStructure (complexSubcategory P)).cof
    (ArrowCategory.waldhausenStructure (complexSubcategory P)).weq
    (ExtensionCategory.waldhausenStructure (complexSubcategory P)).cof
    (ExtensionCategory.waldhausenStructure (complexSubcategory P)).weq
    (subcategoryJointFunctor P hcone hshift) := subcategoryJointFunctor_quasiExact P hcone hshift
example : let W := ofExactCategory (ExactSubcategory.exactStructure
      (abelianExactStructure (CochainComplex A ℤ)) P)
    IsExact (ArrowCategory.waldhausenStructure W).cof (ArrowCategory.waldhausenStructure W).weq
      (ExtensionCategory.waldhausenStructure W).cof (ExtensionCategory.waldhausenStructure W).weq
      (subcategoryJointFunctor P hcone hshift) := subcategoryJointFunctor_isoExact P hcone hshift
example (f : Arrow P.FullSubcategory) :
    (((subcategoryJointFunctor P hcone hshift).obj f).obj.hom).hom = jointInclusion f.hom.hom := rfl
example {f g : Arrow P.FullSubcategory} (α : f ⟶ g) :
    (((subcategoryJointFunctor P hcone hshift).map α).hom.right).hom =
      middleFunctor.map (P.ι.mapArrow.map α) := rfl
example {f g : Arrow P.FullSubcategory} (α : f ⟶ g)
    (hα : (complexSubcategory P).cof α.left ∧ (complexSubcategory P).cof α.right) :
    ExtensionCategory.cof (complexSubcategory P) ((subcategoryJointFunctor P hcone hshift).map α) :=
  (subcategoryJointFunctor_quasiExact P hcone hshift).cofibration α hα
example {f g : Arrow P.FullSubcategory} (α : f ⟶ g)
    (hα : (complexSubcategory P).weq α.right) :
    (complexSubcategory P).weq ((subcategoryMiddleFunctor P hcone).map α) :=
  subcategoryMiddleFunctor_map_weak P hcone α hα
