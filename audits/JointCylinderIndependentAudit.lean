import Quillen.Waldhausen.Cylinder.JointExact
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let wanted := #[`Quillen.Waldhausen.Cylinder.SubcategoryPreservation,
    `Quillen.Waldhausen.Cylinder.JointFunctor, `Quillen.Waldhausen.Cylinder.JointExact]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless wanted.contains origin do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  unless count == 21 do throwError "Expected 21 joint-cylinder origins, got {count}"
  logInfo m!"Audited all {count} joint-cylinder declaration origins."

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open Quillen Quillen.Waldhausen Quillen.Waldhausen.SplitFactorization
universe u v
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L → ∀ f : K ⟶ L, P (mappingCone f))
  (hshift : ∀ K, P K → P (K⟦(1 : ℤ)⟧))

-- Middle weak preservation really needs only the target quasi-isomorphism.
example {f g : Arrow P.FullSubcategory} (α : f ⟶ g) (hα : QuasiIso α.right.hom) :
    QuasiIso (((subcategoryMiddleFunctor P hcone).map α).hom) :=
  subcategoryMiddleFunctor_map_weak P hcone α hα
example {f : Arrow P.FullSubcategory} (hf : IsZero f) :
    IsZero ((subcategoryMiddleFunctor P hcone).obj f) := subcategoryMiddleFunctor_zero P hcone hf
-- Exact unchanged joint-arrow object and both unchanged components.
example (f : Arrow P.FullSubcategory) :
    ((subcategoryJointFunctor P hcone hshift).obj f).obj.hom = subcategoryJointInclusion P hcone f := rfl
example (f : Arrow P.FullSubcategory) :
    ((subcategoryJointFunctor P hcone hshift).obj f).obj.hom.hom = jointInclusion f.hom.hom := rfl
example {f g : Arrow P.FullSubcategory} (α : f ⟶ g) :
    (((subcategoryJointFunctor P hcone hshift).map α).hom.left).hom =
      biprod.map α.left.hom α.right.hom := rfl
example {f g : Arrow P.FullSubcategory} (α : f ⟶ g) :
    ((subcategoryJointFunctor P hcone hshift).map α).hom.right =
      (subcategoryMiddleFunctor P hcone).map α := rfl
example : subcategoryJointFunctor P hcone hshift ⋙ ExtensionCategory.source (complexSubcategory P) =
    subcategoryJointSourceFunctor P := rfl
example : subcategoryJointFunctor P hcone hshift ⋙ ExtensionCategory.middle (complexSubcategory P) =
    subcategoryMiddleFunctor P hcone := rfl
-- No source-sum admissibility or Reedy conclusion is supplied here.
example {f g : Arrow P.FullSubcategory} (α : f ⟶ g)
    (hL : subcategoryCofibrations P α.left) (hR : subcategoryCofibrations P α.right) :
    ExtensionCategory.cof (complexSubcategory P) ((subcategoryJointFunctor P hcone hshift).map α) :=
  (subcategoryJointFunctor_quasiExact P hcone hshift).cofibration α ⟨hL, hR⟩
example :
    IsExact (ArrowCategory.waldhausenStructure (complexSubcategory P)).cof
      (ArrowCategory.waldhausenStructure (complexSubcategory P)).weq
      (ExtensionCategory.waldhausenStructure (complexSubcategory P)).cof
      (ExtensionCategory.waldhausenStructure (complexSubcategory P)).weq
      (subcategoryJointFunctor P hcone hshift) := subcategoryJointFunctor_quasiExact P hcone hshift
example :
    let W := ofExactCategory (ExactSubcategory.exactStructure
      (abelianExactStructure (CochainComplex A ℤ)) P)
    IsExact (ArrowCategory.waldhausenStructure W).cof (ArrowCategory.waldhausenStructure W).weq
      (ExtensionCategory.waldhausenStructure W).cof (ExtensionCategory.waldhausenStructure W).weq
      (subcategoryJointFunctor P hcone hshift) := subcategoryJointFunctor_isoExact P hcone hshift
-- Every actual displayed pointwise-cofibration pushout is preserved as displayed.
example {K L M N : Arrow P.FullSubcategory} {f : K ⟶ L} {g : K ⟶ M} {i : L ⟶ N} {j : M ⟶ N}
    (hf : subcategoryCofibrations P f.left ∧ subcategoryCofibrations P f.right)
    (h : IsPushout f g i j) :
    IsPushout ((subcategoryJointFunctor P hcone hshift).map f)
      ((subcategoryJointFunctor P hcone hshift).map g)
      ((subcategoryJointFunctor P hcone hshift).map i)
      ((subcategoryJointFunctor P hcone hshift).map j) :=
  (subcategoryJointFunctor_quasiExact P hcone hshift).pushout hf h
