import Quillen.Waldhausen.Fibration.Rows.SecondEndpoint
import Quillen.Waldhausen.Fibration.TrivialCofibrations.Category

/-! # Actual row cylinders as structural weak-cofibration comparison data

The data is supplied by the genuine exact joint cylinder, its proved target
section and its original projection. No comma or nerve comparison is assumed.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.Fibration
namespace RowFactorization
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (D : JointData N)

/-- Actual structural data for comparing original weak row cofibrations and weak row arrows. -/
def trivialCofibrationCylinder (hs : SecondEndpointSection N D) (n : SimplexCategory) :
    TrivialCofibrations.CylinderData (RowWeakEquivalences.coarseStructure N n).cof
      (RowWeakEquivalences.coarseStructure N n).weq where
  middle := middle N D n
  inclusion := inclusion N D n
  projection := projection N D n
  target := targetInclusion N D n
  factorization := (factorization N D n).factorization
  target_projection := targetInclusion_projection N D hs
  inclusion_cof := (factorization N D n).cofibration
  target_cof := targetInclusion_cof N D
  projection_weak := (factorization N D n).weak
  middle_cof α hl hr := (middle_exact N D n).cofibration α ⟨hl, hr⟩

@[simp] theorem trivialCofibrationCylinder_target (hs : SecondEndpointSection N D) (n : SimplexCategory) :
    (trivialCofibrationCylinder N D hs n).target = targetInclusion N D n := rfl

@[simp] theorem trivialCofibrationCylinder_projection (hs : SecondEndpointSection N D) (n : SimplexCategory) :
    (trivialCofibrationCylinder N D hs n).projection = (factorization N D n).projection := rfl
end RowFactorization

attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L → ∀ f : K ⟶ L, P (mappingCone f))
  (hshift : ∀ K, P K → P (K⟦(1 : ℤ)⟧))

/-- The actual complex row cylinder supplies every comparison input, including the second section. -/
def complexRowTrivialCofibrationCylinder (n : SimplexCategory) :
    TrivialCofibrations.CylinderData
      (RowWeakEquivalences.coarseStructure (complexSubcategoryNested P) n).cof
      (RowWeakEquivalences.coarseStructure (complexSubcategoryNested P) n).weq :=
  RowFactorization.trivialCofibrationCylinder (complexSubcategoryNested P) (complexJointData P hcone hshift)
    (complexJointData_secondEndpointSection P hcone hshift) n

end Quillen.Waldhausen.Fibration
