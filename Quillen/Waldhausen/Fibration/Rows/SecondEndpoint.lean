/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.Fibration.Rows.ComplexFactorization

/-! # The actual second cylinder endpoint on genuine quotient rows

The second endpoint is a genuine row cofibration by the original endpoint
coproduct pushout. Its projection-section identity is a separate structural
datum, absent from JointData; the actual identity-cone cylinder proves it
literally. Coarse two-out-of-three then makes both endpoints coarse-weak
whenever the original arrow is coarse-weak.
-/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.Fibration
namespace RowFactorization
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (D : JointData N)

/-- The second original endpoint injection is a genuine Reedy row cofibration. -/
theorem second_cof {n : SimplexCategory} (f : Arrow (QuotientRows.Obj V n)) :
    QuotientRows.cof V n ((second N D n).app f) :=
  (QuotientRows.waldhausenStructure V n).cof_pushout
    (QuotientRows.cof_zero V n f.left) (endpoint_isPushout N D f)

/-- The original target endpoint in the actual cylinder middle row. -/
def targetInclusion (n : SimplexCategory) : Arrow.rightFunc ⟶ middle N D n :=
  second N D n ≫ Functor.whiskerLeft (jointOnRows N D n)
    (ExtensionCategory.inclusion (QuotientRows.waldhausenStructure V n))

/-- The entire actual target inclusion satisfies the genuine row cofibration predicate. -/
theorem targetInclusion_cof {n : SimplexCategory} (f : Arrow (QuotientRows.Obj V n)) :
    QuotientRows.cof V n ((targetInclusion N D n).app f) :=
  (QuotientRows.waldhausenStructure V n).cof.comp_mem _ _ (second_cof N D f)
    ((jointOnRows N D n).obj f).property

/-- The component remains the original second injection followed by the actual joint inclusion. -/
@[simp] theorem targetInclusion_component {n : SimplexCategory}
    (f : Arrow (QuotientRows.Obj V n)) (p : Interval n) :
    (((targetInclusion N D n).app f).hom.app p) =
      D.inr.app (Arrow.mk (f.hom.hom.app p)) ≫
        (D.joint.obj (Arrow.mk (f.hom.hom.app p))).obj.hom := rfl

/-- This section identity is additional structural data, not a field inferred from JointData. -/
def SecondEndpointSection : Prop :=
  ∀ f : Arrow C, D.inr.app f ≫ (D.joint.obj f).obj.hom ≫ D.projection.app f = 𝟙 f.right

/-- A proved base section identity lifts componentwise to the unchanged row projection. -/
@[reassoc] theorem targetInclusion_projection (hs : SecondEndpointSection N D)
    {n : SimplexCategory} (f : Arrow (QuotientRows.Obj V n)) :
    (targetInclusion N D n).app f ≫ (projection N D n).app f = 𝟙 f.right := by
  apply ObjectProperty.hom_ext
  ext p
  change (D.inr.app (Arrow.mk (f.hom.hom.app p)) ≫
    (D.joint.obj (Arrow.mk (f.hom.hom.app p))).obj.hom) ≫
      D.projection.app (Arrow.mk (f.hom.hom.app p)) = 𝟙 _
  simpa only [Category.assoc] using! hs (Arrow.mk (f.hom.hom.app p))

/-- The actual second endpoint is coarse-weak because its composite with the weak projection is
identity. -/
theorem targetInclusion_weak (hs : SecondEndpointSection N D)
    [N.coarse.weq.HasTwoOutOfThreeProperty] {n : SimplexCategory}
    (f : Arrow (QuotientRows.Obj V n)) :
    (RowWeakEquivalences.coarseStructure N n).weq ((targetInclusion N D n).app f) := by
  apply (RowWeakEquivalences.coarseStructure N n).weq.of_postcomp
    (W' := (RowWeakEquivalences.coarseStructure N n).weq) _ ((projection N D n).app f)
    ((factorization N D n).weak f)
  rw [targetInclusion_projection N D hs]
  exact (RowWeakEquivalences.coarseStructure N n).weq.id_mem _

/-- For an original coarse-weak arrow the actual first factor is also coarse-weak. -/
theorem inclusion_weak [N.coarse.weq.HasTwoOutOfThreeProperty] {n : SimplexCategory}
    (f : Arrow (QuotientRows.Obj V n)) (hf : (RowWeakEquivalences.coarseStructure N n).weq f.hom) :
    (RowWeakEquivalences.coarseStructure N n).weq ((inclusion N D n).app f) := by
  apply (RowWeakEquivalences.coarseStructure N n).weq.of_postcomp
    (W' := (RowWeakEquivalences.coarseStructure N n).weq) _ ((projection N D n).app f)
    ((factorization N D n).weak f)
  rw [show (inclusion N D n).app f ≫ (projection N D n).app f = f.hom from
    (factorization N D n).factorization f]
  exact hf
end RowFactorization

attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L → ∀ f : K ⟶ L, P (mappingCone f))
  (hshift : ∀ K, P K → P (K⟦(1 : ℤ)⟧))

/-- The actual identity-cone joint cylinder proves the second-endpoint section identity. -/
theorem complexJointData_secondEndpointSection :
    RowFactorization.SecondEndpointSection (complexSubcategoryNested P) (complexJointData P
      hcone hshift) := by
  intro f
  apply ObjectProperty.hom_ext
  change biprod.inr ≫ SplitFactorization.jointInclusion f.hom.hom ≫
    SplitFactorization.projection f.hom.hom = 𝟙 _
  rw [← Category.assoc, SplitFactorization.jointInclusion, biprod.inr_desc]
  exact biprod.inr_snd

/-- The actual complex row target endpoint, retaining the original ambient biproduct inclusion. -/
def complexRowTargetInclusion (n : SimplexCategory) :
    Arrow.rightFunc ⟶ (complexRowFactorization P hcone hshift n).middle :=
  RowFactorization.targetInclusion (complexSubcategoryNested P) (complexJointData P hcone hshift) n

/-- Its unchanged component is literally the original target biproduct inclusion. -/
@[simp] theorem complexRowTargetInclusion_component {n : SimplexCategory}
    (f : Arrow (QuotientRows.Obj
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex A
        ℤ)) P)) n))
    (p : Interval n) :
    (((complexRowTargetInclusion P hcone hshift n).app f).hom.app p).hom =
      (biprod.inr : (f.right.obj.obj p).obj ⟶ SplitFactorization.middle (f.hom.hom.app p).hom) := by
  change biprod.inr ≫ SplitFactorization.jointInclusion (f.hom.hom.app p).hom = _
  exact biprod.inr_desc _ _

/-- The original complex row projection retracts this actual target inclusion exactly. -/
@[reassoc] theorem complexRowTargetInclusion_projection {n : SimplexCategory}
    (f : Arrow (QuotientRows.Obj
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex A
        ℤ)) P)) n)) :
    (complexRowTargetInclusion P hcone hshift n).app f ≫
      (complexRowFactorization P hcone hshift n).projection.app f = 𝟙 f.right :=
  RowFactorization.targetInclusion_projection (complexSubcategoryNested P) (complexJointData P
    hcone hshift)
    (complexJointData_secondEndpointSection P hcone hshift) f

end Quillen.Waldhausen.Fibration
