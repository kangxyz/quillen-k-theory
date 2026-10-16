/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.JointComparison

/-! # Original cross-category cocylinder consumers -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open Quillen.PerfectComplexes
open Quillen.PerfectComplexes.OpenDerivedImage
open Quillen.Waldhausen
open Quillen.Waldhausen.SplitFactorization


open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite HomologicalComplex
open Quillen
attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts
namespace QuillenTest.OppositeJointMap

open Quillen

section Ambient
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D] (F : C ⥤ D) [F.Additive]
open Waldhausen.SplitFactorization

/-- The original inclusion, section and projection survive arbitrary additive change of category. -/
theorem original_three_cylinder_maps {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (F.mapHomologicalComplex (.up ℤ)).map (inclusion f) ≫ (middleMapIso F f).hom =
        inclusion ((F.mapHomologicalComplex (.up ℤ)).map f) ∧
      (F.mapHomologicalComplex (.up ℤ)).map (biprod.inr : L ⟶ middle f) ≫
        (middleMapIso F f).hom = biprod.inr ∧
      (middleMapIso F f).hom ≫ projection ((F.mapHomologicalComplex (.up ℤ)).map f) =
        (F.mapHomologicalComplex (.up ℤ)).map (projection f) :=
  ⟨middleMapIso_inclusion F f, middleMapIso_section F f, middleMapIso_projection F f⟩

/-- Whole cylinder naturality retains the original commutative square, without exactness. -/
theorem original_cylinder_arrow_square {f g : Arrow (CochainComplex C ℤ)} (α : f ⟶ g) :
    (F.mapHomologicalComplex (.up ℤ)).map (middleFunctor.map α) ≫ (middleMapIso F g.hom).hom =
      (middleMapIso F f.hom).hom ≫ middleFunctor.map ((F.mapHomologicalComplex (.up ℤ)).mapArrow.map
        α) :=
  middleMapIso_naturality F α
end Ambient

section Source
variable {C : Type u} [Category.{v} C] [Abelian C]
  (P : ObjectProperty (CochainComplex C ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex C ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts] (hP : ∀ K, P K → P (K⟦(-1 : ℤ)⟧))

/-- The actual opposite joint arrow is split epic in every original degree. -/
theorem original_joint_degreewise_split_epi (f : Arrow P.FullSubcategoryᵒᵖ) (n : ℤ) :
    IsSplitEpi ((((oppositeComplexJointData P hP).joint.obj f).obj.hom.unop.hom).f n) := by
  let g := ((oppositePropertyEquivalence P).inverse.mapArrow.obj f).hom.hom
  have := SplitFactorization.jointInclusion_degreewiseSplitMono g (-n)
  change IsSplitEpi ((SplitFactorization.jointInclusion g).f (-n)).unop
  let s := this.exists_splitMono.some
  exact IsSplitEpi.mk' ⟨s.retraction.unop, congrArg Quiver.Hom.unop s.id⟩
end Source

section CrossCategory
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D] (F : C ⥤ D) [F.Additive]
  (P : ObjectProperty (CochainComplex C ℤ)) (Q : ObjectProperty (CochainComplex D ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex C ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex D ℤ)).IsExtensionClosed Q]
  [Q.IsClosedUnderFiniteProducts]
  (hF : ∀ K, P K → Q ((F.mapHomologicalComplex (.up ℤ)).obj K))
  (hP : ∀ K, P K → P (K⟦(-1 : ℤ)⟧)) (hQ : ∀ K, Q K → Q (K⟦(-1 : ℤ)⟧))
  (hExact : IsExact (oppositeComplexSubcategory P).cof (oppositeComplexSubcategory P).weq
    (oppositeComplexSubcategory Q).cof (oppositeComplexSubcategory Q).weq
    (complexSubcategoryMap F P Q hF).op)

/-- Independent object/hom universes retain both exact endpoint equations and the original weak
  projection. -/
theorem original_inverse_endpoint_triple (f : Arrow P.FullSubcategoryᵒᵖ) :
    (oppositeComplexJointData Q hQ).inl.app ((complexSubcategoryMap F P Q hF).op.mapArrow.obj f) ≫
        ((oppositeComplexJointDataMapIso F P Q hF hP hQ hExact).inv.app f).hom.left =
      (complexSubcategoryMap F P Q hF).op.map ((oppositeComplexJointData P hP).inl.app f) ∧
    (oppositeComplexJointData Q hQ).inr.app ((complexSubcategoryMap F P Q hF).op.mapArrow.obj f) ≫
        ((oppositeComplexJointDataMapIso F P Q hF hP hQ hExact).inv.app f).hom.left =
      (complexSubcategoryMap F P Q hF).op.map ((oppositeComplexJointData P hP).inr.app f) ∧
    ((oppositeComplexJointDataMapIso F P Q hF hP hQ hExact).inv.app f).hom.right ≫
        (complexSubcategoryMap F P Q hF).op.map ((oppositeComplexJointData P hP).projection.app f) =
      (oppositeComplexJointData Q hQ).projection.app ((complexSubcategoryMap F P Q
        hF).op.mapArrow.obj f) :=
  ⟨oppositeComplexJointDataMapIso_inv_inl F P Q hF hP hQ hExact f,
    oppositeComplexJointDataMapIso_inv_inr F P Q hF hP hQ hExact f,
    oppositeComplexJointDataMapIso_inv_projection F P Q hF hP hQ hExact f⟩
end CrossCategory

section Geometry
open PerfectComplexes.OpenDerivedImage
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [Fact (HasDerivedRoofs j)]

/-- The entire original geometric joint-arrow comparison is natural for every actual square. -/
theorem original_restriction_joint_naturality {f g : Arrow (Perfect X)ᵒᵖ} (α : f ⟶ g) :
    ((perfectOppositeJointData X).joint ⋙
      ExtensionCategory.postcompose (perfectOppositeWaldhausen X) (complexOppositeWaldhausen j)
        (complexCorestrict_op_exact j)).map α ≫ (complexCorestrictOpJointIso j).hom.app g =
      (complexCorestrictOpJointIso j).hom.app f ≫
        ((complexCorestrict j).op.mapArrow ⋙ (complexOppositeJointData j).joint).map α :=
  (complexCorestrictOpJointIso j).hom.naturality α

/-- The target cocylinder retains a genuine derived-image kernel in the original ambient sheaf
  category. -/
theorem original_target_kernel_witness (f : Arrow (Perfect X)ᵒᵖ) :
    let e := ((complexOppositeJointData j).joint.obj ((complexCorestrict j).op.mapArrow.obj f))
    ∃ (Z : CochainComplex U.Modules ℤ) (_hZ : complexObjects j Z) (i : Z ⟶ e.obj.right.unop.obj)
        (h : i ≫ e.obj.hom.unop.hom = 0),
      (ShortComplex.mk i e.obj.hom.unop.hom h).ShortExact := by
  exact (ExactSubcategory.deflation_iff (abelianExactStructure (CochainComplex U.Modules ℤ))
    (complexObjects j) _).mp
    (((complexOppositeJointData j).joint.obj ((complexCorestrict j).op.mapArrow.obj f)).property)
end Geometry
end QuillenTest.OppositeJointMap
