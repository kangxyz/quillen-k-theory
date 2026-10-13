/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.Cylinder.AmbientRelative
public import Quillen.Waldhausen.Cylinder.SubcategoryPreservation
public import Quillen.Waldhausen.ExtensionCategory.Embeddings
public import Quillen.Waldhausen.SplitComplexes.FunctorialFactorization

/-! # The actual cylinder as a functor of cofibration arrows

Each arbitrary complex arrow is sent to its original joint endpoint inclusion.
The target uses the genuine Reedy cofibrations on cofibration arrows. Relative
cofibration preservation is derived from the actual cylinder quotient, rather
than included as an input cylinder axiom.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CochainComplex
universe u v

namespace Quillen.Waldhausen.SplitFactorization
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L →
    ∀ f : K ⟶ L, P (mappingCone f))
  (hshift : ∀ K, P K → P (K⟦(1 : ℤ)⟧))

/-- The original joint endpoint inclusion as an actual cofibration-arrow functor. -/
def subcategoryJointFunctor : Arrow P.FullSubcategory ⥤
    ExtensionCategory.Obj (complexSubcategory P) where
  obj f := ⟨Arrow.mk (subcategoryJointInclusion P hcone f),
    (subcategoryJointInclusion_cof P hcone hshift f).1⟩
  map α := (ExtensionCategory.objects (complexSubcategory P)).homMk
    (Arrow.homMk (P.homMk (biprod.map α.left.hom α.right.hom))
      ((subcategoryMiddleFunctor P hcone).map α)
      (ObjectProperty.hom_ext _ (jointInclusion_naturality (P.ι.mapArrow.map α)).symm))
  map_id f := by
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext
    · apply ObjectProperty.hom_ext
      apply biprod.hom_ext <;> simp
    · exact (subcategoryMiddleFunctor P hcone).map_id f
  map_comp α β := by
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext
    · apply ObjectProperty.hom_ext
      apply biprod.hom_ext <;> simp
    · exact (subcategoryMiddleFunctor P hcone).map_comp α β

/-- Its underlying inclusion is literally the original joint cylinder map. -/
@[simp] theorem subcategoryJointFunctor_obj_hom (f : Arrow P.FullSubcategory) :
    ((subcategoryJointFunctor P hcone hshift).obj f).obj.hom =
      subcategoryJointInclusion P hcone f := rfl

/-- Its right component is literally the original cylinder middle functor. -/
@[simp] theorem subcategoryJointFunctor_comp_middle :
    subcategoryJointFunctor P hcone hshift ⋙ ExtensionCategory.middle (complexSubcategory P) =
      subcategoryMiddleFunctor P hcone := rfl

/-- The original map of joint cylinders satisfies the actual Reedy relative
cofibration condition whenever its endpoint sum is admissible. -/
theorem subcategoryJointFunctor_map_cof_of_source
    {f g : Arrow P.FullSubcategory} (α : f ⟶ g)
    (hα : (complexSubcategory P).cof α.left)
    (hs : (complexSubcategory P).cof
      (P.homMk (biprod.map α.left.hom α.right.hom) :
        subcategoryJointSource P f ⟶ subcategoryJointSource P g)) :
    ExtensionCategory.cof (complexSubcategory P)
      ((subcategoryJointFunctor P hcone hshift).map α) := by
  let W := complexSubcategory P
  let F := subcategoryJointFunctor P hcone hshift
  let b : subcategoryJointSource P f ⟶ subcategoryJointSource P g :=
    P.homMk (biprod.map α.left.hom α.right.hom)
  obtain ⟨R, i, j, h⟩ := W.pushout_exists (subcategoryJointInclusion P hcone f) b
    (subcategoryJointInclusion_cof P hcone hshift f).1
  let k : R ⟶ (subcategoryMiddleFunctor P hcone).obj g :=
    h.desc ((subcategoryMiddleFunctor P hcone).map α)
      (subcategoryJointInclusion P hcone g)
      (ObjectProperty.hom_ext _ (jointInclusion_naturality (P.ι.mapArrow.map α)))
  have hi : i ≫ k = (subcategoryMiddleFunctor P hcone).map α := h.inl_desc _ _ _
  have hj : j ≫ k = subcategoryJointInclusion P hcone g := h.inr_desc _ _ _
  apply ExtensionCategory.cof_of_relative W (F.map α) hs h k hi hj
  exact subcategoryRelativeJoint_ambient_cof P hcone hshift α i j
    (fullSubcategory_map_pushout _ P
      (subcategoryJointInclusion_cof P hcone hshift f).1 h) k hi hj hα

end Quillen.Waldhausen.SplitFactorization
