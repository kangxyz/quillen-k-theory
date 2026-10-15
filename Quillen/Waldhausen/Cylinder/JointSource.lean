/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.Cylinder.Subcategory
public import Quillen.Waldhausen.ArrowCategory.Structure
public import Quillen.Waldhausen.Additivity.SplitSequence
public import Quillen.Waldhausen.ExtensionCategory.ExactTransport

/-! # The actual joint-endpoint source functor

Objects are the original ambient biproduct of the source and target, with
membership supplied by extension closure. Maps are the literal ambient
`biprod.map`. Its genuine coproduct universal property identifies this functor
with the already exact sum of the two actual arrow evaluations. This proves
structural exactness for any Waldhausen structure on the same full subcategory,
in particular for both inherited isomorphism and quasi-isomorphism structures.
-/
@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v

namespace Quillen.Waldhausen.SplitFactorization
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]

/-- The actual ambient endpoint biproduct, functorial by the literal biproduct map. -/
def subcategoryJointSourceFunctor : Arrow P.FullSubcategory ⥤ P.FullSubcategory where
  obj f := subcategoryJointSource P f
  map α := P.homMk (biprod.map α.left.hom α.right.hom)
  map_id f := by apply ObjectProperty.hom_ext; apply biprod.hom_ext <;> simp
  map_comp α β := by apply ObjectProperty.hom_ext; apply biprod.hom_ext <;> simp

@[simp] theorem subcategoryJointSourceFunctor_obj (f : Arrow P.FullSubcategory) :
    (subcategoryJointSourceFunctor P).obj f = subcategoryJointSource P f := rfl

@[simp] theorem subcategoryJointSourceFunctor_map {f g : Arrow P.FullSubcategory} (α : f ⟶ g) :
    ((subcategoryJointSourceFunctor P).map α).hom = biprod.map α.left.hom α.right.hom := rfl

/-- The first actual endpoint inclusion. -/
def subcategoryJointSourceInl : Arrow.leftFunc ⟶ subcategoryJointSourceFunctor P where
  app _ := P.homMk biprod.inl
  naturality f g α := by apply ObjectProperty.hom_ext; simp [subcategoryJointSourceFunctor]

/-- The second actual endpoint inclusion. -/
def subcategoryJointSourceInr : Arrow.rightFunc ⟶ subcategoryJointSourceFunctor P where
  app _ := P.homMk biprod.inr
  naturality f g α := by apply ObjectProperty.hom_ext; simp [subcategoryJointSourceFunctor]

/-- The ambient biproduct is an actual coproduct in the full subcategory. -/
def subcategoryJointSourceCofanIsColimit (f : Arrow P.FullSubcategory) :
    IsColimit (BinaryCofan.mk ((subcategoryJointSourceInl P).app f)
      ((subcategoryJointSourceInr P).app f)) := by
  refine BinaryCofan.IsColimit.mk _ (fun a b ↦ P.homMk (biprod.desc a.hom b.hom)) ?_ ?_ ?_
  · intro T a b
    apply ObjectProperty.hom_ext
    exact biprod.inl_desc _ _
  · intro T a b
    apply ObjectProperty.hom_ext
    exact biprod.inr_desc _ _
  · intro T a b m hm hn
    apply ObjectProperty.hom_ext
    apply biprod.hom_ext'
    · simpa [subcategoryJointSourceInl] using congrArg (fun k ↦ k.hom) hm
    · simpa [subcategoryJointSourceInr] using congrArg (fun k ↦ k.hom) hn

variable [P.IsClosedUnderFiniteProducts]

/-- The canonical chosen-coproduct to actual ambient biproduct isomorphism. -/
def subcategoryJointSourceCoproductIso (f : Arrow P.FullSubcategory) :
    f.left ⨿ f.right ≅ subcategoryJointSource P f :=
  (coprodIsCoprod _ _).coconePointUniqueUpToIso (subcategoryJointSourceCofanIsColimit P f)

@[reassoc (attr := simp)] theorem subcategoryJointSourceCoproductIso_inl (f : Arrow
    P.FullSubcategory) :
    coprod.inl ≫ (subcategoryJointSourceCoproductIso P f).hom = (subcategoryJointSourceInl
      P).app f :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod f.left f.right)
    (subcategoryJointSourceCofanIsColimit P f) (Discrete.mk WalkingPair.left)

@[reassoc (attr := simp)] theorem subcategoryJointSourceCoproductIso_inr (f : Arrow
    P.FullSubcategory) :
    coprod.inr ≫ (subcategoryJointSourceCoproductIso P f).hom = (subcategoryJointSourceInr
      P).app f :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod f.left f.right)
    (subcategoryJointSourceCofanIsColimit P f) (Discrete.mk WalkingPair.right)

/-- The actual ambient biproduct functor is naturally the sum of the actual evaluations. -/
def subcategoryJointSourceSumIso :
    Additivity.sumFunctor Arrow.leftFunc Arrow.rightFunc ≅ subcategoryJointSourceFunctor P :=
  NatIso.ofComponents (subcategoryJointSourceCoproductIso P) (by
    intro X Y f
    apply coprod.hom_ext
    · simp only [Additivity.sumFunctor, coprod.inl_map_assoc]
      have h := (subcategoryJointSourceInl P).naturality f
      rw [← subcategoryJointSourceCoproductIso_inl P X,
        ← subcategoryJointSourceCoproductIso_inl P Y] at h
      simpa only [Category.assoc] using! h
    · simp only [Additivity.sumFunctor, coprod.inr_map_assoc]
      have h := (subcategoryJointSourceInr P).naturality f
      rw [← subcategoryJointSourceCoproductIso_inr P X,
        ← subcategoryJointSourceCoproductIso_inr P Y] at h
      simpa only [Category.assoc] using! h)

/-- Genuine source exactness, for any actual Waldhausen structure on the full subcategory. -/
theorem subcategoryJointSourceFunctor_isExact (W : Structure P.FullSubcategory) :
    IsExact (ArrowCategory.waldhausenStructure W).cof (ArrowCategory.waldhausenStructure W).weq
      W.cof W.weq (subcategoryJointSourceFunctor P) :=
  ExtensionCategory.isExact_of_natIso (ArrowCategory.waldhausenStructure W) W
    (Additivity.sumFunctor_isExact (ArrowCategory.waldhausenStructure W) W
      (ArrowCategory.source_exact W) (ArrowCategory.target_exact W))
        (subcategoryJointSourceSumIso P)

variable [P.ContainsZero] [P.IsClosedUnderIsomorphisms]

/-- Specialization to inherited admissible cofibrations and actual isomorphisms. -/
theorem subcategoryJointSourceFunctor_isoExact :
    let W := ofExactCategory (ExactSubcategory.exactStructure
      (abelianExactStructure (CochainComplex A ℤ)) P)
    IsExact (ArrowCategory.waldhausenStructure W).cof (ArrowCategory.waldhausenStructure W).weq
      W.cof W.weq (subcategoryJointSourceFunctor P) :=
  subcategoryJointSourceFunctor_isExact P _

/-- Specialization to inherited admissible cofibrations and actual quasi-isomorphisms. -/
theorem subcategoryJointSourceFunctor_quasiExact :
    IsExact (ArrowCategory.waldhausenStructure (complexSubcategory P)).cof
      (ArrowCategory.waldhausenStructure (complexSubcategory P)).weq
      (complexSubcategory P).cof (complexSubcategory P).weq (subcategoryJointSourceFunctor P) :=
  subcategoryJointSourceFunctor_isExact P _

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms] in
/-- Actual displayed component pushouts give the displayed joint-source pushout. -/
theorem subcategoryJointSourceFunctor_map_isPushout (W : Structure P.FullSubcategory)
    {F G H T : Arrow P.FullSubcategory} {f : F ⟶ G} {g : F ⟶ H} {i : G ⟶ T} {j : H ⟶ T}
    (hf : W.cof f.left ∧ W.cof f.right)
    (hL : IsPushout f.left g.left i.left j.left)
    (hR : IsPushout f.right g.right i.right j.right) :
    IsPushout ((subcategoryJointSourceFunctor P).map f) ((subcategoryJointSourceFunctor P).map g)
      ((subcategoryJointSourceFunctor P).map i) ((subcategoryJointSourceFunctor P).map j) :=
  (subcategoryJointSourceFunctor_isExact P W).pushout hf
    (ArrowCategory.isPushout_of_pointwise f g i j hL hR)

end Quillen.Waldhausen.SplitFactorization
