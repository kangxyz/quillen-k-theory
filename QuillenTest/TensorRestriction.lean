/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Restriction

/-!
# Original-map consumers of tensor restriction

The consumers inspect both-variable naturality, the literal sheafification-unit square,
actual inverse comparison and original scheme restriction. All rings may be zero.
-/

@[expose] public section

open AlgebraicGeometry.Scheme.Modules

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
  SheafOfModulesOfCommRing AlgebraicGeometry.Scheme.Modules
namespace QuillenTest.TensorRestriction

section Sites
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [F.IsContinuous J K] [F.IsCocontinuous J K]
  {S : Sheaf J CommRingCat.{u}} {R : Sheaf K CommRingCat.{u}}
  (φ : S ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj R)

/-- The compatibility uses the original maps on both sides. -/
theorem original_both_variable_square [IsIso φ.hom]
    {M M' N N' : SheafOfModulesOfCommRing R} (f : M ⟶ M') (g : N ⟶ N') :
    (associatedSheaf S).map
        (((toPresheaf S).map ((modulePushforward φ).map f)) ⊗ₘ
          ((toPresheaf S).map ((modulePushforward φ).map g))) ≫
        (tensorPushforwardIso φ M' N').hom =
      (tensorPushforwardIso φ M N).hom ≫
        (modulePushforward φ).map ((associatedSheaf R).map
          (((toPresheaf R).map f) ⊗ₘ ((toPresheaf R).map g))) :=
  tensorPushforwardIso_naturality φ f g

/-- The compatibility uses the original maps on both sides. -/
theorem original_sheafification_unit_square [IsIso φ.hom] (M N : SheafOfModulesOfCommRing R) :
    (associatedSheafUnit S).app
        (((toPresheaf S).obj ((modulePushforward φ).obj M)) ⊗
          ((toPresheaf S).obj ((modulePushforward φ).obj N))) ≫
      (toPresheaf S).map (tensorPushforwardIso φ M N).hom =
    PresheafOfModulesOfCommRing.pushforwardTensorHom φ.hom
        ((toPresheaf R).obj M) ((toPresheaf R).obj N) ≫
      (PresheafOfModulesOfCommRing.pushforward φ.hom).map
        ((associatedSheafUnit R).app
          (((toPresheaf R).obj M) ⊗ ((toPresheaf R).obj N))) :=
  tensorPushforwardIso_unit φ M N
/-- Applying the actual comparison and its inverse recovers the original tensor object. -/
theorem original_tensor_inverse [IsIso φ.hom] (M N : SheafOfModulesOfCommRing R) :
    (tensorPushforwardIso φ M N).hom ≫ (tensorPushforwardIso φ M N).inv =
      𝟙 ((tensorLeftFunctor S ((modulePushforward φ).obj M)).obj
        ((modulePushforward φ).obj N)) :=
  (tensorPushforwardIso φ M N).hom_inv_id
end Sites
section Schemes
variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
/-- The naturality square retains the original open-restriction functor. -/
theorem original_restriction_square (M : Y.Modules) {N P : Y.Modules} (g : N ⟶ P) :
    (moduleTensorLeftFunctor X (M.restrict j)).map
        ((Scheme.Modules.restrictFunctor j).map g) ≫ (tensorRestrictionIso j M P).hom =
      (tensorRestrictionIso j M N).hom ≫
        (Scheme.Modules.restrictFunctor j).map ((moduleTensorLeftFunctor Y M).map g) :=
  (tensorRestrictionNatIso j M).hom.naturality g
/-- The exact unit square uses the actual scheme restriction and sheafification maps. -/
theorem original_open_unit_square (M N : Y.Modules) :
    (associatedSheafUnit X.sheaf).app
        (((toPresheaf X.sheaf).obj (M.restrict j)) ⊗
          ((toPresheaf X.sheaf).obj (N.restrict j))) ≫
      (toPresheaf X.sheaf).map (tensorRestrictionIso j M N).hom =
    PresheafOfModulesOfCommRing.pushforwardTensorHom (restrictionRingHom j).hom
        ((toPresheaf Y.sheaf).obj M) ((toPresheaf Y.sheaf).obj N) ≫
      (PresheafOfModulesOfCommRing.pushforward (restrictionRingHom j).hom).map
        ((associatedSheafUnit Y.sheaf).app
          (((toPresheaf Y.sheaf).obj M) ⊗ ((toPresheaf Y.sheaf).obj N))) :=
  tensorRestrictionIso_unit j M N
/-- The original inverse section-ring map is used on every open. -/
theorem original_section_ring (U : X.Opens) :
    (restrictionRingHom j).hom.app (Opposite.op U) = (j.appIso U).inv := rfl
/-- Arbitrary-ring affine schemes retain the original identity restriction comparison. -/
def affineIdentityComparison (R : CommRingCat.{u}) (M N : (Spec R).Modules) :=
  tensorRestrictionIso (𝟙 (Spec R)) M N
/-- The zero ring requires no additional nontriviality premise. -/
def zeroRingComparison
    (M N : (Spec (CommRingCat.of (ZMod 1))).Modules) :=
  affineIdentityComparison (CommRingCat.of (ZMod 1)) M N
/-- A composite of two actual open immersions retains the original restricted arrow. -/
theorem composite_open_arrow {Z : Scheme.{u}} (k : Y ⟶ Z) [IsOpenImmersion k]
    (M : Z.Modules) {N P : Z.Modules} (g : N ⟶ P) :
    (moduleTensorLeftFunctor X (M.restrict (j ≫ k))).map
        ((Scheme.Modules.restrictFunctor (j ≫ k)).map g) ≫
          (tensorRestrictionIso (j ≫ k) M P).hom =
      (tensorRestrictionIso (j ≫ k) M N).hom ≫
        (Scheme.Modules.restrictFunctor (j ≫ k)).map
          ((moduleTensorLeftFunctor Z M).map g) :=
  (tensorRestrictionNatIso (j ≫ k) M).hom.naturality g
end Schemes
end QuillenTest.TensorRestriction
