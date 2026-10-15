/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pushforward
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.TwoOpenSheafSequence
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffineCompositeDerivedPushforward
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AcyclicShortExactTriangle

/-!
# Actual derived computation from a two-open affine cover

Assume the two chart immersions and common overlap immersion are affine, as
are their composites with the original target morphism. For a quasicoherent
sheaf, the original signed sheaf sequence gives a distinguished triangle whose
last two terms are ordinary direct images. The first term remains the original
derived direct image, and the connecting morphism is explicitly preserved.
-/

@[expose] public section

open AlgebraicGeometry.Scheme.Modules


noncomputable section

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules.TwoOpen
/-- Use the standard derived category of actual module sheaves. -/
local instance twoOpenDerivedTermsStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _
variable {W U V X Y : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (j : U ⟶ X) (k : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion j] [IsOpenImmersion k]
  (h : a ≫ j = b ≫ k) (f : X ⟶ Y)
  [IsAffineHom j] [IsAffineHom k] [IsAffineHom (a ≫ j)]
  [IsAffineHom (j ≫ f)] [IsAffineHom (k ≫ f)] [IsAffineHom ((a ≫ j) ≫ f)]
  (M : X.Modules) [M.IsQuasicoherent]
omit [IsAffineHom (a ≫ j)] [IsAffineHom ((a ≫ j) ≫ f)] in
/-- The actual product of the two original chart direct images is acyclic for `f`. -/
theorem isIso_sheafSequence_second_derivedUnit :
    IsIso ((derivedPushforwardPlusUnit f).app
      (singleZeroPlus X (sheafSequence a b j k h M).X₂)) := by
  let : IsIso ((derivedPushforwardPlusUnit f).app
      (singleZeroPlus X ((openLocalization j).obj M))) :=
    isIso_derivedPushforwardPlusUnit_pushforward_single j f (M.restrict j)
  let : IsIso ((derivedPushforwardPlusUnit f).app
      (singleZeroPlus X ((openLocalization k).obj M))) :=
    isIso_derivedPushforwardPlusUnit_pushforward_single k f (M.restrict k)
  exact isIso_derivedPushforwardPlusUnit_single_prod f _ _
omit [IsAffineHom j] [IsAffineHom k] [IsAffineHom (j ≫ f)] [IsAffineHom (k ≫ f)] in
/-- The actual common-overlap direct image is acyclic for `f`. -/
theorem isIso_sheafSequence_third_derivedUnit :
    IsIso ((derivedPushforwardPlusUnit f).app
      (singleZeroPlus X (sheafSequence a b j k h M).X₃)) :=
  isIso_derivedPushforwardPlusUnit_pushforward_single (a ≫ j) f (M.restrict (a ≫ j))
end AlgebraicGeometry.Scheme.Modules.TwoOpen
end

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Pretriangulated AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules.TwoOpen
/-- Use the standard derived category of actual module sheaves. -/
local instance twoOpenDerivedTriangleStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _
variable {W U V X Y : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (j : U ⟶ X) (k : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion j] [IsOpenImmersion k]
  (h : IsPullback a b j k)
  (hcover : ∀ x : X, (∃ y : U, j y = x) ∨ (∃ z : V, k z = x)) (f : X ⟶ Y)
  [IsAffineHom j] [IsAffineHom k] [IsAffineHom (a ≫ j)]
  [IsAffineHom (j ≫ f)] [IsAffineHom (k ≫ f)] [IsAffineHom ((a ≫ j) ≫ f)]
  (M : X.Modules) [M.IsQuasicoherent]
/-- The derived Čech triangle has the literal pushforward of the signed difference. -/
def sheafDerivedCechTriangle : Triangle (DerivedCategory.Plus Y.Modules) := by
  letI := isIso_sheafSequence_second_derivedUnit a b j k h.w f M
  letI := isIso_sheafSequence_third_derivedUnit a b j k h.w f M
  exact acyclicShortExactTriangle f (sheafSequence_shortExact a b j k h M hcover)
/-- The computed triangle is identified with the original derived short-exact triangle. -/
def sheafDerivedCechTriangleIso :
    sheafDerivedCechTriangle a b j k h hcover f M ≅
      (derivedPushforwardPlus f).mapTriangle.obj
        (sheafSequence_shortExact a b j k h M hcover).singleTrianglePlus := by
  letI := isIso_sheafSequence_second_derivedUnit a b j k h.w f M
  letI := isIso_sheafSequence_third_derivedUnit a b j k h.w f M
  exact acyclicShortExactTriangleIso f (sheafSequence_shortExact a b j k h M hcover)
/-- The connecting arrow is the original derived connecting map after the overlap unit inverse. -/
theorem sheafDerivedCechTriangle_mor₃ :
    letI := isIso_sheafSequence_third_derivedUnit a b j k h.w f M
    (sheafDerivedCechTriangle a b j k h hcover f M).mor₃ =
      (derivedPushforwardPlusSingleIso f (sheafSequence a b j k h.w M).X₃).inv ≫
        ((derivedPushforwardPlus f).mapTriangle.obj
          (sheafSequence_shortExact a b j k h M hcover).singleTrianglePlus).mor₃ := rfl
/-- The original derived object is the first vertex of the computed Čech triangle. -/
theorem sheafDerivedCechTriangle_obj₁ :
    (sheafDerivedCechTriangle a b j k h hcover f M).obj₁ =
      (derivedPushforwardPlus f).obj ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) := rfl
/-- The differential is exactly the original sheaf restriction difference under direct image. -/
theorem sheafDerivedCechTriangle_mor₂ :
    (sheafDerivedCechTriangle a b j k h hcover f M).mor₂ =
      (DerivedCategory.Plus.singleFunctor Y.Modules 0).map
        ((Scheme.Modules.pushforward f).map (sheafDifference a b j k h.w M)) := rfl
/-- Original affine acyclicity and the genuine cover make the computed triangle distinguished. -/
theorem sheafDerivedCechTriangle_distinguished :
    sheafDerivedCechTriangle a b j k h hcover f M ∈
      distTriang (DerivedCategory.Plus Y.Modules) := by
  let := isIso_sheafSequence_second_derivedUnit a b j k h.w f M
  let := isIso_sheafSequence_third_derivedUnit a b j k h.w f M
  exact acyclicShortExactTriangle_distinguished f (sheafSequence_shortExact a b j k h M hcover)
end AlgebraicGeometry.Scheme.Modules.TwoOpen
end
