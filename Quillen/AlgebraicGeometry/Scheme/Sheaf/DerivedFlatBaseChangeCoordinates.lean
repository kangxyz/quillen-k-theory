/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.DerivedIsomorphismFunctors
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.DerivedFlatBaseChangeVertical
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.DerivedFlatBaseChangeLocalization
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.DerivedSingleAcyclicity

/-! # Coordinate transport of the original derived flat base-change mate -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.SchemeSheaf
/-- The original standard module-sheaf derived categories. -/
local instance coordinateStandard (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _
variable {Z' Z W U V X : Scheme.{u}}
  (c : Z' ⟶ Z) (d : Z' ⟶ W) (g : Z ⟶ U)
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (hs : IsPullback c d g a) (h : IsPullback a b f j) [Flat j] [IsIso g]
/-- Source-coordinate transport retains the same derived mate under actual direct image. -/
theorem isIso_derivedFlatBaseChangeMap_sourceIso_iff (K : DerivedCategory.Plus Z.Modules) :
    letI := flat_cartesian_baseChange a b f j h
    letI := flat_cartesian_baseChange c d g a hs
    IsIso ((derivedFlatBaseChangeMap a b f j h).app ((derivedPushforwardPlus g).obj K)) ↔
      IsIso ((derivedFlatBaseChangeMap c (d ≫ b) (g ≫ f) j (hs.paste_vert h)).app K) := by
  let := flat_cartesian_baseChange a b f j h
  let := flat_cartesian_baseChange c d g a hs
  have := isIso_derivedFlatBaseChangeMap_of_isIso c d g a hs
  rw [← derivedFlatBaseChangeMap_paste_vert c d g a b f j hs h,
    derivedFlatBaseChangeVerticalComposite_app]
  rw [isIso_comp_left_iff, ← Category.assoc, isIso_comp_right_iff,
    isIso_comp_right_iff]
/-- Actual source-coordinate pullback transports the original single-sheaf mate. -/
theorem isIso_derivedFlatBaseChangeMap_sourceIso_single_iff (M : U.Modules) :
    letI := flat_cartesian_baseChange a b f j h
    letI := flat_cartesian_baseChange c d g a hs
    IsIso ((derivedFlatBaseChangeMap a b f j h).app
      ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)) ↔
      IsIso ((derivedFlatBaseChangeMap c (d ≫ b) (g ≫ f) j (hs.paste_vert h)).app
        ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj
          ((Scheme.Modules.pullback g).obj M))) := by
  let := flat_cartesian_baseChange a b f j h
  let := flat_cartesian_baseChange c d g a hs
  let := pushforward_isEquivalence_of_isIso g
  have : IsIso (derivedPushforwardPlusUnit g) :=
    (Scheme.Modules.pushforward g).isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  let e := derivedPushforwardPlusSingleIso g ((Scheme.Modules.pullback g).obj M) ≪≫
    (DerivedCategory.Plus.singleFunctor U.Modules 0).mapIso
      (asIso ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M)).symm
  exact (NatTrans.isIso_app_iff_of_iso (derivedFlatBaseChangeMap a b f j h) e).symm.trans
    (isIso_derivedFlatBaseChangeMap_sourceIso_iff c d g a b f j hs h _)
end Quillen.SchemeSheaf

namespace Quillen.SchemeSheaf
attribute [local instance] coordinateStandard
variable {W' W U V' V X : Scheme.{u}}
  (c : W' ⟶ W) (d : W' ⟶ V') (k : V' ⟶ V)
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (hs : IsPullback c d b k) (h : IsPullback a b f j)
/-- An actual target-coordinate isomorphism retains invertibility of the same original mate. -/
theorem isIso_derivedFlatBaseChangeMap_targetIso_iff [IsIso k] [Flat j]
    (K : DerivedCategory.Plus U.Modules) :
    letI := flat_cartesian_baseChange a b f j h
    letI := flat_cartesian_baseChange c d b k hs
    IsIso ((derivedFlatBaseChangeMap a b f j h).app K) ↔
      IsIso ((derivedFlatBaseChangeMap (c ≫ a) d f (k ≫ j) (hs.paste_horiz h)).app K) := by
  let := flat_cartesian_baseChange a b f j h
  let := flat_cartesian_baseChange c d b k hs
  have := derivedFlatPullbackPlus_isEquivalence_of_isIso k
  rw [← isIso_iff_of_reflects_iso ((derivedFlatBaseChangeMap a b f j h).app K)
    (derivedFlatPullbackPlus k)]
  exact isIso_derivedFlatBaseChangeMap_pullback_iff c d k a b f j hs h K
/-- An actual base-coordinate isomorphism preserves the original pasted mate criterion. -/
theorem isIso_derivedFlatBaseChangeMap_baseIso_iff [Flat k] [IsIso j]
    (K : DerivedCategory.Plus U.Modules) :
    letI := flat_cartesian_baseChange a b f j h
    letI := flat_cartesian_baseChange c d b k hs
    IsIso ((derivedFlatBaseChangeMap c d b k hs).app ((derivedFlatPullbackPlus a).obj K)) ↔
      IsIso ((derivedFlatBaseChangeMap (c ≫ a) d f (k ≫ j) (hs.paste_horiz h)).app K) := by
  let := flat_cartesian_baseChange a b f j h
  let := flat_cartesian_baseChange c d b k hs
  have := isIso_derivedFlatBaseChangeMap_of_open a b f j h
  rw [← derivedFlatBaseChangeMap_paste_horiz c d k a b f j hs h,
    derivedFlatBaseChangeHorizontalComposite_app]
  rw [isIso_comp_left_iff, isIso_comp_left_iff, isIso_comp_right_iff]
end Quillen.SchemeSheaf

namespace Quillen.SchemeSheaf
/-- The standard derived category of module sheaves. -/
local instance affineCoordinateStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _
variable {W U V X U' : Scheme.{u}}
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (h : IsPullback a b f j) [Flat j]
/-- The original source-coordinate cartesian square. -/
theorem sourceCoordinateSquare (e : U' ≅ U) :
    IsPullback (a ≫ e.inv) (𝟙 W) e.hom a :=
  IsPullback.of_vert_isIso ⟨by simp⟩
/-- Source coordinates transport the actual single-sheaf base-change mate. -/
theorem isIso_derivedFlatBaseChangeMap_sourceCoordinates_iff (e : U' ≅ U)
    (M : U.Modules) :
    letI := flat_cartesian_baseChange a b f j h
    IsIso ((derivedFlatBaseChangeMap a b f j h).app
      ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)) ↔
    IsIso ((derivedFlatBaseChangeMap (a ≫ e.inv) ((𝟙 W) ≫ b) (e.hom ≫ f) j
      ((sourceCoordinateSquare a e).paste_vert h)).app
      ((DerivedCategory.Plus.singleFunctor U'.Modules 0).obj
        ((Scheme.Modules.pullback e.hom).obj M))) := by
  exact isIso_derivedFlatBaseChangeMap_sourceIso_single_iff
    (a ≫ e.inv) (𝟙 W) e.hom a b f j (sourceCoordinateSquare a e) h M
/-- The original target-coordinate cartesian square. -/
theorem targetCoordinateSquare {V' : Scheme.{u}} (e : V' ≅ V) :
    IsPullback (𝟙 W) (b ≫ e.inv) b e.hom :=
  IsPullback.of_horiz_isIso ⟨by simp⟩
/-- Target coordinates retain the original derived mate criterion. -/
theorem isIso_derivedFlatBaseChangeMap_targetCoordinates_iff {V' : Scheme.{u}}
    (e : V' ≅ V) (K : DerivedCategory.Plus U.Modules) :
    letI := flat_cartesian_baseChange a b f j h
    IsIso ((derivedFlatBaseChangeMap a b f j h).app K) ↔
    IsIso ((derivedFlatBaseChangeMap ((𝟙 W) ≫ a) (b ≫ e.inv) f (e.hom ≫ j)
      ((targetCoordinateSquare b e).paste_horiz h)).app K) := by
  exact isIso_derivedFlatBaseChangeMap_targetIso_iff
    (𝟙 W) (b ≫ e.inv) e.hom a b f j (targetCoordinateSquare b e) h K
/-- Changing the base by an actual scheme isomorphism gives a cartesian square. -/
theorem baseCoordinateSquare {X' : Scheme.{u}} (e : X ≅ X') :
    IsPullback (𝟙 U) f (f ≫ e.hom) e.hom :=
  IsPullback.of_horiz_isIso ⟨by simp⟩
/-- Base coordinates retain the original derived mate, using its actual identity pullback. -/
theorem isIso_derivedFlatBaseChangeMap_baseCoordinates_iff {X' : Scheme.{u}}
    (e : X ≅ X') (K : DerivedCategory.Plus U.Modules) :
    letI := flat_cartesian_baseChange a b f j h
    IsIso ((derivedFlatBaseChangeMap a b f j h).app K) ↔
    IsIso ((derivedFlatBaseChangeMap (a ≫ 𝟙 U) b (f ≫ e.hom) (j ≫ e.hom)
      (h.paste_horiz (baseCoordinateSquare f e))).app K) := by
  let := flat_cartesian_baseChange a b f j h
  let ei : derivedFlatPullbackPlus (𝟙 U) ≅ 𝟭 (DerivedCategory.Plus U.Modules) :=
    (Scheme.Modules.pullback (𝟙 U)).rightDerivedFunctorPlusIso
      (Scheme.Modules.pullbackId U) ≪≫ Functor.rightDerivedFunctorPlusIdIso U.Modules
  exact (NatTrans.isIso_app_iff_of_iso (derivedFlatBaseChangeMap a b f j h)
    (ei.app K)).symm.trans
    (isIso_derivedFlatBaseChangeMap_baseIso_iff a b j (𝟙 U) f (f ≫ e.hom) e.hom
      h (baseCoordinateSquare f e) K)
/-- Changing the pullback corner by its actual scheme isomorphism is cartesian. -/
theorem cornerCoordinateSquare {W' : Scheme.{u}} (e : W' ≅ W) :
    IsPullback (e.hom ≫ a) e.hom (𝟙 U) a :=
  IsPullback.of_vert_isIso ⟨by simp⟩
/-- Corner coordinates retain the original derived mate, using actual identity direct image. -/
theorem isIso_derivedFlatBaseChangeMap_cornerCoordinates_iff {W' : Scheme.{u}}
    (e : W' ≅ W) (K : DerivedCategory.Plus U.Modules) :
    letI := flat_cartesian_baseChange a b f j h
    IsIso ((derivedFlatBaseChangeMap a b f j h).app K) ↔
    IsIso ((derivedFlatBaseChangeMap (e.hom ≫ a) (e.hom ≫ b) ((𝟙 U) ≫ f) j
      ((cornerCoordinateSquare a e).paste_vert h)).app K) := by
  let := flat_cartesian_baseChange a b f j h
  let ei : derivedPushforwardPlus (𝟙 U) ≅ 𝟭 (DerivedCategory.Plus U.Modules) :=
    (Scheme.Modules.pushforward (𝟙 U)).rightDerivedFunctorPlusIso
      (Scheme.Modules.pushforwardId U) ≪≫ Functor.rightDerivedFunctorPlusIdIso U.Modules
  exact (NatTrans.isIso_app_iff_of_iso (derivedFlatBaseChangeMap a b f j h)
    (ei.app K)).symm.trans
    (isIso_derivedFlatBaseChangeMap_sourceIso_iff (e.hom ≫ a) e.hom (𝟙 U)
      a b f j (cornerCoordinateSquare a e) h K)
end Quillen.SchemeSheaf

namespace Quillen.SchemeSheaf
/-- The standard derived category of module sheaves. -/
local instance normalizationStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _
/-- Equality of the four original arrows preserves the actual mate criterion. -/
theorem derivedFlatBaseChangeMap_congr_iff
    {W U V X : Scheme.{u}} {a a' : W ⟶ U} {b b' : W ⟶ V}
    {f f' : U ⟶ X} {j j' : V ⟶ X} [Flat j] [Flat j']
    (ha : a = a') (hb : b = b') (hf : f = f') (hj : j = j')
    (h : IsPullback a b f j) (h' : IsPullback a' b' f' j')
    (K : DerivedCategory.Plus U.Modules) :
    IsIso ((derivedFlatBaseChangeMap a b f j h).app K) ↔
      IsIso ((derivedFlatBaseChangeMap a' b' f' j' h').app K) := by
  subst a' b' f' j'
  rfl
variable {W U V X W' U' V' X' : Scheme.{u}}
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (h : IsPullback a b f j)
  (eW : W' ≅ W) (eU : U' ≅ U) (eV : V' ≅ V) (eX : X ≅ X')
include h
/-- The same cartesian square expressed in four actual scheme coordinates. -/
theorem coordinatePullback :
    IsPullback (eW.hom ≫ a ≫ eU.inv) (eW.hom ≫ b ≫ eV.inv)
      (eU.hom ≫ f ≫ eX.hom) (eV.hom ≫ j ≫ eX.hom) := by
  have h1 := (sourceCoordinateSquare a eU).paste_vert h
  have h2 := (targetCoordinateSquare ((𝟙 W) ≫ b) eV).paste_horiz h1
  have h3 := h2.paste_horiz (baseCoordinateSquare (eU.hom ≫ f) eX)
  have h4 := (cornerCoordinateSquare ((𝟙 W) ≫ (a ≫ eU.inv) ≫ 𝟙 U') eW).paste_vert h3
  simpa only [Category.id_comp, Category.comp_id, Category.assoc] using h4
/-- All four coordinate changes retain the actual single-sheaf derived mate. -/
theorem isIso_derivedFlatBaseChangeMap_coordinates_iff [Flat j] (M : U.Modules) :
    letI := flat_cartesian_baseChange a b f j h
    IsIso ((derivedFlatBaseChangeMap a b f j h).app
      ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)) ↔
    IsIso ((derivedFlatBaseChangeMap _ _ _ _ (coordinatePullback a b f j h eW eU eV eX)).app
      ((DerivedCategory.Plus.singleFunctor U'.Modules 0).obj
        ((Scheme.Modules.pullback eU.hom).obj M))) := by
  let := flat_cartesian_baseChange a b f j h
  have h1 := (sourceCoordinateSquare a eU).paste_vert h
  have h2 := (targetCoordinateSquare ((𝟙 W) ≫ b) eV).paste_horiz h1
  have h3 := h2.paste_horiz (baseCoordinateSquare (eU.hom ≫ f) eX)
  let K := (DerivedCategory.Plus.singleFunctor U'.Modules 0).obj
    ((Scheme.Modules.pullback eU.hom).obj M)
  have s1 := isIso_derivedFlatBaseChangeMap_sourceCoordinates_iff a b f j h eU M
  have s2 := isIso_derivedFlatBaseChangeMap_targetCoordinates_iff
    (a ≫ eU.inv) ((𝟙 W) ≫ b) (eU.hom ≫ f) j h1 eV K
  have s3 := isIso_derivedFlatBaseChangeMap_baseCoordinates_iff
    ((𝟙 W) ≫ (a ≫ eU.inv)) (((𝟙 W) ≫ b) ≫ eV.inv)
    (eU.hom ≫ f) (eV.hom ≫ j) h2 eX K
  have s4 := isIso_derivedFlatBaseChangeMap_cornerCoordinates_iff
    (((𝟙 W) ≫ (a ≫ eU.inv)) ≫ 𝟙 U') (((𝟙 W) ≫ b) ≫ eV.inv)
    ((eU.hom ≫ f) ≫ eX.hom) ((eV.hom ≫ j) ≫ eX.hom) h3 eW K
  apply (s1.trans (s2.trans (s3.trans s4))).trans
  exact derivedFlatBaseChangeMap_congr_iff
    (by simp) (by simp) (by simp [Category.assoc]) (by simp [Category.assoc])
    _ (coordinatePullback a b f j h eW eU eV eX) K
end Quillen.SchemeSheaf
