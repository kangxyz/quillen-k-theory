/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.VectorBundleDirectImage
public import Mathlib.Data.ZMod.Basic

/-! # Consumers of original affine-bundle projection and negative-twist maps -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.SchemeSheaf Quillen.Scheme.ProjectiveLine
universe u
namespace Quillen.Tests.ProjectiveLineVectorBundleDirectImage
/-- The standard ambient derived category of actual module sheaves. -/
local instance standardDerived (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _

/-- The original pullback maps retain the actual affine sheaf retraction equation. -/
theorem original_pullback_retract (R : CommRingCat.{u}) (M : (Spec R).Modules)
    [IsFiniteLocallyFree (Spec R) M] :
    ∃ (I : Type u) (_ : Finite I) (r : Retract M
        (SheafOfModules.free (R := (Spec R).ringCatSheaf) I)),
      (AlgebraicGeometry.Scheme.Modules.pullback (projection R)).map r.i ≫
        (AlgebraicGeometry.Scheme.Modules.pullback (projection R)).map r.r = 𝟙 _ := by
  obtain ⟨I, hI, ⟨r⟩⟩ := exists_retract_finiteFree R M
  exact ⟨I, hI, r, (r.map _).retract⟩

/-- On the original structure module the geometric adjunction unit is the literal ringed unit. -/
theorem original_unit (R : CommRingCat.{u}) :
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (projection R)).unit.app
        (SheafOfModules.unit (Spec R).ringCatSheaf) ≫
      (AlgebraicGeometry.Scheme.Modules.pushforward (projection R)).map
        (pullbackUnitIso (projection R)).hom = projectionUnitMap R :=
  pullbackAdjunctionUnit_unit (projection R)

/-- Every arrow into the original ordinary direct image lifts uniquely through its actual unit. -/
theorem unique_original_unit_lift (R : CommRingCat.{u}) (M N : (Spec R).Modules)
    [IsFiniteLocallyFree (Spec R) M]
    (f : N ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward (projection R)).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback (projection R)).obj M)) :
    ∃! g : N ⟶ M, g ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
        (projection R)).unit.app M = f := by
  have := isIso_projectionAdjunctionUnit_bundle R M
  let a := (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
    (projection R)).unit.app M
  refine ⟨f ≫ inv a, by simp [a], ?_⟩
  intro g hg
  apply (cancel_mono a).mp
  simpa [a] using hg

/-- The actual geometric unit, single comparison, and installed derived unit compose to an iso. -/
theorem original_derived_composite (R : CommRingCat.{u}) (M : (Spec R).Modules)
    [IsFiniteLocallyFree (Spec R) M] :
    IsIso (DerivedCategory.Plus.Q.map
        ((CochainComplex.singleFunctorPlus (Spec R).Modules 0).map
          ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
            (projection R)).unit.app M)) ≫
      DerivedCategory.Plus.Q.map (pushforwardSingleZeroPlusIso (projection R)
        ((AlgebraicGeometry.Scheme.Modules.pullback (projection R)).obj M)).inv ≫
      (derivedPushforwardPlusUnit (projection R)).app
        (singleZeroPlus (twoChartLine R)
          ((AlgebraicGeometry.Scheme.Modules.pullback (projection R)).obj M))) := by
  rw [← derivedProjectionPullbackBundleIso_hom]
  infer_instance

/-- Every arrow into the actual negative-twisted derived direct image is zero. -/
theorem negative_derived_arrow_zero (R : CommRingCat.{u}) (M : (Spec R).Modules)
    [IsFiniteLocallyFree (Spec R) M] (K : DerivedCategory.Plus (Spec R).Modules)
    (f : K ⟶ (derivedPushforwardPlus (projection R)).obj (DerivedCategory.Plus.Q.obj
      (singleZeroPlus (twoChartLine R)
        (twistMinus R ((AlgebraicGeometry.Scheme.Modules.pullback (projection R)).obj M))))) :
    f = 0 := (isZero_derivedProjection_twisted_bundle R M).eq_of_tgt _ _

/-- A nonreduced base retains the literal geometric adjunction unit. -/
theorem nonreduced_unit : IsIso
    ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
      (projection (CommRingCat.of (ZMod 4)))).unit.app
        (SheafOfModules.unit (Spec (CommRingCat.of (ZMod 4))).ringCatSheaf)) :=
  isIso_projectionAdjunctionUnit_unit _

/-- The zero-ring base is included in the actual negative-twist direct-image theorem. -/
theorem zero_ring_negative : IsZero
    ((derivedPushforwardPlus (projection (CommRingCat.of (ZMod 1)))).obj
      (DerivedCategory.Plus.Q.obj (singleZeroPlus (twoChartLine (CommRingCat.of (ZMod 1)))
        (twistMinus (CommRingCat.of (ZMod 1))
          ((AlgebraicGeometry.Scheme.Modules.pullback (projection (CommRingCat.of (ZMod 1)))).obj
            (SheafOfModules.unit (Spec (CommRingCat.of (ZMod 1))).ringCatSheaf)))))) :=
  by
    let X := Spec (CommRingCat.of (ZMod 1))
    let e : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{0} Unit) ≅
        SheafOfModules.unit X.ringCatSheaf := coproductUniqueIso _
    have : IsFiniteLocallyFree X (SheafOfModules.unit X.ringCatSheaf) :=
      finiteLocallyFree_of_iso e
    exact isZero_derivedProjection_twisted_bundle _ _
end Quillen.Tests.ProjectiveLineVectorBundleDirectImage
