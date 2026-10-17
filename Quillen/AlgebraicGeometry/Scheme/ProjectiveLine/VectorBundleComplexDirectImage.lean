/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.VectorBundleDirectImage
public import Quillen.Aglib.Algebra.Homology.DerivedCategory.BoundedRightDerivedUnit

/-! # Actual projection comparisons for bounded vector-bundle complexes

The original right-derived unit is invertible after termwise projection pullback, with or
without the actual negative twist. The negatively twisted termwise direct image is already
zero. The positive comparison uses the original degreewise geometric unit, whose naturality
is retained. All statements concern literal bounded complexes over arbitrary base rings.
-/
@[expose] public section
open Quillen

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules
/-- The standard derived category used for the actual bounded comparison. -/
local instance boundedBundleStandard (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _
/-- Negative-twisted pullbacks of affine bundles already have zero ordinary direct image. -/
theorem isZero_pushforward_twisted_bundle (R : CommRingCat.{u})
    (M : (Spec R).Modules) [IsFiniteLocallyFree (Spec R) M] :
    IsZero ((AlgebraicGeometry.Scheme.Modules.pushforward (projection R)).obj
      (twistMinus R ((AlgebraicGeometry.Scheme.Modules.pullback (projection R)).obj M))) := by
  let H := AlgebraicGeometry.Scheme.Modules.pullback (projection R) ⋙ twistMinusFunctor R
  let : H.Additive := by dsimp [H]; infer_instance
  let F := H ⋙ AlgebraicGeometry.Scheme.Modules.pushforward (projection R)
  let : F.Additive := by dsimp [F]; infer_instance
  let e : H.obj (SheafOfModules.unit (Spec R).ringCatSheaf) ≅ tautologicalLine R :=
    (twistMinusFunctor R).mapIso (pullbackUnitIso (projection R)) ≪≫ twistMinusUnitIso R
  apply isZero_obj_affineBundle_of_unit R F _ M
  exact (isZero_pushforward_projection_tautologicalLine R).of_iso
    ((AlgebraicGeometry.Scheme.Modules.pushforward (projection R)).mapIso e)
/-- The installed unit on termwise pullback of a bounded vector-bundle complex is invertible. -/
theorem isIso_derivedProjectionUnit_pullback_bounded (R : CommRingCat.{u})
    (K : CochainComplex.Plus (Spec R).Modules) (a b : ℤ)
    (hl : ∀ i, i < a → IsZero (K.obj.X i)) (hu : ∀ i, b < i → IsZero (K.obj.X i))
    (hf : ∀ i, IsFiniteLocallyFree (Spec R) (K.obj.X i)) :
    IsIso ((derivedPushforwardPlusUnit (projection R)).app
      ((AlgebraicGeometry.Scheme.Modules.pullback
        (projection R)).mapCochainComplexPlus.obj K)) := by
  apply Functor.rightDerivedFunctorPlusUnit_isIso_of_term_bounds
    (AlgebraicGeometry.Scheme.Modules.pushforward (projection R)) _ a b
  · intro i hi
    exact (AlgebraicGeometry.Scheme.Modules.pullback (projection R)).map_isZero (hl i hi)
  · intro i hi
    exact (AlgebraicGeometry.Scheme.Modules.pullback (projection R)).map_isZero (hu i hi)
  · intro i
    let := hf i
    exact isIso_derivedProjectionUnit_pullback_bundle R (K.obj.X i)
/-- The installed unit on the actual negative twist of a bounded pullback is invertible. -/
theorem isIso_derivedProjectionUnit_twisted_bounded (R : CommRingCat.{u})
    (K : CochainComplex.Plus (Spec R).Modules) (a b : ℤ)
    (hl : ∀ i, i < a → IsZero (K.obj.X i)) (hu : ∀ i, b < i → IsZero (K.obj.X i))
    (hf : ∀ i, IsFiniteLocallyFree (Spec R) (K.obj.X i)) :
    IsIso ((derivedPushforwardPlusUnit (projection R)).app
      ((AlgebraicGeometry.Scheme.Modules.pullback (projection R) ⋙
        twistMinusFunctor R).mapCochainComplexPlus.obj K)) := by
  let H := AlgebraicGeometry.Scheme.Modules.pullback (projection R) ⋙ twistMinusFunctor R
  let : H.Additive := by dsimp [H]; infer_instance
  apply Functor.rightDerivedFunctorPlusUnit_isIso_of_term_bounds
    (AlgebraicGeometry.Scheme.Modules.pushforward (projection R)) _ a b
  · intro i hi
    exact H.map_isZero (hl i hi)
  · intro i hi
    exact H.map_isZero (hu i hi)
  · intro i
    let := hf i
    exact isIso_derivedProjectionUnit_twisted_bundle R (K.obj.X i)
/-- Termwise direct image of an actual negative-twisted bundle complex is zero. -/
theorem isZero_pushforward_twisted_complex (R : CommRingCat.{u})
    (K : CochainComplex.Plus (Spec R).Modules)
    (hf : ∀ i, IsFiniteLocallyFree (Spec R) (K.obj.X i)) :
    IsZero ((AlgebraicGeometry.Scheme.Modules.pushforward (projection R)).mapCochainComplexPlus.obj
      ((AlgebraicGeometry.Scheme.Modules.pullback (projection R) ⋙
        twistMinusFunctor R).mapCochainComplexPlus.obj K)) := by
  rw [IsZero.iff_id_eq_zero]
  apply ObjectProperty.hom_ext
  apply HomologicalComplex.Hom.ext
  funext i
  let := hf i
  exact (isZero_pushforward_twisted_bundle R (K.obj.X i)).eq_of_src _ _
/-- The actual negative-twisted bounded bundle complex has zero derived direct image. -/
theorem isZero_derivedProjection_twisted_bounded (R : CommRingCat.{u})
    (K : CochainComplex.Plus (Spec R).Modules) (a b : ℤ)
    (hl : ∀ i, i < a → IsZero (K.obj.X i)) (hu : ∀ i, b < i → IsZero (K.obj.X i))
    (hf : ∀ i, IsFiniteLocallyFree (Spec R) (K.obj.X i)) :
    IsZero ((derivedPushforwardPlus (projection R)).obj (DerivedCategory.Plus.Q.obj
      ((AlgebraicGeometry.Scheme.Modules.pullback (projection R) ⋙
        twistMinusFunctor R).mapCochainComplexPlus.obj K))) := by
  have := isIso_derivedProjectionUnit_twisted_bounded R K a b hl hu hf
  let : (DerivedCategory.Plus.Q (C := (Spec R).Modules)).Additive := by
    dsimp [DerivedCategory.Plus.Q]
    infer_instance
  exact (DerivedCategory.Plus.Q.map_isZero
    (isZero_pushforward_twisted_complex R K hf)).of_iso
      (asIso ((derivedPushforwardPlusUnit (projection R)).app _)).symm
/-- The original geometric adjunction unit on an actual bounded-below complex. -/
def projectionPullbackComplexUnit (R : CommRingCat.{u})
    (K : CochainComplex.Plus (Spec R).Modules) :
    K ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward (projection R)).mapCochainComplexPlus.obj
      ((AlgebraicGeometry.Scheme.Modules.pullback (projection R)).mapCochainComplexPlus.obj K) :=
  ObjectProperty.homMk
    { f i := (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
        (projection R)).unit.app (K.obj.X i)
      comm' i j _ := ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
        (projection R)).unit.naturality (K.obj.d i j)).symm }
/-- The degreewise geometric unit commutes with the original cochain maps. -/
theorem projectionPullbackComplexUnit_naturality (R : CommRingCat.{u})
    {K L : CochainComplex.Plus (Spec R).Modules} (f : K ⟶ L) :
    f ≫ projectionPullbackComplexUnit R L = projectionPullbackComplexUnit R K ≫
      (AlgebraicGeometry.Scheme.Modules.pushforward (projection R)).mapCochainComplexPlus.map
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (projection R)).mapCochainComplexPlus.map f) := by
  apply ObjectProperty.hom_ext
  apply HomologicalComplex.Hom.ext
  funext i
  exact (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
    (projection R)).unit.naturality
    (f.hom.f i)
/-- The original degreewise unit is invertible on complexes of affine vector bundles. -/
theorem isIso_projectionPullbackComplexUnit (R : CommRingCat.{u})
    (K : CochainComplex.Plus (Spec R).Modules)
    (hf : ∀ i, IsFiniteLocallyFree (Spec R) (K.obj.X i)) :
    IsIso (projectionPullbackComplexUnit R K) := by
  have (i : ℤ) : IsIso ((projectionPullbackComplexUnit R K).hom.f i) := by
    let := hf i
    exact isIso_projectionAdjunctionUnit_bundle R (K.obj.X i)
  have : IsIso ((CochainComplex.Plus.ι (Spec R).Modules).map
      (projectionPullbackComplexUnit R K)) := by
    change IsIso (projectionPullbackComplexUnit R K).hom
    exact HomologicalComplex.Hom.isIso_of_components _
  exact isIso_of_reflects_iso (projectionPullbackComplexUnit R K)
    (CochainComplex.Plus.ι _)
/-- The positive bounded comparison uses the actual complex adjunction unit and installed unit. -/
def derivedProjectionPullbackBoundedIso (R : CommRingCat.{u})
    (K : CochainComplex.Plus (Spec R).Modules) (a b : ℤ)
    (hl : ∀ i, i < a → IsZero (K.obj.X i)) (hu : ∀ i, b < i → IsZero (K.obj.X i))
    (hf : ∀ i, IsFiniteLocallyFree (Spec R) (K.obj.X i)) :
    DerivedCategory.Plus.Q.obj K ≅
      (derivedPushforwardPlus (projection R)).obj (DerivedCategory.Plus.Q.obj
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (projection R)).mapCochainComplexPlus.obj K)) := by
  have := isIso_projectionPullbackComplexUnit R K hf
  have := isIso_derivedProjectionUnit_pullback_bounded R K a b hl hu hf
  exact DerivedCategory.Plus.Q.mapIso (asIso (projectionPullbackComplexUnit R K)) ≪≫
    asIso ((derivedPushforwardPlusUnit (projection R)).app _)
/-- The bounded comparison retains both original unit morphisms. -/
theorem derivedProjectionPullbackBoundedIso_hom (R : CommRingCat.{u})
    (K : CochainComplex.Plus (Spec R).Modules) (a b : ℤ)
    (hl : ∀ i, i < a → IsZero (K.obj.X i)) (hu : ∀ i, b < i → IsZero (K.obj.X i))
    (hf : ∀ i, IsFiniteLocallyFree (Spec R) (K.obj.X i)) :
    (derivedProjectionPullbackBoundedIso R K a b hl hu hf).hom =
      DerivedCategory.Plus.Q.map (projectionPullbackComplexUnit R K) ≫
        (derivedPushforwardPlusUnit (projection R)).app
          ((AlgebraicGeometry.Scheme.Modules.pullback
            (projection R)).mapCochainComplexPlus.obj K) :=
  rfl
end AlgebraicGeometry.Scheme.ProjectiveLine
