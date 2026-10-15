/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.VectorBundleComplexDirectImage
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedPushforwardComparison
public import Mathlib.Data.ZMod.Basic

/-! # Consumers of original strict-complex projection and negative-twist maps -/
@[expose] public section

open Quillen.PerfectComplexes

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace QuillenTest.ProjectiveLineVectorBundleComplexDirectImage

open Quillen
/-- The standard ambient derived category of actual module sheaves. -/
local instance standardDerived (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _


/-- Each actual complex-unit component is the original geometric adjunction unit. -/
theorem original_unit_component (R : CommRingCat.{u})
    (K : CochainComplex.Plus (Spec R).Modules) (i : ℤ) :
    (projectionPullbackComplexUnit R K).hom.f i =
      (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
        (projection R)).unit.app (K.obj.X i) := rfl

/-- Original cochain maps satisfy the actual geometric unit square. -/
theorem original_unit_square (R : CommRingCat.{u})
    {K L : CochainComplex.Plus (Spec R).Modules} (f : K ⟶ L) :
    f ≫ projectionPullbackComplexUnit R L = projectionPullbackComplexUnit R K ≫
      (AlgebraicGeometry.Scheme.Modules.pushforward (projection R)).mapCochainComplexPlus.map
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (projection R)).mapCochainComplexPlus.map f) :=
  projectionPullbackComplexUnit_naturality R f

/-- Both original installed units are invertible for the library's actual strict-perfect input. -/
theorem original_strict_units (R : CommRingCat.{u}) (K : StrictPerfect (Spec R)) :
    IsIso ((derivedPushforwardPlusUnit (projection R)).app
      ((AlgebraicGeometry.Scheme.Modules.pullback (projection R)).mapCochainComplexPlus.obj
        ((strictToPlus (Spec R)).obj K))) ∧
    IsIso ((derivedPushforwardPlusUnit (projection R)).app
      ((AlgebraicGeometry.Scheme.Modules.pullback (projection R) ⋙
        twistMinusFunctor R).mapCochainComplexPlus.obj ((strictToPlus (Spec R)).obj K))) := by
  obtain ⟨a, b, h⟩ := K.property.1
  exact ⟨isIso_derivedProjectionUnit_pullback_bounded R _ a b
      (fun i hi => h i (Or.inl hi)) (fun i hi => h i (Or.inr hi)) K.property.2,
    isIso_derivedProjectionUnit_twisted_bounded R _ a b
      (fun i hi => h i (Or.inl hi)) (fun i hi => h i (Or.inr hi)) K.property.2⟩

/-- The strict comparison retains the literal composite of the two original unit maps. -/
theorem original_strict_composite (R : CommRingCat.{u}) (K : StrictPerfect (Spec R)) :
    IsIso (DerivedCategory.Plus.Q.map
        (projectionPullbackComplexUnit R ((strictToPlus (Spec R)).obj K)) ≫
      (derivedPushforwardPlusUnit (projection R)).app
        ((AlgebraicGeometry.Scheme.Modules.pullback (projection R)).mapCochainComplexPlus.obj
          ((strictToPlus (Spec R)).obj K))) := by
  have := (original_strict_units R K).1
  have := isIso_projectionPullbackComplexUnit R ((strictToPlus (Spec R)).obj K) K.property.2
  infer_instance

/-- The negative-twisted ordinary pushforward is literally zero even without an upper bound. -/
theorem original_unbounded_above_term_zero (R : CommRingCat.{u})
    (K : CochainComplex.Plus (Spec R).Modules)
    (hK : ∀ i, IsFiniteLocallyFree (Spec R) (K.obj.X i)) (i : ℤ) :
    𝟙 (((AlgebraicGeometry.Scheme.Modules.pushforward (projection R)).mapCochainComplexPlus.obj
      ((AlgebraicGeometry.Scheme.Modules.pullback (projection R) ⋙
        twistMinusFunctor R).mapCochainComplexPlus.obj K)).obj.X i) = 0 := by
  let := hK i
  exact (isZero_pushforward_twisted_bundle R (K.obj.X i)).eq_of_src _ _

/-- Every arrow to the original strict negative-twist derived image vanishes. -/
theorem original_strict_negative_arrow (R : CommRingCat.{u}) (K : StrictPerfect (Spec R))
    (L : DerivedCategory.Plus (Spec R).Modules)
    (f : L ⟶ (derivedPushforwardPlus (projection R)).obj (DerivedCategory.Plus.Q.obj
      ((AlgebraicGeometry.Scheme.Modules.pullback (projection R) ⋙
        twistMinusFunctor R).mapCochainComplexPlus.obj ((strictToPlus (Spec R)).obj K)))) :
    f = 0 := by
  obtain ⟨a, b, h⟩ := K.property.1
  exact (isZero_derivedProjection_twisted_bounded R _ a b
    (fun i hi => h i (Or.inl hi)) (fun i hi => h i (Or.inr hi)) K.property.2).eq_of_tgt _ _

/-- The actual strict-complex theorem also covers the zero-ring base. -/
theorem zero_ring_strict_units (K : StrictPerfect (Spec (CommRingCat.of (ZMod 1)))) :
    IsIso ((derivedPushforwardPlusUnit (projection (CommRingCat.of (ZMod 1)))).app
      ((AlgebraicGeometry.Scheme.Modules.pullback (projection (CommRingCat.of (ZMod 1))) ⋙
        twistMinusFunctor (CommRingCat.of (ZMod 1))).mapCochainComplexPlus.obj
          ((strictToPlus (Spec (CommRingCat.of (ZMod 1)))).obj K))) :=
  (original_strict_units _ K).2
end QuillenTest.ProjectiveLineVectorBundleComplexDirectImage
