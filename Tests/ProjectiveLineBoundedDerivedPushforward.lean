/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.BoundedDerivedPushforward

/-! # Bounded projective-line direct-image consumers

These consumers retain the original quotient and direct-image functors, allow arbitrary
finite bounds, and transport the proved property along an actual derived isomorphism.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.SchemeSheaf Quillen.Scheme.ProjectiveLine
open Quillen.PerfectComplexes Quillen.PerfectComplexes.ProjectiveLine
universe u
namespace Quillen.Tests.ProjectiveLineBoundedDerivedPushforward
/-- The standard ambient derived category of original module sheaves. -/
local instance boundedConsumerStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _
variable (R : CommRingCat.{u})

/-- An arbitrary single degree is computed by the same original direct-image functor. -/
theorem shifted_single (M : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) M] (n : ℤ) :
    perfectDerivedObjects (Spec R)
      (DerivedCategory.Plus.ι.obj
        ((derivedPushforwardPlus (projection R)).obj
          ((DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules n).obj M))) :=
  perfect_derivedPushforward_vectorBundle_single R M n

/-- The input is the original quotient of the given bounded complex. -/
theorem original_bounded_image
    (K : CochainComplex.Plus (twoChartLine R).Modules) (a b : ℤ)
    (hl : ∀ i, i < a → IsZero (K.obj.X i))
    (hu : ∀ i, b < i → IsZero (K.obj.X i))
    (ht : ∀ i, IsFiniteLocallyFree (twoChartLine R) (K.obj.X i)) :
    perfectDerivedObjects (Spec R)
      (DerivedCategory.Plus.ι.obj
        ((derivedPushforwardPlus (projection R)).obj (DerivedCategory.Plus.Q.obj K))) :=
  perfect_derivedPushforward_of_bounded_vectorBundle_terms R K a b hl hu ht

/-- A supplied derived representative is transported by the actual direct-image map. -/
theorem actual_representative_image
    (K : CochainComplex.Plus (twoChartLine R).Modules) (a b : ℤ)
    (hl : ∀ i, i < a → IsZero (K.obj.X i))
    (hu : ∀ i, b < i → IsZero (K.obj.X i))
    (ht : ∀ i, IsFiniteLocallyFree (twoChartLine R) (K.obj.X i))
    (E : DerivedCategory.Plus (twoChartLine R).Modules)
    (e : DerivedCategory.Plus.Q.obj K ≅ E) :
    perfectDerivedObjects (Spec R)
      (DerivedCategory.Plus.ι.obj ((derivedPushforwardPlus (projection R)).obj E)) :=
  (perfectDerivedObjects (Spec R)).prop_of_iso
    (DerivedCategory.Plus.ι.mapIso ((derivedPushforwardPlus (projection R)).mapIso e))
    (original_bounded_image R K a b hl hu ht)

/-- Reversed term bounds are permitted, including the empty supported interval. -/
theorem empty_interval_image
    (K : CochainComplex.Plus (twoChartLine R).Modules)
    (hl : ∀ i, i < 1 → IsZero (K.obj.X i))
    (hu : ∀ i, 0 < i → IsZero (K.obj.X i))
    (ht : ∀ i, IsFiniteLocallyFree (twoChartLine R) (K.obj.X i)) :
    perfectDerivedObjects (Spec R)
      (DerivedCategory.Plus.ι.obj
        ((derivedPushforwardPlus (projection R)).obj (DerivedCategory.Plus.Q.obj K))) :=
  original_bounded_image R K 1 0 hl hu ht
end Quillen.Tests.ProjectiveLineBoundedDerivedPushforward
