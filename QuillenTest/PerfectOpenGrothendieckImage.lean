/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenGrothendieckImage

/-! # Consumers retaining the original relative-open image quotient -/
@[expose] public section

open Quillen.PerfectComplexes


noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.AlgebraicGrothendieck
universe u
namespace QuillenTest.PerfectOpenGrothendieckImage

open Quillen
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The unchanged two algebraic restriction maps have the identical target subgroup. -/
theorem original_ranges :
    (map (perfectOpenWeakWaldhausen j) (perfectRestrict j)
      (perfectOpenRestrict_waldhausenExact j)).range =
    (map (perfectWaldhausen X) (perfectRestrict j) (perfectRestrict_waldhausenExact j)).range :=
  range_perfectOpenGrothendieckRestrict j

/-- The comparison preserves each original target quotient projection. -/
theorem original_quotient_projection (y : Group (perfectWaldhausen U)) :
    perfectFineOpenImageQuotientEquiv j
      (QuotientAddGroup.mk'
        (map (perfectWaldhausen X) (perfectRestrict j)
          (perfectRestrict_waldhausenExact j)).range y) =
    QuotientAddGroup.mk' (map (perfectOpenWeakWaldhausen j) (perfectRestrict j)
      (perfectOpenRestrict_waldhausenExact j)).range y :=
  perfectFineOpenImageQuotientEquiv_mk j y

/-- The target is precisely the original relative-open object grading used by the deficit. -/
theorem original_object_grade (K : Perfect U) :
    perfectFineOpenImageQuotientEquiv j
      ((imageQuotientGrading (perfectWaldhausen X) (perfectRestrict j)
        (perfectRestrict_waldhausenExact j)).value K) =
    (imageQuotientGrading (perfectOpenWeakWaldhausen j) (perfectRestrict j)
      (perfectOpenRestrict_waldhausenExact j)).value K :=
  perfectFineOpenImageQuotientEquiv_objectClass j K

end QuillenTest.PerfectOpenGrothendieckImage
