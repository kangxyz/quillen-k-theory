/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionImageMap

/-!
# Original coefficient quotient and section-grade consumers

These checks retain the actual derived pullback, original relative-open quotient,
and original full-open section reindexing on arbitrary coefficient arrows.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.Waldhausen.AlgebraicGrothendieck
open Quillen.Scheme.AffineOpenPair
universe u
namespace QuillenTest.FullOpenSectionImageMap

open Quillen

/-- The original derived K-zero square retains both genuine Grothendieck comparisons. -/
theorem original_derived_comparison {X Y : Scheme.{u}} [CompactSpace X] [CompactSpace Y]
    (f : X ⟶ Y) (x : Group (perfectWaldhausen Y)) :
    perfectGrothendieckKZeroEquiv X (Multiplicative.ofAdd (perfectGrothendieckPullback f x)) =
      perfectKPullback f 0 (perfectGrothendieckKZeroEquiv Y (Multiplicative.ofAdd x)) :=
  perfectGrothendieckPullback_comparison f x

variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]
local instance (a : Under R) : CompactSpace (openSpace j a) := compactSpace_openSpace j a

omit [IsOpenImmersion j] in
/-- The genuine original pulled-back open is compact at each coefficient algebra. -/
theorem original_open_compact (a : Under R) : CompactSpace (openSpace j a) :=
  compactSpace_openSpace j a

/-- The quotient projection is the original coarse-source projection on both sides. -/
theorem original_quotient_projection {a b : Under R} (f : a ⟶ b)
    (x : Group (perfectWaldhausen (openSpace j a))) :
    boundedFlatAffineFullOpenSectionImageMap j f
      (QuotientAddGroup.mk' (map (perfectOpenWeakWaldhausen (inclusion j a))
        (perfectRestrict (inclusion j a))
        (perfectOpenRestrict_waldhausenExact (inclusion j a))).range x) =
    QuotientAddGroup.mk' (map (perfectOpenWeakWaldhausen (inclusion j b))
      (perfectRestrict (inclusion j b))
      (perfectOpenRestrict_waldhausenExact (inclusion j b))).range
        (perfectGrothendieckPullback (openMap j f) x) :=
  perfectOpenImageQuotientPullback_mk (inclusion j a) (inclusion j b)
    (Spec.map f.right) (openMap j f) (openMap_inclusion j f) x

/-- Original section grades commute with the actual arbitrary coefficient reindexing. -/
theorem original_section_grade {a b : Under R} (f : a ⟶ b)
    (S : BoundedFlatAffineFullOpenSections j a) :
    boundedFlatAffineFullOpenSectionImageMap j f
        ((boundedFlatAffineFullOpenSectionGrading j a).value S) =
      (boundedFlatAffineFullOpenSectionGrading j b).value
        ((boundedFlatAffineFullOpenSectionsMap j f).obj S) :=
  boundedFlatAffineFullOpenSectionImageMap_value j f S

/-- Equality of the original source grades implies equality after actual reindexing. -/
theorem original_equal_grades {a b : Under R} (f : a ⟶ b)
    (S T : BoundedFlatAffineFullOpenSections j a)
    (h : (boundedFlatAffineFullOpenSectionGrading j a).value S =
      (boundedFlatAffineFullOpenSectionGrading j a).value T) :
    (boundedFlatAffineFullOpenSectionGrading j b).value
        ((boundedFlatAffineFullOpenSectionsMap j f).obj S) =
      (boundedFlatAffineFullOpenSectionGrading j b).value
        ((boundedFlatAffineFullOpenSectionsMap j f).obj T) := by
  rw [← boundedFlatAffineFullOpenSectionImageMap_value,
    ← boundedFlatAffineFullOpenSectionImageMap_value, h]

end QuillenTest.FullOpenSectionImageMap
