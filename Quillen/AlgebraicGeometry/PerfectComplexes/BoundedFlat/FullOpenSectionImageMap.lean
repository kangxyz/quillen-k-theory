/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenImagePullback
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionGrading
public import Quillen.AlgebraicGeometry.Scheme.Affine.OpenPairCompactness

/-!
# Actual coefficient action on the original full-open section grades

The quotient map acts on the unchanged relative-open image quotient. Its action
on a section grade is computed using the actual coefficient-evaluation isomorphism
and the original bounded-flat representative. Arbitrary coefficient arrows are
allowed; compactness is proved for their actual pulled-back opens.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.AlgebraicGrothendieck
open AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

local instance (a : Under R) : CompactSpace (openSpace j a) := compactSpace_openSpace j a

/-- Arbitrary coefficients act on the original relative-open image quotients. -/
def boundedFlatAffineFullOpenSectionImageMap {a b : Under R} (f : a ⟶ b) :
    ImageQuotient (perfectOpenWeakWaldhausen (inclusion j a))
        (perfectRestrict (inclusion j a)) (perfectOpenRestrict_waldhausenExact (inclusion j a)) →+
    ImageQuotient (perfectOpenWeakWaldhausen (inclusion j b))
        (perfectRestrict (inclusion j b)) (perfectOpenRestrict_waldhausenExact (inclusion j b)) :=
  perfectOpenImageQuotientPullback (inclusion j a) (inclusion j b)
    (Spec.map f.right) (openMap j f) (openMap_inclusion j f)

/-- The actual quotient action preserves the original grade of every reindexed section. -/
theorem boundedFlatAffineFullOpenSectionImageMap_value {a b : Under R} (f : a ⟶ b)
    (S : BoundedFlatAffineFullOpenSections j a) :
    boundedFlatAffineFullOpenSectionImageMap j f
        ((boundedFlatAffineFullOpenSectionGrading j a).value S) =
      (boundedFlatAffineFullOpenSectionGrading j b).value
        ((boundedFlatAffineFullOpenSectionsMap j f).obj S) := by
  change perfectOpenImageQuotientPullback (inclusion j a) (inclusion j b)
    (Spec.map f.right) (openMap j f) (openMap_inclusion j f)
      ((imageQuotientGrading (perfectOpenWeakWaldhausen (inclusion j a))
        (perfectRestrict (inclusion j a))
        (perfectOpenRestrict_waldhausenExact (inclusion j a))).value
          ((boundedFlatPerfectInclusion (openSpace j a)).obj
            ((boundedFlatAffineFullOpenOriginalEvaluation j a).obj S))) = _
  rw [perfectOpenImageQuotientPullback_boundedFlat_objectClass]
  let e := (boundedFlatPerfectInclusion (openSpace j b)).mapIso
    ((boundedFlatAffineFullOpenSectionCoefficientIso j f).app S)
  exact (perfectOpenDeficitGrading (inclusion j b)).weak e.inv
    ((perfectWaldhausen (openSpace j b)).weq_iso _ (by
      change IsIso e.inv
      infer_instance))

end Quillen.PerfectComplexes
