/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionKComparison

/-! Original perfect object classes and all-degree classes lift back to the same section groups. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace QuillenTest.FullOpenSectionKComparison

open Quillen
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

/-- The inverse perfect comparison recovers the exact original section object-loop class. -/
theorem original_object_class_inverse (a : Under R)
    (S : BoundedFlatAffineFullOpenSections j a) :
    (boundedFlatAffineFullOpenSectionPerfectKEquiv j a 0).symm
        ((perfectWaldhausen (openSpace j a)).kZeroObjectClass
          ((boundedFlatAffineFullOpenPerfectEvaluation j a).obj S)) =
      (boundedFlatAffineFullOpenSectionWaldhausen j a).kZeroObjectClass S := by
  rw [← boundedFlatAffineFullOpenSectionPerfectKEquiv_objectClass j a S,
    MulEquiv.symm_apply_apply]

/-- The comparison keeps products of original object-loop classes in the original perfect group. -/
theorem original_object_classes_product (a : Under R)
    (S T : BoundedFlatAffineFullOpenSections j a) :
    boundedFlatAffineFullOpenSectionPerfectKEquiv j a 0
        ((boundedFlatAffineFullOpenSectionWaldhausen j a).kZeroObjectClass S *
          (boundedFlatAffineFullOpenSectionWaldhausen j a).kZeroObjectClass T) =
      (perfectWaldhausen (openSpace j a)).kZeroObjectClass
          ((boundedFlatAffineFullOpenPerfectEvaluation j a).obj S) *
        (perfectWaldhausen (openSpace j a)).kZeroObjectClass
          ((boundedFlatAffineFullOpenPerfectEvaluation j a).obj T) := by
  rw [map_mul, boundedFlatAffineFullOpenSectionPerfectKEquiv_objectClass,
    boundedFlatAffineFullOpenSectionPerfectKEquiv_objectClass]

/-- Every original perfect K-class has a preimage under this same original section comparison. -/
theorem original_perfect_class_preimage (a : Under R) (n : ℕ)
    (x : (perfectWaldhausen (openSpace j a)).K n) :
    ∃ y : (boundedFlatAffineFullOpenSectionWaldhausen j a).K n,
      boundedFlatAffineFullOpenSectionPerfectKEquiv j a n y = x :=
  (boundedFlatAffineFullOpenSectionPerfectKEquiv j a n).surjective x

end QuillenTest.FullOpenSectionKComparison
