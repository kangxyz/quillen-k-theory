/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionWaldhausen
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionOpenStructure

/-!
# Original relative-open weak equivalences of affine sections

The original section category keeps its cofibrations and chosen zero. Weak equivalences
are detected by actual original evaluation into the existing bounded-flat relative-open
model. The original support predicate makes the unique zero-to-section transformation
weak after restriction, without any assumption about the full open K₀ endpoint.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes
open Waldhausen Fibration
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedFlatAffineOriginalEvaluation

/-- The unique arrow from the original section zero to each original supported section. -/
def boundedFlatAffineSupportedSectionZeroToOpen :
    (Functor.const (BoundedFlatAffineSupportedSections j)).obj
        (boundedFlatAffineSectionWaldhausen R).zero ⟶ (boundedFlatAffineSectionSupported j).ι where
  app s := (boundedFlatAffineSectionWaldhausen R).isZero.to_ s.obj
  naturality _ _ _ := (boundedFlatAffineSectionWaldhausen R).isZero.eq_of_src _ _

/-- Actual support proves weakness of the entire original zero-to-inclusion transformation. -/
theorem boundedFlatAffineSupportedSectionZeroToOpen_weak
    (s : BoundedFlatAffineSupportedSections j) :
    (boundedFlatAffineSectionOpenWaldhausen j).weq
      ((boundedFlatAffineSupportedSectionZeroToOpen j).app s) := by
  have hZ : IsZero ((restrict j).obj
      ((boundedFlatAffineOriginalEvaluation R).obj
        (boundedFlatAffineSectionWaldhausen R).zero).obj) :=
    (restrict j).map_isZero ((boundedFlatPerfect (Spec R)).ι.map_isZero
      ((boundedFlatAffineOriginalEvaluation_exact R).zero
        (boundedFlatAffineSectionWaldhausen R).isZero))
  change QuasiIso ((restrict j).map
    ((boundedFlatAffineOriginalEvaluation R).map
      ((boundedFlatAffineSupportedSectionZeroToOpen j).app s)).hom)
  rw [quasiIso_iff]
  intro n
  exact (quasiIsoAt_iff_exactAt _ n (HomologicalComplex.acyclic_of_isZero _ hZ n)).mpr
    (s.property n)

end Quillen.PerfectComplexes
