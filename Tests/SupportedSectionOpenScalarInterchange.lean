/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionOpenScalarInterchange

/-!
# Consumers of the actual supported scalar and reversed null square

These retain the actual section categories, the specified original scalar, the independent
null, scalar and degree-zero loop coordinates, and the inherited zero-to-section transformation.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.Tests.SupportedSectionOpenScalarInterchange
open Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
    (r : (Γ(Spec R, ⊤))ˣ)

/-- The original scalar square retains the third, actual degree-zero loop coordinate. -/
theorem original_zero_level (s t q : unitInterval)
    (x : (prespectrum (boundedFlatAffineSupportedSectionModel j)).space 0) :
    Path.toContinuousMap
        ((boundedFlatAffineSupportedSectionOpenNullHomotopy j).level 0
          (s, (prespectrumIsoHomotopy (𝟙 (boundedFlatAffineSupportedSectionModel j))
            (boundedFlatAffineSupportedSectionUnitIso j r)).level 0 (t, x))) q =
      Path.toContinuousMap
        ((prespectrumIsoHomotopy (𝟙 (boundedFlatAffineSectionOpenModel j))
          (boundedFlatAffineSectionUnitIso R r)).level 0
          (t, (boundedFlatAffineSupportedSectionOpenNullHomotopy j).level 0 (s, x))) q :=
  congrArg (fun p => Path.toContinuousMap p q)
    (boundedFlatAffineSupportedSectionOpenNullHomotopy_unit_apply j r 0 s t x)

/-- The source of the interchange uses exactly the original reversed transformation time. -/
theorem original_reversed_null_coordinate (n : ℕ) (s t : unitInterval)
    (x : (prespectrum (boundedFlatAffineSupportedSectionModel j)).space n) :
    (boundedFlatAffineSupportedSectionOpenNullHomotopy j).level n
        (s, (prespectrumIsoHomotopy (𝟙 (boundedFlatAffineSupportedSectionModel j))
          (boundedFlatAffineSupportedSectionUnitIso j r)).level n (t, x)) =
      (prespectrumTransformationHomotopy
        (F := zeroHom (boundedFlatAffineSupportedSectionModel j)
          (boundedFlatAffineSectionOpenModel j))
        (G := boundedFlatAffineSupportedSectionForgetModelMap j ≫
          boundedFlatAffineSectionOpenModelMap j)
        (boundedFlatAffineSupportedSectionZeroToOpen j)
        (boundedFlatAffineSupportedSectionZeroToOpen_weak j)).level n
        (unitInterval.symm s,
          (prespectrumIsoHomotopy (𝟙 (boundedFlatAffineSupportedSectionModel j))
            (boundedFlatAffineSupportedSectionUnitIso j r)).level n (t, x)) := rfl

/-- The original section structure parameter is independent of both cylinder parameters. -/
theorem original_structure_time (n : ℕ) (s t q : unitInterval)
    (x : (prespectrum (boundedFlatAffineSupportedSectionModel j)).space n) :
    (boundedFlatAffineSupportedSectionOpenNullHomotopy j).level (n + 1)
        (s, (prespectrumIsoHomotopy (𝟙 (boundedFlatAffineSupportedSectionModel j))
          (boundedFlatAffineSupportedSectionUnitIso j r)).level (n + 1)
          (t, (prespectrum (boundedFlatAffineSupportedSectionModel j)).structureMap n x q)) =
      (prespectrum (boundedFlatAffineSectionOpenModel j)).structureMap n
        ((boundedFlatAffineSupportedSectionOpenNullHomotopy j).level n
          (s, (prespectrumIsoHomotopy (𝟙 (boundedFlatAffineSupportedSectionModel j))
            (boundedFlatAffineSupportedSectionUnitIso j r)).level n (t, x))) q := by
  rw [(prespectrumIsoHomotopy (𝟙 (boundedFlatAffineSupportedSectionModel j))
      (boundedFlatAffineSupportedSectionUnitIso j r)).comm,
    (boundedFlatAffineSupportedSectionOpenNullHomotopy j).comm]

end Quillen.Tests.SupportedSectionOpenScalarInterchange
