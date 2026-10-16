/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionOpenNull
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.SupportedSectionUnit
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumIsoNaturality
public import Quillen.Waldhausen.SConstruction.Iterated.TransformationInterchange

/-!
# Literal scalar interchange for the original supported-section null track

The source and target use the actual supported and coarse section categories and their inherited
zeros. The original forgetful functor preserves the scalar by its proved full-section equation;
the original zero functor does so by zero uniqueness. The original zero-to-section transformation
therefore commutes with both original time parameters, including the reversed null time and the
actual degree-zero loop. No scalar-interchange or seed-compatibility premise is supplied.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
    (r : (Γ(Spec R, ⊤))ˣ)

/-- Both independent original scalar and reversed null times commute on the unchanged section
prespectra, with their chosen zeros and literal support inclusion. -/
theorem boundedFlatAffineSupportedSectionOpenNullHomotopy_unit_apply
    (n : ℕ) (s t : unitInterval)
    (x : (prespectrum (boundedFlatAffineSupportedSectionModel j)).space n) :
    (boundedFlatAffineSupportedSectionOpenNullHomotopy j).level n
        (s, (prespectrumIsoHomotopy (𝟙 (boundedFlatAffineSupportedSectionModel j))
          (boundedFlatAffineSupportedSectionUnitIso j r)).level n (t, x)) =
      (prespectrumIsoHomotopy (𝟙 (boundedFlatAffineSectionOpenModel j))
        (boundedFlatAffineSectionUnitIso R r)).level n
        (t, (boundedFlatAffineSupportedSectionOpenNullHomotopy j).level n (s, x)) := by
  exact prespectrumTransformationHomotopy_symm_identityAction_interchange
    (F := Quillen.Waldhausen.IteratedS.zeroHom
      (boundedFlatAffineSupportedSectionModel j) (boundedFlatAffineSectionOpenModel j))
    (G := boundedFlatAffineSupportedSectionForgetModelMap j ≫
      boundedFlatAffineSectionOpenModelMap j)
    (boundedFlatAffineSupportedSectionZeroToOpen j)
    (boundedFlatAffineSupportedSectionUnitIso j r).hom
    (boundedFlatAffineSectionUnitIso R r).hom
    (boundedFlatAffineSupportedSectionZeroToOpen_weak j)
    (fun X => (boundedFlatAffineSupportedSectionModel j).waldhausen.weq_iso _
      (show IsIso ((boundedFlatAffineSupportedSectionUnitIso j r).app X).hom from inferInstance))
    (fun X => (boundedFlatAffineSectionOpenModel j).waldhausen.weq_iso _
      (show IsIso ((boundedFlatAffineSectionUnitIso R r).app X).hom from inferInstance))
    (fun _ => (boundedFlatAffineSectionOpenModel j).waldhausen.isZero.eq_of_src _ _)
    (fun X => boundedFlatAffineSupportedSectionUnitIso_hom j r X) n s t x

end Quillen.PerfectComplexes
