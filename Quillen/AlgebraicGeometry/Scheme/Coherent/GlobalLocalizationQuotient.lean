/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Localization.Fullness

/-!
# From actual coherent object extension to the geometric Serre localization

Faithfulness and fullness have been proved for the canonical functor from
coherent sheaves modulo the actual support category. This file isolates the
last categorical step: essential surjectivity of actual open restriction
makes that quotient functor an equivalence and proves the localization
universal property for the original restriction functor.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Quillen.CoherentScheme

variable {U X : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian U]
  (j : U ⟶ X) [IsOpenImmersion j] [(finiteTypeSheavesRestriction j).EssSurj]

/-- Actual coherent object extension descends to essential surjectivity of
the canonical functor from the support quotient. -/
theorem quotientCoherentRestriction_essSurj_of_restriction :
    (quotientCoherentRestriction j).EssSurj where
  mem_essImage A := by
    obtain ⟨M, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (finiteTypeSheavesRestriction j) A
    refine ⟨(finiteTypeSheavesSupportedAway j).isoModSerre.Q.obj M, ⟨?_⟩⟩
    exact (quotientCoherentRestrictionFactorsIso j).app M ≪≫ e

/-- The full, faithful actual quotient functor is an equivalence once
actual coherent extension is known. -/
theorem quotientCoherentRestriction_isEquivalence_of_essSurj :
    (quotientCoherentRestriction j).IsEquivalence where
  essSurj := quotientCoherentRestriction_essSurj_of_restriction j

/-- The original geometric restriction is localization by actual coherent
support, using the equivalence of its constructed quotient. -/
theorem finiteTypeSheavesRestriction_isLocalization_of_essSurj :
    (finiteTypeSheavesRestriction j).IsLocalization
      (finiteTypeSheavesSupportedAway j).isoModSerre := by
  let := quotientCoherentRestriction_isEquivalence_of_essSurj j
  exact Functor.IsLocalization.of_equivalence_target
    (finiteTypeSheavesSupportedAway j).isoModSerre.Q (finiteTypeSheavesSupportedAway j).isoModSerre
    (finiteTypeSheavesRestriction j) (quotientCoherentRestriction j).asEquivalence
    (quotientCoherentRestrictionFactorsIso j)

/-- Equivalently, actual open restriction is localization by its kernel. -/
theorem finiteTypeSheavesRestriction_isLocalization_kernel_of_essSurj :
    (finiteTypeSheavesRestriction j).IsLocalization
      (finiteTypeSheavesRestriction j).kernel.isoModSerre := by
  have h : (finiteTypeSheavesRestriction j).kernel.isoModSerre =
      (finiteTypeSheavesSupportedAway j).isoModSerre := by
    funext M N f
    apply propext
    change ((finiteTypeSheavesRestriction j).kernel (kernel f) ∧
      (finiteTypeSheavesRestriction j).kernel (cokernel f)) ↔ _
    rw [finiteTypeSheavesRestriction_kernel_eq_support]
    rfl
  rw [h]
  exact finiteTypeSheavesRestriction_isLocalization_of_essSurj j

end Quillen.CoherentScheme
