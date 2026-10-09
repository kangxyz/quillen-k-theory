import Quillen.Scheme.Coherent.Localization.Fullness

/-!
# From actual coherent object extension to the geometric Serre localization

Faithfulness and fullness have been proved for the canonical functor from
coherent sheaves modulo the actual support category. This file isolates the
last categorical step: essential surjectivity of actual open restriction
makes that quotient functor an equivalence and proves the localization
universal property for the original restriction functor.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Quillen.CoherentScheme

variable {U X : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian U]
  (j : U ⟶ X) [IsOpenImmersion j] [(coherentRestriction j).EssSurj]

/-- Actual coherent object extension descends to essential surjectivity of
the canonical functor from the support quotient. -/
theorem quotientCoherentRestriction_essSurj_of_restriction :
    (quotientCoherentRestriction j).EssSurj where
  mem_essImage A := by
    obtain ⟨M, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (coherentRestriction j) A
    refine ⟨(coherentSupportedAway j).isoModSerre.Q.obj M, ⟨?_⟩⟩
    exact (quotientCoherentRestriction_facIso j).app M ≪≫ e

/-- The full, faithful actual quotient functor is an equivalence once
actual coherent extension is known. -/
theorem quotientCoherentRestriction_isEquivalence_of_essSurj :
    (quotientCoherentRestriction j).IsEquivalence where
  essSurj := quotientCoherentRestriction_essSurj_of_restriction j

/-- The original geometric restriction is localization by actual coherent
support, using the equivalence of its constructed quotient. -/
theorem coherentRestriction_isLocalization_of_essSurj :
    (coherentRestriction j).IsLocalization (coherentSupportedAway j).isoModSerre := by
  let := quotientCoherentRestriction_isEquivalence_of_essSurj j
  exact Functor.IsLocalization.of_equivalence_target
    (coherentSupportedAway j).isoModSerre.Q (coherentSupportedAway j).isoModSerre
    (coherentRestriction j) (quotientCoherentRestriction j).asEquivalence
    (quotientCoherentRestriction_facIso j)

/-- Equivalently, actual open restriction is localization by its kernel. -/
theorem coherentRestriction_isLocalization_kernel_of_essSurj :
    (coherentRestriction j).IsLocalization (coherentRestriction j).kernel.isoModSerre := by
  have h : (coherentRestriction j).kernel.isoModSerre =
      (coherentSupportedAway j).isoModSerre := by
    funext M N f
    apply propext
    change ((coherentRestriction j).kernel (kernel f) ∧
      (coherentRestriction j).kernel (cokernel f)) ↔ _
    rw [coherentRestriction_kernel_eq_support]
    rfl
  rw [h]
  exact coherentRestriction_isLocalization_of_essSurj j

end Quillen.CoherentScheme
