/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.ClassifyingSpace.GroupCompletionTranslation
public import Quillen.Topology.LocalCoefficients.HomotopyEquivalence

/-!
# Local-coefficient homology of translations on categorical group completion

The two coordinate translations on the actual realized `S⁻¹S` are homotopy
equivalences, so they preserve every target local system. This result concerns
the categorical completion itself. It does not assert an all-local-system
homology equivalence for the action on a pre-completion telescope.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace Quillen.GroupCompletion.Localization

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The original first-coordinate translation preserves every target local system. -/
theorem isIso_firstTranslation_localHomology (s : C)
    (A : LocalCoefficients.System.{max u v, max u v}
      (ClassifyingSpace (Localization C C))) (n : ℕ) :
    IsIso (LocalCoefficients.pushforwardHomologyMap
      (classifyingSpaceMap (firstTranslation s)).hom A n) :=
  LocalCoefficients.isIso_pushforwardHomologyMap_of_homotopyEquiv
    (translationClassifyingHomotopyEquiv s) A n

/-- The original second-coordinate translation also preserves arbitrary local systems. -/
theorem isIso_secondTranslation_localHomology (s : C)
    (A : LocalCoefficients.System.{max u v, max u v}
      (ClassifyingSpace (Localization C C))) (n : ℕ) :
    IsIso (LocalCoefficients.pushforwardHomologyMap
      (classifyingSpaceMap (secondTranslation s)).hom A n) :=
  LocalCoefficients.isIso_pushforwardHomologyMap_of_homotopyEquiv
    (translationClassifyingHomotopyEquiv s).symm A n

end Quillen.GroupCompletion.Localization
