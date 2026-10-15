/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Basic
public import Quillen.Resolution.InheritedQ
public import Quillen.KTheory.Map.HomotopyEquivalence

/-!
# Quillen's length-one resolution theorem

For a full inherited exact subcategory closed under extensions and kernels of
admissible epimorphisms, actual resolutions of length at most one imply that
the canonical inclusion is a homotopy equivalence on Q-classifying spaces and
an isomorphism on every nonnegative K-group. All comma contractions are
constructed in the preceding modules.

This is Weibel, *The K-book*, V.3.1.1. The unrestricted finite-resolution
statement additionally needs resolution-length filtration and union passage;
it is not silently claimed by the theorem in this module.
-/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Quillen.Resolution
variable {C : Type u} [SmallCategory C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (P : ObjectProperty C)
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [E.IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]

section AdmissibleSubobjects
variable [E.IsAdmissibleSubobjectClosed P]

/-- Resolution under admissible-subobject closure and actual covers. -/
def classifyingHomotopyEquivOfCovers (h : ∀ M, Nonempty (Cover E P M)) :
    ContinuousMap.HomotopyEquiv (ExactSubcategory.exactStructure E P).KSpace E.KSpace :=
  (inheritedQClassifyingHomotopyEquiv E P).trans (fullQClassifyingHomotopyEquiv E P h)

/-- The resulting forward map is exactly the original Q-inclusion. -/
@[simp] theorem classifyingHomotopyEquivOfCovers_toFun (h : ∀ M, Nonempty (Cover E P M)) :
    (classifyingHomotopyEquivOfCovers E P h).toFun =
      (classifyingSpaceMap (exactInclusion E P).mapQ).hom := by
  change (classifyingSpaceMap (fullQInclusion E P)).hom.comp
    (classifyingSpaceMap (inheritedToFullQ E P)).hom = _
  rw [← TopCat.hom_comp, ← classifyingSpaceMap_comp, inheritedToFullQ_comp]

/-- Normalization changes only the chosen zero basepoint, by the actual
natural isomorphism. The forward map is the one defining the canonical K-map. -/
def normalizedClassifyingHomotopyEquivOfCovers (h : ∀ M, Nonempty (Cover E P M)) :
    ContinuousMap.HomotopyEquiv (ExactSubcategory.exactStructure E P).KSpace E.KSpace :=
  TheoremA.homotopyEquivWithMap (classifyingHomotopyEquivOfCovers E P h)
    (classifyingSpaceMap (exactInclusion E P).normalizedQ).hom (by
      rw [classifyingHomotopyEquivOfCovers_toFun]
      exact ⟨classifyingSpaceNaturalTransformationHomotopy
        (rebaseFunctorIso (exactInclusion E P).mapQ
          (Q.of _ _ (0 : P.FullSubcategory)) (Q.of _ _ (0 : C))
          (E.qIsoOfIso (exactInclusion E P).toFunctor.mapZeroObject)).inv⟩)

/-- Every nonnegative canonical K-map is bijective under actual covers and
admissible-subobject closure. -/
theorem inclusionKMap_bijective_of_covers (h : ∀ M, Nonempty (Cover E P M)) (n : ℕ) :
    Function.Bijective (inclusionKMap E P n) :=
  (exactInclusion E P).KMap_bijective_of_homotopyEquiv
    (normalizedClassifyingHomotopyEquivOfCovers E P h) rfl n

end AdmissibleSubobjects

variable [E.IsKernelClosed P]

/-- Quillen's length-one resolution theorem on actual Q-classifying spaces. -/
def classifyingHomotopyEquivOfLengthOne (h : ∀ X, E.ResolutionLength P 1 X) :
    ContinuousMap.HomotopyEquiv (ExactSubcategory.exactStructure E P).KSpace E.KSpace := by
  letI := E.admissibleSubobjectClosed_of_resolutionLength_one P h
  exact classifyingHomotopyEquivOfCovers E P (fun X => by
    obtain ⟨R, _⟩ := h X
    obtain ⟨Y, p, hY, hp⟩ := R.presentation
    exact ⟨⟨Y, hY, p, hp⟩⟩)

@[simp] theorem classifyingHomotopyEquivOfLengthOne_toFun
    (h : ∀ X, E.ResolutionLength P 1 X) :
    (classifyingHomotopyEquivOfLengthOne E P h).toFun =
      (classifyingSpaceMap (exactInclusion E P).mapQ).hom := by
  let := E.admissibleSubobjectClosed_of_resolutionLength_one P h
  exact classifyingHomotopyEquivOfCovers_toFun E P _

/-- All-degree Quillen resolution with a length-one bound. No categorical
contraction, inverse map, or K-group equivalence is assumed in the hypotheses. -/
theorem inclusionKMap_bijective_of_length_one
    (h : ∀ X, E.ResolutionLength P 1 X) (n : ℕ) :
    Function.Bijective (inclusionKMap E P n) := by
  let := E.admissibleSubobjectClosed_of_resolutionLength_one P h
  apply inclusionKMap_bijective_of_covers E P _ n
  intro X
  obtain ⟨R, _⟩ := h X
  obtain ⟨Y, p, hY, hp⟩ := R.presentation
  exact ⟨⟨Y, hY, p, hp⟩⟩

/-- The actual K-group equivalence retains the canonical inclusion as its
forward homomorphism. -/
def KEquivOfLengthOne (h : ∀ X, E.ResolutionLength P 1 X) (n : ℕ) :
    (ExactSubcategory.exactStructure E P).K n ≃* E.K n :=
  MulEquiv.ofBijective (inclusionKMap E P n) (inclusionKMap_bijective_of_length_one E P h n)

/-- The underlying monoid homomorphism of this K-equivalence. -/
@[simp] theorem KEquivOfLengthOne_coe (h : ∀ X, E.ResolutionLength P 1 X) (n : ℕ) :
    (↑(KEquivOfLengthOne E P h n) : (ExactSubcategory.exactStructure E P).K n →* E.K n) =
        inclusionKMap E P n := rfl


end Quillen.Resolution
