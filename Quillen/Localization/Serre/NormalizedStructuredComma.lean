/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Localization.Serre.NormalizedComma
public import Quillen.CategoryTheory.TheoremB.StructuredWeakTransport
public import Quillen.CategoryTheory.TheoremB.StructuredFunctorIso
public import Quillen.CategoryTheory.TheoremB.StructuredIsoHomotopy
public import Quillen.Topology.ClassifyingSpace.FunctorChain

/-! The normalized structured zero-comma inclusion retains the exact
functors used by the canonical K maps. -/
@[expose] public section

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts quotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

/-- The structured-arrow category of Q-arrows from the quotient Q-zero object to the image of
the normalized quotient functor. -/
abbrev NormalizedZeroStructuredComma :=
  StructuredArrow (quotientExactStructure P).qZero (quotientNormalizedQ P)

/-- The functor from the Serre subcategory Q-category to the normalized structured zero-comma
category, using the inverse of the natural zero comparison as its structure arrow. -/
def normalizedSerreToZeroStructuredComma :
    (CategoryTheory.ObjectProperty.subcategoryExactStructure P).QCategory ⥤
      NormalizedZeroStructuredComma P :=
  (inclusionNormalizedQ P).toStructuredArrow _ (quotientNormalizedQ P)
    (fun X ↦ (normalizedQuotientInclusionZeroIso P).inv.app X)
    (fun f ↦ by simpa using ((normalizedQuotientInclusionZeroIso P).inv.naturality f).symm)

/-- The natural isomorphism comparing the raw structured zero-comma inclusion, transported along
the quotient normalization, with `normalizedSerreToZeroStructuredComma P`. -/
def normalizedSerreToZeroStructuredCommaIso :
    serreToZeroStructuredComma P ⋙ (StructuredArrow.mapNatIso
      (S := (quotientExactStructure P).qZero) (quotientNormalizedIso P)).functor ≅
      normalizedSerreToZeroStructuredComma P :=
  NatIso.ofComponents (fun X ↦ StructuredArrow.isoMk ((inclusionNormalizedIso P).app X)
    (by
      apply (cancel_mono ((normalizedQuotientInclusionZeroIso P).hom.app X)).1
      exact ((quotientExactStructure P).qHom_subsingleton_of_isZero _ _
        (isZero_zero _)).elim _ _)) (by
    intro X Y f
    apply StructuredArrow.hom_ext
    exact (inclusionNormalizedIso P).hom.naturality f)

/-- The already proved raw structured inclusion transports by actual natural
isomorphisms, retaining the normalized inclusion as its forward map. -/
def normalizedZeroStructuredCommaClassifyingHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (CategoryTheory.ObjectProperty.subcategoryExactStructure P).KSpace
      (ClassifyingSpace (NormalizedZeroStructuredComma P)) :=
  TheoremA.homotopyEquivWithMap
    ((zeroStructuredCommaClassifyingHomotopyEquiv P).trans
      (equivalenceClassifyingHomotopyEquiv (StructuredArrow.mapNatIso
        (S := (quotientExactStructure P).qZero) (quotientNormalizedIso P))))
    (classifyingSpaceMap (normalizedSerreToZeroStructuredComma P)).hom
    (by
      have H := classifyingSpaceNaturalTransformationHomotopy
        (normalizedSerreToZeroStructuredCommaIso P).inv
      exact ⟨H.cast rfl (by simp only [classifyingSpaceMap_comp, TopCat.hom_comp]; rfl)⟩)

@[simp] theorem normalizedZeroStructuredCommaClassifyingHomotopyEquiv_toFun :
    (normalizedZeroStructuredCommaClassifyingHomotopyEquiv P).toFun =
      (classifyingSpaceMap (normalizedSerreToZeroStructuredComma P)).hom := rfl

@[simp] theorem normalizedSerreToZeroStructuredComma_projection :
    normalizedSerreToZeroStructuredComma P ⋙ StructuredArrow.proj
      (quotientExactStructure P).qZero (quotientNormalizedQ P) = inclusionNormalizedQ P := rfl

@[simp] theorem normalizedSerreToZeroStructuredComma_transformation :
    Functor.whiskerLeft (normalizedSerreToZeroStructuredComma P)
      (TheoremB.structuredCommaTransformation (quotientNormalizedQ P)
        (quotientExactStructure P).qZero) = (normalizedQuotientInclusionZeroIso P).inv := rfl

/-- The source-zero route uses precisely the reversed inverse of the
normalized natural isomorphism, not a separately chosen nullhomotopy. -/
theorem normalizedSerreToZeroStructuredComma_nullhomotopy (t : unitInterval)
    (x : (CategoryTheory.ObjectProperty.subcategoryExactStructure P).KSpace) :
    TheoremB.structuredCommaNullhomotopy (quotientNormalizedQ P)
      (quotientExactStructure P).qZero
      (t, classifyingSpaceMap (normalizedSerreToZeroStructuredComma P) x) =
      TheoremB.naturalIsoInverseNullhomotopy (inclusionNormalizedQ P)
        (quotientNormalizedQ P) (quotientExactStructure P).qZero
        (normalizedQuotientInclusionZeroIso P) (t, x) := by
  change classifyingSpaceNaturalTransformationHomotopy
    (TheoremB.structuredCommaTransformation (quotientNormalizedQ P)
      (quotientExactStructure P).qZero)
    (unitInterval.symm t, classifyingSpaceMap (normalizedSerreToZeroStructuredComma P) x) =
    classifyingSpaceNaturalTransformationHomotopy (normalizedQuotientInclusionZeroIso P).inv
      (unitInterval.symm t, x)
  rw [← classifyingSpaceNaturalTransformationHomotopy_whiskerLeft,
    normalizedSerreToZeroStructuredComma_transformation]

theorem normalizedQuotient_structuredTransitions
    (h : TheoremB.StructuredTransitionHomotopyEquivalences (quotientMapQ P)) :
    TheoremB.StructuredTransitionHomotopyEquivalences (quotientNormalizedQ P) :=
  TheoremB.structuredTransitionHomotopyEquivalences_of_natIso (quotientNormalizedIso P) h

/-- The complete normalized structured comparison into the actual fiber. -/
def normalizedStructuredFiberComparison :
    C((CategoryTheory.ObjectProperty.subcategoryExactStructure P).KSpace,
      NormalizedLocalizationFiber P) :=
  (TheoremB.structuredFiberComparison (quotientNormalizedQ P)
    (quotientExactStructure P).qZero).comp
      (classifyingSpaceMap (normalizedSerreToZeroStructuredComma P)).hom

theorem normalizedStructuredFiberComparison_eq_lift :
    normalizedStructuredFiberComparison P =
      HomotopyFiber.lift (classifyingSpaceMap (quotientNormalizedQ P)).hom
        (quotientExactStructure P).kBasepoint
        (classifyingSpaceMap (inclusionNormalizedQ P)).hom
        (TheoremB.naturalIsoInverseNullhomotopy (inclusionNormalizedQ P)
          (quotientNormalizedQ P) (quotientExactStructure P).qZero
          (normalizedQuotientInclusionZeroIso P)) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · exact ConcreteCategory.congr_hom
      (classifyingSpaceMap_comp (normalizedSerreToZeroStructuredComma P)
        (StructuredArrow.proj (quotientExactStructure P).qZero (quotientNormalizedQ P))).symm x
  · apply ContinuousMap.ext
    intro t
    exact normalizedSerreToZeroStructuredComma_nullhomotopy P t x

/-- Actual two-parameter coherence connects the chosen direct nullhomotopy
with the normalized structured-comma comparison. -/
def normalizedStructuredFiberComparisonHomotopy :
    (basedLocalizationFiberComparison P).Homotopy (normalizedStructuredFiberComparison P) :=
  (TheoremB.naturalIsoFiberLiftHomotopy (inclusionNormalizedQ P)
    (quotientNormalizedQ P) (quotientExactStructure P).qZero
    (normalizedQuotientInclusionZeroIso P)).cast rfl
      (normalizedStructuredFiberComparison_eq_lift P).symm

/-- The coherence fixes the original zero basepoint at every time, not merely
its source coordinate or the endpoints of its path coordinate. -/
theorem normalizedStructuredFiberComparisonHomotopy_based (s : unitInterval) :
    normalizedStructuredFiberComparisonHomotopy P
      (s, (CategoryTheory.ObjectProperty.subcategoryExactStructure P).kBasepoint) =
        normalizedFiberBasepoint P := by
  apply Subtype.ext
  apply Prod.ext
  · exact (CategoryTheory.ObjectProperty.exactInclusion P).normalizedQ_map_point
  · apply ContinuousMap.ext
    intro t
    exact TheoremB.naturalIsoInverseHomotopy_vertex_of_subsingleton
      (normalizedQuotientInclusionZeroIso P).symm
      (CategoryTheory.ObjectProperty.subcategoryExactStructure P).qZero (quotientExactStructure
        P).qZero
      rfl (normalizedComposite_obj_zero P)
      (fun Y ↦ (quotientExactStructure P).qHom_subsingleton_of_isZero _ _ (isZero_zero _)) s t

end Quillen.SerreLocalization
