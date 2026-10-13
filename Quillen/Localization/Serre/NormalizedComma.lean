/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Localization.Serre.LocalizationComma
public import Quillen.Localization.Serre.BasedFiberComparison
public import Quillen.CategoryTheory.TheoremB.FunctorIso

/-! The zero-comma equivalence for the exact normalized functors underlying KMap. -/
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

/-- The canonical natural isomorphism from the raw quotient to its zero normalization. -/
def quotientNormalizedIso : quotientMapQ P ≅ quotientNormalizedQ P :=
  rebaseFunctorIso (quotientMapQ P) (abelianExactStructure C).qZero
    (quotientExactStructure P).qZero
    ((quotientExactStructure P).qIsoOfIso (quotientExactFunctor P).toFunctor.mapZeroObject)

/-- The canonical natural isomorphism from the raw inclusion to its zero normalization. -/
def inclusionNormalizedIso : Devissage.mapQ P ≅ inclusionNormalizedQ P :=
  rebaseFunctorIso (Devissage.mapQ P) (Devissage.subcategoryExactStructure P).qZero
    (abelianExactStructure C).qZero
    ((abelianExactStructure C).qIsoOfIso (Devissage.exactInclusion P).toFunctor.mapZeroObject)

/-- The costructured-arrow category of Q-arrows from the image of the normalized quotient
functor to the quotient Q-zero object. -/
abbrev NormalizedZeroComma :=
  CostructuredArrow (quotientNormalizedQ P) (quotientExactStructure P).qZero

/-- The normalized nullhomotopy determines the exact normalized zero-comma comparison. -/
def normalizedSerreToZeroComma :
    (Devissage.subcategoryExactStructure P).QCategory ⥤ NormalizedZeroComma P :=
  (inclusionNormalizedQ P).toCostructuredArrow (quotientNormalizedQ P) _
    (fun X ↦ (normalizedQuotientInclusionZeroIso P).hom.app X)
    (fun f ↦ by simpa using (normalizedQuotientInclusionZeroIso P).hom.naturality f)

/-- Normalization transports the previously proved equivalence by actual
natural isomorphisms, retaining the normalized structure arrows. -/
def normalizedSerreToZeroCommaIso :
    serreToZeroComma P ⋙ (CostructuredArrow.mapNatIso
      (T := (quotientExactStructure P).qZero) (quotientNormalizedIso P)).functor ≅
      normalizedSerreToZeroComma P :=
  NatIso.ofComponents (fun X ↦ CostructuredArrow.isoMk ((inclusionNormalizedIso P).app X)
    (by exact ((quotientExactStructure P).qHom_subsingleton_of_isZero _ _
      (isZero_zero _)).elim _ _)) (by
    intro X Y f
    apply CostructuredArrow.hom_ext
    exact (inclusionNormalizedIso P).hom.naturality f)

instance normalizedSerreToZeroComma_isEquivalence :
    (normalizedSerreToZeroComma P).IsEquivalence :=
  Functor.isEquivalence_of_iso (normalizedSerreToZeroCommaIso P)

/-- The normalized Serre comparison is a genuine categorical equivalence. -/
def normalizedZeroCommaEquivalence :
    (Devissage.subcategoryExactStructure P).QCategory ≌ NormalizedZeroComma P :=
  (normalizedSerreToZeroComma P).asEquivalence

/-- Its actual realized homotopy equivalence uses exactly the normalized comparison. -/
def normalizedZeroCommaClassifyingHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (Devissage.subcategoryExactStructure P).KSpace
      (ClassifyingSpace (NormalizedZeroComma P)) :=
  equivalenceClassifyingHomotopyEquiv (normalizedZeroCommaEquivalence P)

@[simp] theorem normalizedZeroCommaClassifyingHomotopyEquiv_toFun :
    (normalizedZeroCommaClassifyingHomotopyEquiv P).toFun =
      (classifyingSpaceMap (normalizedSerreToZeroComma P)).hom := rfl

@[simp] theorem normalizedSerreToZeroComma_projection :
    normalizedSerreToZeroComma P ⋙ CostructuredArrow.proj (quotientNormalizedQ P)
      (quotientExactStructure P).qZero = inclusionNormalizedQ P := rfl

@[simp] theorem normalizedSerreToZeroComma_transformation :
    Functor.whiskerLeft (normalizedSerreToZeroComma P)
      (TheoremB.commaTransformation (quotientNormalizedQ P) (quotientExactStructure P).qZero) =
      (normalizedQuotientInclusionZeroIso P).hom := rfl

/-- The complete normalized comma homotopy is the already-chosen based
localization nullhomotopy, including every value of its path coordinate. -/
theorem normalizedSerreToZeroComma_nullhomotopy (t : unitInterval)
    (x : (Devissage.subcategoryExactStructure P).KSpace) :
    TheoremB.commaNullhomotopy (quotientNormalizedQ P) (quotientExactStructure P).qZero
      (t, classifyingSpaceMap (normalizedSerreToZeroComma P) x) =
      normalizedQuotientInclusionHomotopy P (t, x) := by
  change classifyingSpaceNaturalTransformationHomotopy
    (TheoremB.commaTransformation (quotientNormalizedQ P) (quotientExactStructure P).qZero)
    (t, classifyingSpaceMap (normalizedSerreToZeroComma P) x) =
    classifyingSpaceNaturalTransformationHomotopy (normalizedQuotientInclusionZeroIso P).hom (t, x)
  rw [← classifyingSpaceNaturalTransformationHomotopy_whiskerLeft,
    normalizedSerreToZeroComma_transformation]

/-- The normalized zero-comma route gives exactly the existing based fiber
comparison, not merely some homotopic map into the same unbased fiber. -/
theorem normalizedSerreToZeroComma_fiberComparison :
    (TheoremB.fiberComparison (quotientNormalizedQ P) (quotientExactStructure P).qZero).comp
      (classifyingSpaceMap (normalizedSerreToZeroComma P)).hom =
      basedLocalizationFiberComparison P := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · change classifyingSpaceMap (CostructuredArrow.proj (quotientNormalizedQ P)
        (quotientExactStructure P).qZero) (classifyingSpaceMap (normalizedSerreToZeroComma P) x) =
      classifyingSpaceMap (inclusionNormalizedQ P) x
    have h := classifyingSpaceMap_comp (normalizedSerreToZeroComma P)
      (CostructuredArrow.proj (quotientNormalizedQ P) (quotientExactStructure P).qZero)
    exact ConcreteCategory.congr_hom h.symm x
  · apply ContinuousMap.ext
    intro t
    exact normalizedSerreToZeroComma_nullhomotopy P t x

/-- The genuine raw quotient transition hypothesis transfers to the exact
normalized quotient functor used by KMap. -/
theorem normalizedQuotient_transitions
    (h : TheoremB.TransitionHomotopyEquivalences (quotientMapQ P)) :
    TheoremB.TransitionHomotopyEquivalences (quotientNormalizedQ P) :=
  TheoremB.transitionHomotopyEquivalences_of_natIso (quotientNormalizedIso P) h

end Quillen.SerreLocalization
