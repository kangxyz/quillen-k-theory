import Quillen.Localization.Serre.StructuredTransitionReduction
import Quillen.Localization.Serre.AuxiliaryStructuredTransition
import Quillen.Localization.Serre.AuxiliaryBaseChangeEquivalence

/-!
# Assembling structured transitions from the filtered comparator equivalences

The genuine mono/epi squares and quotient-arrow lifting do all the algebra.
This final assembly is kept separate from the filtered realization theorem
which must supply the map-preserving comparator equivalences.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
namespace Quillen.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts quotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

variable
  (E : ∀ N : C, ContinuousMap.HomotopyEquiv (ClassifyingSpace (AuxiliaryKernel P N))
    (ClassifyingSpace (IsoStructuredComma P ((quotientMapQ P).obj
      (Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation N)))))
  (hE : ∀ N, (E N).toFun = (classifyingSpaceMap (auxiliaryToIsoStructured P N)).hom)

/-- Composing with the already proved isomorphism-comma inclusion gives the
full structured-comma comparison, with its actual map retained. -/
def fullAuxiliaryStructuredEquiv (N : C) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (AuxiliaryKernel P N))
      (ClassifyingSpace (StructuredArrow ((quotientMapQ P).obj
        (Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation N))
          (quotientMapQ P))) :=
  (E N).trans (isoStructuredInclusionClassifyingHomotopyEquiv P _)

include hE

lemma fullAuxiliaryStructuredEquiv_toFun (N : C) :
    (fullAuxiliaryStructuredEquiv P E N).toFun =
      (classifyingSpaceMap (auxiliaryToIsoStructured P N ⋙ isoStructuredInclusion P _)).hom := by
  change (isoStructuredInclusionClassifyingHomotopyEquiv P _).toFun.comp (E N).toFun = _
  rw [hE, isoStructuredInclusionClassifyingHomotopyEquiv_toFun,
    classifyingSpaceMap_comp, TopCat.hom_comp]
  rfl

/-- The monomorphic transition square gives the actual mono transition equivalence. -/
theorem structuredInflationTransitionIsHE {M N : C} (i : M ⟶ N) [Mono i] :
    TheoremB.StructuredTransitionIsHE (quotientMapQ P) ((quotientMapQ P).map (Q.inflationArrow i)) := by
  let s := fullAuxiliaryStructuredEquiv P E N
  let t := (auxiliaryBaseChangeClassifyingHomotopyEquiv P i).trans (fullAuxiliaryStructuredEquiv P E M)
  let f := TheoremB.structuredTransitionMap (quotientMapQ P) ((quotientMapQ P).map (Q.inflationArrow i))
  have h : (f.comp s.toFun).Homotopic t.toFun := by
    have H := (classifyingSpaceNaturalTransformationHomotopy (auxiliaryStructuredInflationSquare P i)).symm
    refine ⟨H.cast ?_ ?_⟩
    · simp only [f, s, fullAuxiliaryStructuredEquiv_toFun P E hE,
        TheoremB.structuredTransitionMap, TheoremB.structuredTransition,
        classifyingSpaceMap_comp, TopCat.hom_comp, ContinuousMap.comp_assoc]
    · change _ = (fullAuxiliaryStructuredEquiv P E M).toFun.comp
        (auxiliaryBaseChangeClassifyingHomotopyEquiv P i).toFun
      rw [fullAuxiliaryStructuredEquiv_toFun P E hE,
        auxiliaryBaseChangeClassifyingHomotopyEquiv_toFun]
      simp only [classifyingSpaceMap_comp, TopCat.hom_comp, ContinuousMap.comp_assoc]
  exact ⟨TheoremA.homotopyEquivOfTriangle s t f h, rfl⟩

/-- The reversed-epimorphism square gives the actual epi transition equivalence. -/
theorem structuredSurjectionTransitionIsHE {M N : C} (p : M ⟶ N) [Epi p] :
    TheoremB.StructuredTransitionIsHE (quotientMapQ P) ((quotientMapQ P).map (Q.surjectionArrow p)) := by
  let s := (auxiliaryBaseChangeClassifyingHomotopyEquiv P p).trans (fullAuxiliaryStructuredEquiv P E M)
  let t := fullAuxiliaryStructuredEquiv P E N
  let f := TheoremB.structuredTransitionMap (quotientMapQ P) ((quotientMapQ P).map (Q.surjectionArrow p))
  have h : (f.comp s.toFun).Homotopic t.toFun := by
    have H := (classifyingSpaceNaturalTransformationHomotopy (auxiliaryStructuredSurjectionSquare P p)).symm
    refine ⟨H.cast ?_ ?_⟩
    · change _ = f.comp ((fullAuxiliaryStructuredEquiv P E M).toFun.comp
        (auxiliaryBaseChangeClassifyingHomotopyEquiv P p).toFun)
      rw [fullAuxiliaryStructuredEquiv_toFun P E hE,
        auxiliaryBaseChangeClassifyingHomotopyEquiv_toFun]
      simp only [f, TheoremB.structuredTransitionMap, TheoremB.structuredTransition,
        classifyingSpaceMap_comp, TopCat.hom_comp, ContinuousMap.comp_assoc]
    · exact (fullAuxiliaryStructuredEquiv_toFun P E hE N).symm
  exact ⟨TheoremA.homotopyEquivOfTriangle s t f h, rfl⟩

/-- Once the filtered realization theorem supplies the comparator HEs,
all raw structured transitions follow from the checked mono/epi squares and
actual fixed-target quotient-span lifting. -/
theorem structuredTransitions_of_auxiliaryComparatorEquivalences :
    TheoremB.StructuredTransitionHomotopyEquivalences (quotientMapQ P) :=
  structuredTransitions_of_mapped_mono_epi P
    (structuredInflationTransitionIsHE P E hE) (structuredSurjectionTransitionIsHE P E hE)

end Quillen.SerreLocalization
