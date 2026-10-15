/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionAcyclicEvaluation
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionOpenComparison
public import Quillen.Waldhausen.SmallModel.Composition

/-!
# Original supported-section comparison with geometric relative acyclics

The actual exact equivalence is lifted to the original common universe. Its inherited-zero
identity supplies the same forward Model arrow, and its actual categorical inverse proves
complete levelwise weakness. The literal support-inclusion square is retained for the whole
null-track and cone comparison; no full-open endpoint identification is inferred.
-/
@[expose] public section

open Quillen.Waldhausen
open Quillen.Waldhausen.Fibration
open Quillen.Waldhausen.IteratedS

noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
open Waldhausen Waldhausen.Fibration Waldhausen.IteratedS
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedFlatAffineOriginalEvaluation
  boundedFlatAffineSupportedSectionEquivalence boundedFlatAffineSupportedEvaluation

/-- The original supported-to-acyclic equivalence with the actual common-universe lifting. -/
def boundedFlatAffineSupportedSectionAcyclicSmallEquivalence :
    BoundedFlatAffineSupportedSections j ≌
      SmallModel (AcyclicCategory (boundedFlatPerfectOpenNested j)) :=
  (boundedFlatAffineSupportedSectionAcyclicEquivalence j).trans AsSmall.equiv

/-- The actual forward common-universe evaluation is exact. -/
theorem boundedFlatAffineSupportedSectionAcyclicSmallEquivalence_exact :
    IsExact (boundedFlatAffineSupportedSectionWaldhausen j).cof
      (boundedFlatAffineSupportedSectionWaldhausen j).weq
      (acyclicStructure (boundedFlatPerfectOpenNested j)).smallModel.cof
      (acyclicStructure (boundedFlatPerfectOpenNested j)).smallModel.weq
      (boundedFlatAffineSupportedSectionAcyclicSmallEquivalence j).functor := by
  change IsExact _ _ _ _ (boundedFlatAffineSupportedSectionAcyclicEvaluation j ⋙ AsSmall.up)
  exact (boundedFlatAffineSupportedSectionAcyclicEvaluation_exact j).comp
    (acyclicStructure (boundedFlatPerfectOpenNested j)).smallModel_up_exact

/-- The unchanged actual inverse is exact for the same original inherited fine classes. -/
theorem boundedFlatAffineSupportedSectionAcyclicSmallEquivalence_inverse_exact :
    IsExact (acyclicStructure (boundedFlatPerfectOpenNested j)).smallModel.cof
      (acyclicStructure (boundedFlatPerfectOpenNested j)).smallModel.weq
      (boundedFlatAffineSupportedSectionWaldhausen j).cof
      (boundedFlatAffineSupportedSectionWaldhausen j).weq
      (boundedFlatAffineSupportedSectionAcyclicSmallEquivalence j).inverse :=
  (acyclicStructure (boundedFlatPerfectOpenNested j)).smallModel_down_exact.comp
    (boundedFlatAffineSupportedSectionAcyclicEquivalence_inverse_exact j)

/-- The actual supported evaluation retains the inherited geometric acyclic zero literally. -/
def boundedFlatAffineSupportedSectionAcyclicModelMap :
    boundedFlatAffineSupportedSectionModel j ⟶
      modelOf (acyclicStructure (boundedFlatPerfectOpenNested j)) where
  functor := (boundedFlatAffineSupportedSectionAcyclicSmallEquivalence j).functor
  exact := boundedFlatAffineSupportedSectionAcyclicSmallEquivalence_exact j
  zero := congrArg AsSmall.up.obj (boundedFlatAffineSupportedSectionAcyclicEvaluation_zero j)

/-- The same forward Model arrow induces the actual original supported-acyclic prespectrum map. -/
def boundedFlatAffineSupportedSectionAcyclicPrespectrumMap :
    prespectrum (boundedFlatAffineSupportedSectionModel j) ⟶
      originalPrespectrum (acyclicStructure (boundedFlatPerfectOpenNested j)) :=
  prespectrumMap (boundedFlatAffineSupportedSectionAcyclicModelMap j)

/-- The two unchanged original support-inclusion routes agree as actual Model arrows. -/
theorem boundedFlatAffineSupportedSectionAcyclicModelMap_inclusion :
    boundedFlatAffineSupportedSectionForgetModelMap j ≫
        boundedFlatAffineSectionEvaluationModelMap R =
      boundedFlatAffineSupportedSectionAcyclicModelMap j ≫
        modelMap _ _ (acyclicInclusion_exact (boundedFlatPerfectOpenNested j)) rfl := by
  apply Model.Hom.ext
  exact smallModelFunctor_square (boundedFlatAffineSectionSupported j).ι
    (boundedFlatAffineOriginalEvaluation R) (boundedFlatAffineSupportedSectionAcyclicEvaluation j)
    (acyclicInclusion (boundedFlatPerfectOpenNested j))
    (boundedFlatAffineSupportedSectionAcyclicEvaluation_inclusion j).symm

/-- The literal original inclusion square survives unchanged on actual prespectra. -/
theorem boundedFlatAffineSupportedSectionAcyclicPrespectrumMap_inclusion :
    boundedFlatAffineSupportedSectionForgetPrespectrumMap j ≫
        boundedFlatAffineSectionEvaluationPrespectrumMap R =
      boundedFlatAffineSupportedSectionAcyclicPrespectrumMap j ≫
        acyclicInclusionPrespectrumMap (boundedFlatPerfectOpenNested j) := by
  exact (prespectrumFunctor.map_comp _ _).symm.trans
    ((congrArg prespectrumFunctor.map
      (boundedFlatAffineSupportedSectionAcyclicModelMap_inclusion j)).trans
        (prespectrumFunctor.map_comp _ _))

/-- Every original level map is a complete weak equivalence, including every component. -/
theorem boundedFlatAffineSupportedSectionAcyclic_level_isWeakHomotopyEquivalence (n : ℕ) :
    IsWeakHomotopyEquivalence ((boundedFlatAffineSupportedSectionAcyclicPrespectrumMap j).map n) :=
  ExactModelEquivalence.level_isWeakHomotopyEquivalence
    (V := boundedFlatAffineSupportedSectionModel j)
    (W := modelOf (acyclicStructure (boundedFlatPerfectOpenNested j)))
    (boundedFlatAffineSupportedSectionAcyclicSmallEquivalence j)
    (boundedFlatAffineSupportedSectionAcyclicSmallEquivalence_exact j)
    (boundedFlatAffineSupportedSectionAcyclicSmallEquivalence_inverse_exact j)
    (boundedFlatAffineSupportedSectionAcyclicModelMap j).zero n

/-- The same original supported-acyclic comparison is stable in every signed degree. -/
theorem boundedFlatAffineSupportedSectionAcyclic_isStableEquivalence :
    LoopPrespectrum.IsStableEquivalence
      (boundedFlatAffineSupportedSectionAcyclicPrespectrumMap j) :=
  ExactModelEquivalence.isStableEquivalence
    (V := boundedFlatAffineSupportedSectionModel j)
    (W := modelOf (acyclicStructure (boundedFlatPerfectOpenNested j)))
    (boundedFlatAffineSupportedSectionAcyclicSmallEquivalence j)
    (boundedFlatAffineSupportedSectionAcyclicSmallEquivalence_exact j)
    (boundedFlatAffineSupportedSectionAcyclicSmallEquivalence_inverse_exact j)
    (boundedFlatAffineSupportedSectionAcyclicModelMap j).zero

end Quillen.PerfectComplexes
