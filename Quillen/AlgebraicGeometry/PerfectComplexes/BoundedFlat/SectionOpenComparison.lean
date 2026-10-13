/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionOpenEquivalence
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionOpenNull
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionSpectrumEquivalence
public import Quillen.Waldhausen.Fibration.Prespectrum

/-!
# Actual relative-open section evaluation on prespectra

Original evaluation, followed by its original common-universe inclusion, is exact in both
directions for the genuine relative-open weak structures. Its original chosen section zero
maps to the inherited geometric zero by the already proved fine evaluation equality. The same
forward Model map has whole two-sided inverse homotopies and is a complete weak equivalence
at every level. No identification with the full open-scheme endpoint is asserted.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
open Waldhausen Waldhausen.IteratedS
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedFlatAffineOriginalEvaluation

/-- The actual evaluation followed by original universe lifting preserves the relative classes. -/
theorem boundedFlatAffineSectionOpenSmallEquivalence_exact :
    IsExact (boundedFlatAffineSectionOpenWaldhausen j).cof
      (boundedFlatAffineSectionOpenWaldhausen j).weq
      (boundedFlatPerfectOpenWaldhausen j).smallModel.cof
      (boundedFlatPerfectOpenWaldhausen j).smallModel.weq
      (boundedFlatAffineSectionSmallEquivalence R).functor :=
  (boundedFlatAffineSectionOpenEvaluation_coarse_exact j).comp
    (boundedFlatPerfectOpenWaldhausen j).smallModel_up_exact

/-- The same original common-universe inverse is exact for the actual relative classes. -/
theorem boundedFlatAffineSectionOpenSmallEquivalence_inverse_exact :
    IsExact (boundedFlatPerfectOpenWaldhausen j).smallModel.cof
      (boundedFlatPerfectOpenWaldhausen j).smallModel.weq
      (boundedFlatAffineSectionOpenWaldhausen j).cof
      (boundedFlatAffineSectionOpenWaldhausen j).weq
      (boundedFlatAffineSectionSmallEquivalence R).inverse :=
  (boundedFlatPerfectOpenWaldhausen j).smallModel_down_exact.comp
    (boundedFlatAffineSectionOpenEquivalence_inverse_exact j)

/-- Original evaluation sends the unchanged section zero to the inherited geometric zero. -/
def boundedFlatAffineSectionOpenEvaluationModelMap :
    boundedFlatAffineSectionOpenModel j ⟶ modelOf (boundedFlatPerfectOpenWaldhausen j) where
  functor := (boundedFlatAffineSectionSmallEquivalence R).functor
  exact := boundedFlatAffineSectionOpenSmallEquivalence_exact j
  zero := (boundedFlatAffineSectionEvaluationModelMap R).zero

/-- The actual relative-open comparison retains the original evaluated section map. -/
def boundedFlatAffineSectionOpenEvaluationPrespectrumMap :
    prespectrum (boundedFlatAffineSectionOpenModel j) ⟶
      originalPrespectrum (boundedFlatPerfectOpenWaldhausen j) :=
  prespectrumMap (boundedFlatAffineSectionOpenEvaluationModelMap j)

/-- The actual fine/coarse square commutes for the unchanged section and geometric maps. -/
theorem boundedFlatAffineSectionOpenEvaluation_changeWeak :
    boundedFlatAffineSectionOpenPrespectrumMap j ≫
        boundedFlatAffineSectionOpenEvaluationPrespectrumMap j =
      boundedFlatAffineSectionEvaluationPrespectrumMap R ≫
        Fibration.changeWeakPrespectrumMap (boundedFlatPerfectOpenNested j) := by
  change prespectrumFunctor.map (boundedFlatAffineSectionOpenModelMap j) ≫
      prespectrumFunctor.map (boundedFlatAffineSectionOpenEvaluationModelMap j) =
    prespectrumFunctor.map (boundedFlatAffineSectionEvaluationModelMap R) ≫
      prespectrumFunctor.map (modelMap _ _
        (Fibration.changeWeak_exact (boundedFlatPerfectOpenNested j))
        (boundedFlatPerfectOpenNested j).zero_eq.symm)
  rw [← prespectrumFunctor.map_comp, ← prespectrumFunctor.map_comp]
  apply congrArg prespectrumFunctor.map
  apply Model.Hom.ext
  change 𝟭 _ ⋙ (boundedFlatAffineSectionSmallEquivalence R).functor =
    (boundedFlatAffineSectionSmallEquivalence R).functor ⋙ 𝟭 _
  rw [Functor.id_comp, Functor.comp_id]

/-- The actual inverse uses only canonical chosen-zero normalization of evaluation's inverse. -/
def boundedFlatAffineSectionOpenEvaluationInversePrespectrumMap :
    originalPrespectrum (boundedFlatPerfectOpenWaldhausen j) ⟶
      prespectrum (boundedFlatAffineSectionOpenModel j) :=
  prespectrumMap (ExactModelEquivalence.backward
    (V := boundedFlatAffineSectionOpenModel j)
    (W := modelOf (boundedFlatPerfectOpenWaldhausen j))
    (boundedFlatAffineSectionSmallEquivalence R)
    (boundedFlatAffineSectionOpenSmallEquivalence_inverse_exact j))

/-- The original categorical unit and inverse normalization give a whole left inverse track. -/
def boundedFlatAffineSectionOpenEvaluationLeftHomotopy : LoopPrespectrum.Homotopy
    (boundedFlatAffineSectionOpenEvaluationPrespectrumMap j ≫
      boundedFlatAffineSectionOpenEvaluationInversePrespectrumMap j)
    (𝟙 (prespectrum (boundedFlatAffineSectionOpenModel j))) :=
  ExactModelEquivalence.leftHomotopy
    (V := boundedFlatAffineSectionOpenModel j)
    (W := modelOf (boundedFlatPerfectOpenWaldhausen j))
    (boundedFlatAffineSectionSmallEquivalence R)
    (boundedFlatAffineSectionOpenSmallEquivalence_exact j)
    (boundedFlatAffineSectionOpenSmallEquivalence_inverse_exact j)
    (boundedFlatAffineSectionOpenEvaluationModelMap j).zero

/-- The unchanged categorical counit and the same normalization give the whole right track. -/
def boundedFlatAffineSectionOpenEvaluationRightHomotopy : LoopPrespectrum.Homotopy
    (boundedFlatAffineSectionOpenEvaluationInversePrespectrumMap j ≫
      boundedFlatAffineSectionOpenEvaluationPrespectrumMap j)
    (𝟙 (originalPrespectrum (boundedFlatPerfectOpenWaldhausen j))) :=
  ExactModelEquivalence.rightHomotopy
    (V := boundedFlatAffineSectionOpenModel j)
    (W := modelOf (boundedFlatPerfectOpenWaldhausen j))
    (boundedFlatAffineSectionSmallEquivalence R)
    (boundedFlatAffineSectionOpenSmallEquivalence_exact j)
    (boundedFlatAffineSectionOpenSmallEquivalence_inverse_exact j)
    (boundedFlatAffineSectionOpenEvaluationModelMap j).zero

/-- Every level of the same original forward relative-open comparison is completely weak. -/
theorem boundedFlatAffineSectionOpenEvaluation_level_isWeakHomotopyEquivalence (n : ℕ) :
    IsWeakHomotopyEquivalence ((boundedFlatAffineSectionOpenEvaluationPrespectrumMap j).map n) :=
  ExactModelEquivalence.level_isWeakHomotopyEquivalence
    (V := boundedFlatAffineSectionOpenModel j)
    (W := modelOf (boundedFlatPerfectOpenWaldhausen j))
    (boundedFlatAffineSectionSmallEquivalence R)
    (boundedFlatAffineSectionOpenSmallEquivalence_exact j)
    (boundedFlatAffineSectionOpenSmallEquivalence_inverse_exact j)
    (boundedFlatAffineSectionOpenEvaluationModelMap j).zero n

/-- The actual original relative-open evaluation is consequently stable in every signed degree. -/
theorem boundedFlatAffineSectionOpenEvaluation_isStableEquivalence :
    LoopPrespectrum.IsStableEquivalence (boundedFlatAffineSectionOpenEvaluationPrespectrumMap j) :=
  ExactModelEquivalence.isStableEquivalence
    (V := boundedFlatAffineSectionOpenModel j)
    (W := modelOf (boundedFlatPerfectOpenWaldhausen j))
    (boundedFlatAffineSectionSmallEquivalence R)
    (boundedFlatAffineSectionOpenSmallEquivalence_exact j)
    (boundedFlatAffineSectionOpenSmallEquivalence_inverse_exact j)
    (boundedFlatAffineSectionOpenEvaluationModelMap j).zero

end Quillen.PerfectComplexes
