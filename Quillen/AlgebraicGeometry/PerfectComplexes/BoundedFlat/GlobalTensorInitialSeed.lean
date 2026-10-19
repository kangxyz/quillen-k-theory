/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSectionLaurentAction
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionEvaluationSeedComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitBassComposite

/-!
# The initial global coefficient seed and genuine tensor/null word

The existing full first-cone evaluation keeps its original source null. Actual global row
restriction and the original tensor unitor then compare the two whole initial transitions.
This statement concerns Bass stage zero at every spectrum level, not all Bass stages.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.KTheory.Bass Quillen.LoopPrespectrum
open CommRingCat.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The actual global seed restricts to the original fine first seed, with its same source null. -/
theorem initial_seed_restriction :
    (globalLaurentAction P).track.seedMap a ≫
      ((strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (Functor.whiskerRight (rowRestriction P) prespectrumFunctor)).app a =
    prespectrumMap ((rowRestriction P).app a) ≫
      boundedFlatCoefficientFullOpenBassSeedMap (𝟙 P) a := by
  have h := NatTrans.congr_app (rowRestriction_seed P) a
  exact h

/-- The whole initial global seed evaluates to the actual tensor/null transition.
The target remains parameter loops of the original raw cone. -/
def initialTensorSeedComparison :
    Homotopy
      (((globalLaurentAction P).track.seedMap a ≫
        ((strictDiagramFunctor (laurentUnderSquareFunctor R)).map
          (Functor.whiskerRight (rowRestriction P) prespectrumFunctor)).app a) ≫
        parameterLoopingMap (boundedFlatCoefficientFullOpenBassConeEvaluation (𝟙 P) a))
      (prespectrumMap ((rowRestriction P).app a) ≫
        boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a) ≫
          boundedFlatCoefficientTensorBassTransition P a) := by
  let J := (boundedFlatCoefficientFullOpenBassSeedEvaluationHomotopy (𝟙 P) a).trans
    (Homotopy.precomp (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a))
      (boundedFlatCoefficientTensorBassTransitionHomotopy P a).symm)
  refine (Homotopy.precomp (prespectrumMap ((rowRestriction P).app a)) J).cast ?_ rfl
  have h := congrArg
    (fun k => k ≫ parameterLoopingMap
      (boundedFlatCoefficientFullOpenBassConeEvaluation (𝟙 P) a))
    (initial_seed_restriction P a).symm
  exact (Category.assoc _ _ _).symm.trans h

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
