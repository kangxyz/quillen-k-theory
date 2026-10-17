/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassConnectiveInvertibility
public import Quillen.Topology.Prespectrum.ParameterLoopingStableEquivalence

/-!
# Connective invertibility of the original native fine seed

The already constructed whole one-step evaluation homotopy transports connective
invertibility of the actual raw seed to the original strict fine seed. Both evaluation maps
are the original geometric ones. This does not posit an all-stage raw comparison.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left]
variable [QuasiSeparatedSpace P.left] (a : Under R)

/-- Original whole one-step evaluation carries raw connective invertibility to the fine seed. -/
instance boundedFlatCoefficientFullOpenBassSeedMap_connective_isIso (n : ℕ) :
    IsIso ((stableHomotopyFunctor (n : ℤ)).map
      (boundedFlatCoefficientFullOpenBassSeedMap (𝟙 P) a)) := by
  let e := boundedFlatCoefficientFullOpenBassConeEvaluation (𝟙 P) a
  let : IsIso ((stableHomotopyFunctor (n : ℤ)).map (parameterLoopingMap e)) :=
    parameterLoopingMap_isStableEquivalence e
      (boundedFlatCoefficientFullOpenBassConeEvaluation_isStableEquivalence (𝟙 P) a) _
  let : IsIso ((stableHomotopyFunctor (n : ℤ)).map
      (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a))) :=
    boundedFlatCoefficientSectionEvaluationPrespectrumMap_isStableEquivalence (op P, a) _
  have h := Homotopy.stableHomotopyMap_eq
    (boundedFlatCoefficientFullOpenBassSeedEvaluationHomotopy (𝟙 P) a) (n : ℤ)
  simp only [Functor.map_comp] at h
  let : IsIso ((stableHomotopyFunctor (n : ℤ)).map
      (boundedFlatCoefficientFullOpenBassSeedMap (𝟙 P) a) ≫
        (stableHomotopyFunctor (n : ℤ)).map (parameterLoopingMap e)) := by
    change IsIso (_ ≫ (stableHomotopyFunctor (n : ℤ)).map
      (parameterLoopingMap (boundedFlatCoefficientFullOpenBassConeEvaluation (𝟙 P) a)))
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((stableHomotopyFunctor (n : ℤ)).map (parameterLoopingMap e))

/-- The actual strict native transition at stage zero has the same proved connective isomorphism.
-/
instance boundedFlatCoefficientAmbientBassTransition_zero_connective_isIso (n : ℕ) :
    IsIso ((stableHomotopyFunctor (n : ℤ)).map
      ((boundedFlatCoefficientAmbientBassTransition P 0).app a)) :=
  boundedFlatCoefficientFullOpenBassSeedMap_connective_isIso P a n

end Quillen.PerfectComplexes
