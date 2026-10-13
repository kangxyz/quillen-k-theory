/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.Topology.ClassifyingSpace.StableGeneralLinearCompletionSurjectivity

/-! Consumer checks for original finite-matrix representatives and realized surjectivity. -/

attribute [local instance] CategoryTheory.Limits.hasBinaryBiproducts_of_finite_biproducts
  Quillen.FiniteProjectiveModule.categoryDirectSumMonoidal
  Quillen.FiniteProjectiveModule.directSumMonoidal
  Quillen.FiniteProjectiveModule.directSumSymmetric

open CategoryTheory Quillen Quillen.FiniteProjectiveModule.StableCompletion

universe u
variable (R : Type u) [Ring R]

example : Function.Surjective ((groupoidCompletionFunctorMap (telescopeFunctor R)).mapEnd
    ((⊤ : MorphismProperty (StableGeneralLinear.GrothendieckModel.Telescope R)).Q.obj
      (telescopeBase R))) := telescopeCompletion_mapEnd_surjective R

example : Function.Surjective (piMap 0 (telescopeMap R)
    (classifyingSpaceMapUniversal_point (telescopeFunctor R) (telescopeBase R))) :=
  telescopeMap_piOne_surjective R

example : Function.Surjective (piMap 0 (telescopeMap (Matrix (Fin 2) (Fin 2) ℤ))
    (classifyingSpaceMapUniversal_point (telescopeFunctor (Matrix (Fin 2) (Fin 2) ℤ))
      (telescopeBase (Matrix (Fin 2) (Fin 2) ℤ)))) :=
  telescopeMap_piOne_surjective _
