/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Topology.ClassifyingSpace.StableGeneralLinearCharacter

/-! The original stable comparison is detected by the original quotient map. -/
open CategoryTheory CategoryTheory.Limits Quillen Quillen.FiniteProjectiveModule
open Quillen.FiniteProjectiveModule.StableCompletion
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
universe u
variable (R : Type u) [Ring R]

example : ((quotientDetectionMap R).comp (stableMap R)).Homotopic
    (GroupoidClassifying.classifyingMap (StableGeneralLinear.quotientMap R)).hom :=
  stableMap_quotientDetection_homotopic R
