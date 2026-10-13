/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyCofiber.UnreducedConeHomology

/-! # Degree-one and degree-two homology tests for the original unreduced cone -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits Quillen.LocalCoefficients Quillen.ReducedMappingCone
universe u
namespace QuillenTest.UnreducedConeHomology
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) (V : ModuleCat.{u} ℤ)
  (hf : QuasiIso (pushforwardChainMap f (constant Y V)))

include hf

/-- Positive degree one requires no simply-connectedness or homotopy-detection premise. -/
theorem degree_one : IsZero (homology (constant (UnreducedSpace f) V) 1) :=
  unreducedCone_positive_homology_isZero_of_quasiIso f V hf 0

/-- The first-obstruction degree two uses the actual original cone and actual constant system. -/
theorem degree_two : IsZero (homology (constant (UnreducedSpace f) V) 2) :=
  unreducedCone_positive_homology_isZero_of_quasiIso f V hf 1

/-- Mathlib's ordinary singular functor gives the same actual positive-degree vanishing. -/
theorem ordinary_degree_two :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) 2).obj V).obj
      (UnreducedSpace f)) :=
  unreducedCone_positive_singularHomology_isZero_of_quasiIso f V hf 1

end QuillenTest.UnreducedConeHomology
