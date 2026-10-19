/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.GeometricConeLaurentWordRepresentative

/-!
# Epimorphic original Laurent representatives in every finite cone stage

The original zero-offset growth survives all actual unlooped cone iterates.
Each literal Laurent inclusion is therefore epimorphic on stable H-zero,
including the unchanged original finite representative at every index.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
namespace Quillen.KTheory.Bass.GeometricConeInterchange

/-- The original finite cone iterate retains zero-offset growth at every actual parameter. -/
theorem iterate_linearZeroGrowth (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (hF : ∀ X, LinearZeroGrowth (F.obj X)) (n : ℕ) (X : Scheme.{u}ᵒᵖ) :
    LinearZeroGrowth ((FiniteConeTopology.iterate squareFunctor n F).obj X) := by
  induction n generalizing X with
  | zero => exact hF X
  | succ n ih => exact cone_linearZeroGrowth _ ih X

/-- Every original finite H-zero cone class has its actual n-fold Laurent representative. -/
theorem laurentInclusion_zero_epi (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (hF : ∀ X, LinearZeroGrowth (F.obj X)) (n : ℕ) (X : Scheme.{u}ᵒᵖ) :
    Epi ((stableHomotopyFunctor 0).map (laurentInclusion n F X)) := by
  induction n generalizing X with
  | zero =>
    change Epi ((stableHomotopyFunctor 0).map (𝟙 (F.obj X)))
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  | succ n ih =>
    have h₁ := ih (laurent.op.obj X)
    have h₂ := coneInclusion_zero_epi (FiniteConeTopology.iterate squareFunctor n F)
      (iterate_linearZeroGrowth F hF n) X
    rw [show (stableHomotopyFunctor 0).map (laurentInclusion (n + 1) F X) =
      (stableHomotopyFunctor 0).map (laurentInclusion n F (laurent.op.obj X)) ≫
        (stableHomotopyFunctor 0).map
          (coneInclusion (FiniteConeTopology.iterate squareFunctor n F) X) from
            (stableHomotopyFunctor 0).map_comp _ _]
    exact epi_comp' h₁ h₂

end Quillen.KTheory.Bass.GeometricConeInterchange
