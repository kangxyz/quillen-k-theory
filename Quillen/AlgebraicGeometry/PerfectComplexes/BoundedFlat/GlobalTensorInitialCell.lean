/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalTensorInitialSeed
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientBassTransition

/-!
# The initial global seed and the actual stabilized coefficient cell

Postcompose the original whole seed comparison by the actual stabilization of its raw cone.
The target is the independently realized coefficient-cell transition. Both loop coordinates
and the unchanged positive source null remain present.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.KTheory.Bass Quillen.LoopPrespectrum
open CommRingCat.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- Reassociate postcomposition with an explicitly identified final factor. -/
theorem postcompose_factor {C : Type*} [Category C] {A B D E F : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F) (e : D ⟶ F)
    (h : e = c ≫ d) : (a ≫ b ≫ c) ≫ d = a ≫ b ≫ e := by
  rw [h]
  simp only [Category.assoc]

/-- The actual initial comparison after cone stabilization, retaining its given target map. -/
def initialStabilizedTensorSeedComparison :=
  (initialTensorSeedComparison P a).postcomp (parameterLoopingMap
    (stabilizationMap (mappingCone (boundedFlatCoefficientBassSquareComparison P a))))

/-- Postcompose a whole homotopy and retain an explicitly identified final factor. -/
def postcomposeFactorHomotopy {A B D E F : LoopPrespectrum}
    {f : A ⟶ E} {a : A ⟶ B} {b : B ⟶ D} {c : D ⟶ E}
    (H : Homotopy f (a ≫ b ≫ c)) (d : E ⟶ F) (e : D ⟶ F)
    (h : e = c ≫ d) : Homotopy (f ≫ d) (a ≫ b ≫ e) :=
  (H.postcomp d).cast rfl (postcompose_factor a b c d e h)

/-- The initial global seed evaluates to the independently realized stabilized cell/null word. -/
def initialCellSeedComparison :=
  postcomposeFactorHomotopy (initialTensorSeedComparison P a)
    (parameterLoopingMap (stabilizationMap
      (mappingCone (boundedFlatCoefficientBassSquareComparison P a))))
    (boundedFlatCoefficientCellBassTransition P a)
    (boundedFlatCoefficientCellBassTransition_eq P a)

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
