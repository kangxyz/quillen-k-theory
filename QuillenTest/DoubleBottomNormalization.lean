/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.GeometricConeDoubleBottomShift

/-! # Original second-bottom shifts and both independent loop times -/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.LoopPrespectrum Quillen.KTheory.Bass
open Quillen.KTheory.Bass.GeometricConeInterchange
open scoped Topology unitInterval

universe u v w

example {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
    (F : C ⥤ Quillen.LoopPrespectrum.{w}) (X : C) (n : ℕ)
    (γ : (((strictDiagramIterate Q 2).obj F).obj X).space n) (r t : unitInterval) :
    Path.toContinuousMap
        (Path.toContinuousMap
          (((NormalizedStageMap.stageMap Q 2 F).app X).map n γ) r) t =
      Path.toContinuousMap
        (Path.toContinuousMap ((parameterLoopingMap
          (LoopFactor.coneStrength ((ConeTrack.diagram Q F).mapArrow.mapArrow.obj
            (Q.obj X)))).map n γ) t) r := by
  rw [NormalizedStageMap.stageMap_two_app]
  exact LoopFactor.strength_factor_value (ConeTrack.diagram Q F) Q X n γ r t

example (F : Scheme.{u}ᵒᵖ ⥤ Quillen.LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ)
    (x : (stableHomotopyFunctor (((-2 : ℤ) + 1) + 1)).obj
      (F.obj (laurent.op.obj (laurent.op.obj X)))) :
    (doubleNormalizedShift F X (-2)).hom
        ((stableHomotopyFunctor (-2)).map
          ((NormalizedStageMap.stageMap squareFunctor 2 F).app X)
            (doubleBottomRepresentative F X (-2) x)) =
      -((stableHomotopyFunctor (((-2 : ℤ) + 1) + 1)).map (doubleLaurentInclusion F X) x) :=
  congrArg (fun k => k x) (doubleBottomRepresentative_stageMap F X (-2))
