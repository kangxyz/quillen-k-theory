/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.SchemeNaturalSeed
public import Quillen.KTheory.Bass.NormalizedStageAction

/-! # Original all-scheme seeds under the fixed loop strength -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.LoopPrespectrum
universe u w
namespace Quillen.KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSeedCospan
open LoopStrength LoopConeTrack IteratedLoopStrength
variable {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

/-- Input-loop time and the original seed time keep their prescribed order. -/
theorem seed_loop_strength (A : Track laurent.op coefficient F) :
    seed A.loop ≫ strengthDiagram squareFunctor F =
      Functor.whiskerRight (seed A) parameterLoopingFunctor := by
  apply NatTrans.ext
  funext X
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro γ
  apply Path.ext
  funext r
  apply Path.ext
  funext t
  have h := seed_square A.loop A (evaluationAt F r) (by
    intro Y s
    apply Hom.ext
    funext m
    ext δ
    rfl)
  have hv := congrArg (fun k => Path.toContinuousMap ((k.app X).map n γ) t) h
  have hb := bassHomotopy_apply (E := F ⋙ parameterLoopingFunctor) (F := F)
    (evaluation F) (evaluation_naturality F) squareFunctor X n r
    ((seed A.loop).app X |>.map n γ)
  exact (congrArg (fun p => Path.toContinuousMap p t) hb).trans hv

end Quillen.KTheory.Bass.SchemeNaturalSeed
