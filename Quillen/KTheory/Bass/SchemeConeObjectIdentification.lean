/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.GeometricConeIndexTransport
public import Quillen.KTheory.Bass.ConeTrack

/-! # The literal object of the geometric cone functor -/
@[expose] public section
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
namespace Quillen.KTheory.Bass.SchemeIteratedSeedTransition

/-- This object identification changes only the presentation of the original cone. -/
theorem coneFunctor_obj_eq (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :
    GeometricConeInterchange.coneFunctor.obj F = ConeTrack.diagram squareFunctor F := rfl

end Quillen.KTheory.Bass.SchemeIteratedSeedTransition
