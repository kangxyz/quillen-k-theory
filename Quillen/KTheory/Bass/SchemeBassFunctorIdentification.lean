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
universe u v w
namespace Quillen.KTheory.Bass.SchemeIteratedSeedTransition

/-- The original Bass functor is the original cone diagram followed by parameter looping. -/
theorem bassFunctor_obj_eq {C : Type u} [Category.{w} C]
    (Q : C ⥤ Arrow (Arrow C)) (G : C ⥤ LoopPrespectrum.{v}) :
    (strictDiagramFunctor Q).obj G = ConeTrack.diagram Q G ⋙ parameterLoopingFunctor := rfl

end Quillen.KTheory.Bass.SchemeIteratedSeedTransition
