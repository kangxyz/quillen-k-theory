/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSectionLaurentAction

/-! # Original scalar/null seed restriction regressions -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
open Quillen.Waldhausen.IteratedS Quillen.KTheory.Bass
open CommRingCat.PolynomialLaurent
universe u
namespace QuillenTest.GlobalSectionLaurentAction

/-- The seed target is literally the existing named ambient Bass seed. -/
theorem original_seed_square {R : CommRingCat.{u}} (P : Over (Spec R)) :
    (globalLaurentAction P).track.seed ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (Functor.whiskerRight (rowRestriction P) prespectrumFunctor) =
    Functor.whiskerRight (rowRestriction P) prespectrumFunctor ≫
      boundedFlatCoefficientAmbientBassSeed P := rowRestriction_seed P

example {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R) :
    ((rowRestriction P).app a).functor.obj ((globalRow P).obj a).waldhausen.zero =
      ((boundedFlatCoefficientSectionModelRow P).obj a).waldhausen.zero :=
  ((rowRestriction P).app a).zero

end QuillenTest.GlobalSectionLaurentAction
