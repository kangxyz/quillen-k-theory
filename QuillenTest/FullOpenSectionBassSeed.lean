/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenSectionBassSeed

/-!
# Original-chart consumers of the actual full-open Bass seed

The polynomial charts stay in their original order. The seed is coefficient-natural and its
literal loop retains the original forward-T track between the original two null legs.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
open Quillen.PerfectComplexes
universe u
namespace QuillenTest.FullOpenSectionBassSeed

open Quillen
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The rightward chart is positive and the downward chart uses the inverse coordinate. -/
theorem original_chart_order (a : Under R) :
    (boundedFlatAffineFullOpenSectionBassSquare j a).hom.right =
        (boundedFlatAffineFullOpenSectionPrespectrumFunctor j).map
          ((underToLaurent R).app a) ∧
      (boundedFlatAffineFullOpenSectionBassSquare j a).right.hom =
        (boundedFlatAffineFullOpenSectionPrespectrumFunctor j).map
          ((underToLaurentInvert R).app a) := ⟨rfl, rfl⟩

/-- Every actual coefficient arrow preserves the constructed pointwise seed. -/
theorem original_coefficient_seed {a b : Under R} (f : a ⟶ b) :
    (boundedFlatAffineFullOpenSectionBassSeed j).app a ≫
        parameterLoopingMap (boundedFlatAffineFullOpenSectionBassConeMap j f) =
      (boundedFlatAffineFullOpenSectionPrespectrumFunctor j).map f ≫
        (boundedFlatAffineFullOpenSectionBassSeed j).app b :=
  boundedFlatAffineFullOpenSectionBassSeedMap_naturality j f

/-- The literal loop uses the checked forward-T track and the same original null on both legs. -/
theorem original_seed_loop (a : Under R) (n : ℕ)
    (x : ((boundedFlatAffineFullOpenSectionPrespectrumFunctor j).obj a).space n)
    (t : unitInterval) :
    Path.toContinuousMap (((boundedFlatAffineFullOpenSectionBassSeed j).app a).map n x) t =
      (((boundedFlatAffineFullOpenSectionDiagramLaurentHomotopy j a).postcomp
        (mappingConeInclusion
          (StrictSquare.comparison (boundedFlatAffineFullOpenSectionBassSquare j a))))
        |>.conjugateToZero
          (boundedFlatAffineFullOpenSectionBassNullHomotopy j a)).level n (t, x) :=
  boundedFlatAffineFullOpenSectionBassSeedMap_apply j a n x t

end QuillenTest.FullOpenSectionBassSeed
