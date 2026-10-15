/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenSectionBassSeedChangeWeak

/-!
# Consumers of the original quotient-graded full-open Bass seed

The original chart order survives quotient grading. The actual changeWeak map retains the
forward-T action and inherited cone null at independent times, and the original seed square
holds on the specified identity algebra without identifying independently chosen open fibers.
-/
@[expose] public section

open Quillen.PerfectComplexes


open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace QuillenTest.FullOpenGradedSectionBassSeed

open Quillen
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

/-- The graded square keeps the positive rightward chart and inverse-coordinate downward chart. -/
theorem original_graded_chart_order (a : Under R) :
    (boundedFlatAffineFullOpenGradedSectionBassSquare j a).hom.right =
        (boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map
          ((underToLaurent R).app a) ∧
      (boundedFlatAffineFullOpenGradedSectionBassSquare j a).right.hom =
        (boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map
          ((underToLaurentInvert R).app a) := ⟨rfl, rfl⟩

/-- At degree zero the original action and source-null retain their independently chosen times. -/
theorem original_track_and_null (a : Under R) (t s : unitInterval)
    (x : ((boundedFlatAffineFullOpenSectionPrespectrumFunctor j).obj a).space 0) :
    ((boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j).app
        ((laurentUnderFunctor R).obj a)).map 0
        ((boundedFlatAffineFullOpenSectionDiagramLaurentHomotopy j a).level 0 (t, x)) =
      (boundedFlatAffineFullOpenGradedSectionDiagramLaurentHomotopy j a).level 0
        (t, ((boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j).app a).map 0 x) ∧
    (boundedFlatAffineFullOpenSectionBassConeChangeWeak j a).map 0
        ((boundedFlatAffineFullOpenSectionBassNullHomotopy j a).level 0 (s, x)) =
      (boundedFlatAffineFullOpenGradedSectionBassNullHomotopy j a).level 0
        (s, ((boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j).app a).map 0 x) :=
  ⟨boundedFlatAffineFullOpenSectionDiagramLaurentHomotopy_changeWeak_apply j a 0 t x,
    boundedFlatAffineFullOpenSectionBassNullHomotopy_changeWeak_apply j a 0 s x⟩

/-- The specified identity-algebra fiber satisfies the actual seed square before normalization. -/
theorem original_identity_algebra_seed_square :
    (boundedFlatAffineFullOpenSectionBassSeed j).app (Under.mk (𝟙 R)) ≫
        ((Quillen.KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).map
          (boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j)).app
            (Under.mk (𝟙 R)) =
      (boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j).app
          (Under.mk (𝟙 R)) ≫
        (boundedFlatAffineFullOpenGradedSectionBassSeed j).app (Under.mk (𝟙 R)) := by
  simpa only [NatTrans.comp_app] using congrArg (fun η ↦ η.app (Under.mk (𝟙 R)))
    (boundedFlatAffineFullOpenSectionBassSeed_changeWeak j)

end QuillenTest.FullOpenGradedSectionBassSeed
