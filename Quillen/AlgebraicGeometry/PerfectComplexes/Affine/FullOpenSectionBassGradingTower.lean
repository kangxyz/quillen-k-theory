/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenSectionBassTower
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenSectionBassSeedChangeWeak
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenGradedSectionBassTelescope
public import Quillen.KTheory.Bass.StrictDiagramMap

/-!
# The actual fine-to-graded maps through the full-open Bass tower

The strict Bass iterate acts on the original grading transformation. Its proved seed equation
makes the actual fine and graded transitions commute with these same finite maps. Compactness
enters only through the original coefficient-natural grading diagram and its seed equation.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

variable [CompactSpace U]

/-- Every finite grading map is the literal Bass iterate of the original transformation. -/
def boundedFlatAffineFullOpenSectionBassGrading (i : ℕ) :
    boundedFlatAffineFullOpenSectionBassDiagram j i ⟶
      boundedFlatAffineFullOpenGradedSectionBassDiagram j i :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
    (boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j)

/-- At stage zero the fine-to-graded arrow is the unchanged original grading map. -/
theorem boundedFlatAffineFullOpenSectionBassGrading_zero :
    boundedFlatAffineFullOpenSectionBassGrading j 0 =
      boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j := rfl

/-- The first finite grading component is the original looped square-cone map. -/
theorem boundedFlatAffineFullOpenSectionBassGrading_one_app (a : Under R) :
    (boundedFlatAffineFullOpenSectionBassGrading j 1).app a =
      parameterLoopingMap (boundedFlatAffineFullOpenSectionBassConeChangeWeak j a) :=
  boundedFlatAffineFullOpenSectionBassChangeWeak_functor_app j a

/-- Every finite grading map preserves the exact original fine and graded transitions. -/
theorem boundedFlatAffineFullOpenSectionBassGrading_transition (i : ℕ) :
    boundedFlatAffineFullOpenSectionBassGrading j i ≫
        boundedFlatAffineFullOpenGradedSectionBassTransition j i =
      boundedFlatAffineFullOpenSectionBassTransition j i ≫
        boundedFlatAffineFullOpenSectionBassGrading j (i + 1) :=
  (strictDiagramTransition_map (laurentUnderSquareFunctor R)
    (boundedFlatAffineFullOpenSectionBassSeed j)
    (boundedFlatAffineFullOpenGradedSectionBassSeed j)
    (boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j)
    (boundedFlatAffineFullOpenSectionBassSeed_changeWeak j) i).symm

/-- The same original arbitrary coefficient square commutes at every finite Bass stage. -/
theorem boundedFlatAffineFullOpenSectionBassGrading_naturality
    (i : ℕ) {a b : Under R} (f : a ⟶ b) :
    (boundedFlatAffineFullOpenSectionBassDiagram j i).map f ≫
        (boundedFlatAffineFullOpenSectionBassGrading j i).app b =
      (boundedFlatAffineFullOpenSectionBassGrading j i).app a ≫
        (boundedFlatAffineFullOpenGradedSectionBassDiagram j i).map f :=
  (boundedFlatAffineFullOpenSectionBassGrading j i).naturality f

end Quillen.PerfectComplexes
