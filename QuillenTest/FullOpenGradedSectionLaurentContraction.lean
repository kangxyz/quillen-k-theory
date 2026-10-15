/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenGradedLaurentContraction

/-!
# Consumers of the chosen original graded Laurent contraction

The initial face is the original forward-T track and the final face is the original
constant coefficient track. Every comparison slice fixes the original action endpoints
and point line. Its structure equation retains independent comparison, action and structure times.
-/
@[expose] public section

open Quillen.PerfectComplexes


open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u
namespace QuillenTest.FullOpenGradedSectionLaurentContraction

open Quillen
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

/-- The chosen comparison starts at the forward-T track and ends at the constant original map. -/
theorem graded_laurent_comparison_faces (a : Under R) :
    (boundedFlatAffineFullOpenGradedSectionDiagramLaurentContraction j a).at 0 =
        boundedFlatAffineFullOpenGradedSectionDiagramLaurentHomotopy j a ∧
      (boundedFlatAffineFullOpenGradedSectionDiagramLaurentContraction j a).at 1 =
        LoopPrespectrum.Homotopy.refl
          ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map
            ((laurentUnderCoefficient R).app a)) :=
  ⟨LoopPrespectrum.Homotopy.RelHomotopy.at_zero _, LoopPrespectrum.Homotopy.RelHomotopy.at_one _⟩

/-- Every comparison slice fixes both original action endpoints and the whole point line. -/
theorem graded_laurent_relative_boundary (a : Under R) (n : ℕ) (r s : unitInterval)
    (x : ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a).space n) :
    ((boundedFlatAffineFullOpenGradedSectionDiagramLaurentContraction j a).at r).level n
        (0, x) = ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map
          ((laurentUnderCoefficient R).app a)).map n x ∧
      ((boundedFlatAffineFullOpenGradedSectionDiagramLaurentContraction j a).at r).level n
        (1, x) = ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map
          ((laurentUnderCoefficient R).app a)).map n x ∧
      ((boundedFlatAffineFullOpenGradedSectionDiagramLaurentContraction j a).at r).level n
        (s, ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a).point n) =
        ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj
          ((laurentUnderFunctor R).obj a)).point n :=
  ⟨((boundedFlatAffineFullOpenGradedSectionDiagramLaurentContraction j a).at r).at_zero n x,
    ((boundedFlatAffineFullOpenGradedSectionDiagramLaurentContraction j a).at r).at_one n x,
    ((boundedFlatAffineFullOpenGradedSectionDiagramLaurentContraction j a).at r).at_point n s⟩

/-- Comparison, action and original structure times remain independent at every level. -/
theorem graded_laurent_independent_structure_time (a : Under R) (n : ℕ) (r s t : unitInterval)
    (x : ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a).space n) :
    (boundedFlatAffineFullOpenGradedSectionDiagramLaurentContraction j a).level (n + 1)
        (r, (s, ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a).structureMap
          n x t)) =
      ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj
        ((laurentUnderFunctor R).obj a)).structureMap n
        ((boundedFlatAffineFullOpenGradedSectionDiagramLaurentContraction j a).level n
          (r, (s, x))) t :=
  (boundedFlatAffineFullOpenGradedSectionDiagramLaurentContraction j a).comm n r s x t

end QuillenTest.FullOpenGradedSectionLaurentContraction
