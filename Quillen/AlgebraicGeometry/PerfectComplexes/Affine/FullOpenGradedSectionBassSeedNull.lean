/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenGradedSectionBassSeed
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenGradedLaurentContraction
public import Quillen.Topology.Prespectrum.RelativeHomotopyLoop

/-!
# The actual quotient-graded Bass seed is pointwise null

The unchanged chosen Laurent contraction is postcomposed with the original Bass cone inclusion.
Both original source-leg cone-null tracks remain fixed while the prescribed relative
concatenations and backtracking cancellation contract the literal seed loop. Currying this same
joint family gives a whole prespectrum nullhomotopy of the actual graded Bass seed map.
The cone null used here is distinct from the normalized localization null. No coefficient
naturality or compatibility with the latter is assumed or asserted in this leaf.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PolynomialBaseChange Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

/-- The prescribed joint family cancels the original seed loop with both cone-null legs fixed. -/
def boundedFlatAffineFullOpenGradedSectionBassSeedNullComparison (a : Under R) :
    (((boundedFlatAffineFullOpenGradedSectionDiagramLaurentHomotopy j a).postcomp
      (mappingConeInclusion
        (StrictSquare.comparison (boundedFlatAffineFullOpenGradedSectionBassSquare j a))))
      |>.conjugateToZero (boundedFlatAffineFullOpenGradedSectionBassNullHomotopy j a)).RelHomotopy
      (LoopPrespectrum.Homotopy.refl
        (zeroHom ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a)
          (boundedFlatAffineFullOpenGradedSectionBassCone j a))) := by
  let N := boundedFlatAffineFullOpenGradedSectionBassNullHomotopy j a
  let J := (boundedFlatAffineFullOpenGradedSectionDiagramLaurentContraction j a).postcomp
    (mappingConeInclusion
      (StrictSquare.comparison (boundedFlatAffineFullOpenGradedSectionBassSquare j a)))
  exact ((LoopPrespectrum.Homotopy.RelHomotopy.refl N.symm).hcomp
    ((J.hcomp (LoopPrespectrum.Homotopy.RelHomotopy.refl N)).trans
      (LoopPrespectrum.Homotopy.RelHomotopy.reflTrans N))).trans
        (LoopPrespectrum.Homotopy.RelHomotopy.reflSymmTrans N).symm

/-- Currying that same joint family nulls the actual original quotient-graded Bass seed map. -/
def boundedFlatAffineFullOpenGradedSectionBassSeedNullHomotopy (a : Under R) :
    LoopPrespectrum.Homotopy (boundedFlatAffineFullOpenGradedSectionBassSeedMap j a)
      (zeroHom ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a)
        (parameterLooping (boundedFlatAffineFullOpenGradedSectionBassCone j a))) :=
  (boundedFlatAffineFullOpenGradedSectionBassSeedNullComparison j a).zeroLoopMapHomotopy

/-- The null time and the original output-loop coordinate remain independent and unchanged. -/
theorem boundedFlatAffineFullOpenGradedSectionBassSeedNullHomotopy_apply
    (a : Under R) (n : ℕ) (r s : unitInterval)
    (x : ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a).space n) :
    Path.toContinuousMap
      ((boundedFlatAffineFullOpenGradedSectionBassSeedNullHomotopy j a).level n (r, x)) s =
      (boundedFlatAffineFullOpenGradedSectionBassSeedNullComparison j a).level n (r, (s, x)) :=
  LoopPrespectrum.Homotopy.RelHomotopy.zeroLoopMapHomotopy_apply _ n r s x

end Quillen.PerfectComplexes
