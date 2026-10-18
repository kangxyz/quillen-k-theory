/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSchemeLaurentTrack
public import Quillen.KTheory.Bass.GeometricSquareInvertibility

/-!
# Regression for the actual all-scheme Laurent action

The track is the original global section scalar realization along the original
projection, and its naturality applies to every scheme morphism. The original
four-corner comparison is invertible without choosing a replacement map.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
open Quillen.KTheory.Bass
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
open Quillen.PerfectComplexes.GlobalSchemeLaurentTrack
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace QuillenTest.GlobalSchemeLaurentSeed

/-- The scalar track keeps every original realization time and source point. -/
theorem original_unit_value (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : (diagram.obj X).space n) :
    (homotopy X).level n (r,x) =
      (prespectrumIsoHomotopy (globalModel.map (GeometricSeedCospan.coefficient.app X))
        (onFunctor (globalModel.map (GeometricSeedCospan.coefficient.app X)).functor
          (unit X))).level n (r,x) := rfl

/-- No affine, compactness or flatness assumption is needed for actual track naturality. -/
theorem arbitrary_scheme_map {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) (n : ℕ)
    (r : unitInterval) (x : (diagram.obj X).space n) :
    (diagram.map (laurent.op.map f)).map n ((homotopy X).level n (r,x)) =
      (homotopy Y).level n (r,(diagram.map f).map n x) :=
  homotopy_naturality f n r x

/-- The finite geometric square uses its own componentwise invertible map. -/
example : IsIso (GeometricSquareInterchange.squareInterchangeMap diagram.{u}) :=
  GeometricSquareInterchange.squareInterchange_isIso diagram

#print axioms GeometricSquareInterchange.squareInterchange_polynomial_lower
#print axioms GeometricSquareInterchange.squareInterchange_isIso
#print axioms Quillen.PerfectComplexes.GlobalSchemeLaurentTrack.laurentScalar_map
#print axioms Quillen.PerfectComplexes.GlobalSchemeLaurentTrack.unit_naturality
#print axioms Quillen.PerfectComplexes.GlobalSchemeLaurentTrack.homotopy_naturality
#print axioms Quillen.PerfectComplexes.GlobalSchemeLaurentTrack.wholeUnitSquare
#print axioms Quillen.PerfectComplexes.GlobalSchemeLaurentTrack.seed_cospan

end QuillenTest.GlobalSchemeLaurentSeed
