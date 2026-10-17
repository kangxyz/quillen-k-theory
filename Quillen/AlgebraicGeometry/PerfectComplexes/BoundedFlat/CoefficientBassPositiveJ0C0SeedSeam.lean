/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Aglib.Topology.Path.HomotopyPathSlice
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0C0ProjectionSeam
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0C0ContractionSeam
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0TypedUnitRails

/-!
# The complete C0 source seed in the actual J0 carrier

Whole projection, contraction and unit rails are pasted with the literal original parentheses.
The single outer C0 reversal is retained; no conjugation square is supplied or assumed.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveJ0C0SeedSeam
open CoefficientBassPositiveC0CarrierSeed CoefficientBassPositiveJ0C0SeedAlignment
open CoefficientBassPositiveJ0C0ProjectionSeam CoefficientBassPositiveJ0C0ContractionSeam
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (d : Under R)

/-- Endpoint retyping preserves every value of the original direct-l unit path. -/
theorem source_unit_typed (s : I) :
    toJ0 P d (forwardUnit P ((polynomialUnderCoefficient R).app d)
      ((underToLaurent R).app d) (s, 0)) =
      CoefficientBassPositiveJ0TypedUnitRails.newUnit P d s := by
  exact (source_unit_newUnit P d s).trans
    (Path.RetypedUnitComparison.newUnit_apply _ _ _ _ _ _ _ s).symm

/-- The entire minus null keeps its original projection/contraction half-time cut. -/
theorem source_nullMinus (s : I) :
    toJ0 P d (nullMinus P ((polynomialUnderCoefficient R).app d)
      ((underToLaurent R).app d) (s, 0)) =
      CoefficientBassPositiveJ0PairedNull.newNullMinus P d s :=
  ContinuousMap.Homotopy.PathSlice.trans _ _ (toJ0 P d) 0 _ _
    (projectionMinus_newPositive P d) (contractionMinus_newCone P d) s

/-- The entire plus null retains its own sheet, reference action and half-time cut. -/
theorem source_nullPlus (s : I) :
    toJ0 P d (nullPlus P ((polynomialUnderCoefficient R).app d)
      ((underToLaurent R).app d) (s, 0)) =
      CoefficientBassPositiveJ0PairedNull.newNullPlus P d s :=
  ContinuousMap.Homotopy.PathSlice.trans _ _ (toJ0 P d) 0 _ _
    (projectionPlus_newPositive P d) (contractionPlus_newCone P d) s

/-- The full original word agrees at all seed times, with no reassociation or pause removal. -/
theorem source_seedWord (s : I) :
    toJ0 P d (seedWord P ((polynomialUnderCoefficient R).app d)
      ((underToLaurent R).app d) (s, 0)) =
      ((CoefficientBassPositiveJ0PairedNull.newNullMinus P d).symm.trans
        ((CoefficientBassPositiveJ0TypedUnitRails.newUnit P d).trans
          (CoefficientBassPositiveJ0PairedNull.newNullPlus P d))) s :=
  ContinuousMap.Homotopy.PathSlice.trans _ _ (toJ0 P d) 0 _ _
    (ContinuousMap.Homotopy.PathSlice.symm _ (toJ0 P d) 0 _ (source_nullMinus P d))
    (ContinuousMap.Homotopy.PathSlice.trans _ _ (toJ0 P d) 0 _ _
      (source_unit_typed P d) (source_nullPlus P d)) s

/-- The exit of the single reversed C0 face is precisely the complete J0 new seed. -/
theorem reversedFace_exit (s : I) :
    toJ0 P d (reversedFace P ((polynomialUnderCoefficient R).app d)
      ((underToLaurent R).app d) (1, s)) =
      ((CoefficientBassPositiveJ0PairedNull.newNullMinus P d).symm.trans
        ((CoefficientBassPositiveJ0TypedUnitRails.newUnit P d).trans
          (CoefficientBassPositiveJ0PairedNull.newNullPlus P d))) s := by
  change toJ0 P d (seedWord P ((polynomialUnderCoefficient R).app d)
    ((underToLaurent R).app d) (s, unitInterval.symm 1)) = _
  rw [unitInterval.symm_one]
  exact source_seedWord P d s

end Quillen.PerfectComplexes.CoefficientBassPositiveJ0C0SeedSeam
