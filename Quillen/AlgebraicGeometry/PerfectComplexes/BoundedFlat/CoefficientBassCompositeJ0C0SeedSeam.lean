/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Aglib.Topology.Path.HomotopyPathSlice
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0C0ProjectionSeam
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0C0ContractionSeam
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0TypedUnitRails

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
namespace Quillen.PerfectComplexes.CoefficientBassCompositeJ0C0SeedSeam
open CoefficientBassPositiveC0CarrierSeed CoefficientBassCompositeJ0C0SeedAlignment
open CoefficientBassCompositeJ0C0ProjectionSeam CoefficientBassCompositeJ0C0ContractionSeam
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- Endpoint retyping preserves every value of the original direct-l unit path. -/
theorem source_unit_typed (s : I) :
    toJ0 P p q (forwardUnit P p
      q (s, 0)) =
      CoefficientBassCompositeJ0TypedUnitRails.newUnit P p q s := by
  exact (source_unit_newUnit P p q s).trans
    (Path.RetypedUnitComparison.newUnit_apply _ _ _ _ _ _ _ s).symm

/-- The entire minus null keeps its original projection/contraction half-time cut. -/
theorem source_nullMinus (s : I) :
    toJ0 P p q (nullMinus P p
      q (s, 0)) =
      CoefficientBassCompositeJ0PairedNull.newNullMinus P p q s :=
  ContinuousMap.Homotopy.PathSlice.trans _ _ (toJ0 P p q) 0 _ _
    (projectionMinus_newPositive P p q) (contractionMinus_newCone P p q) s

/-- The entire plus null retains its own sheet, reference action and half-time cut. -/
theorem source_nullPlus (s : I) :
    toJ0 P p q (nullPlus P p
      q (s, 0)) =
      CoefficientBassCompositeJ0PairedNull.newNullPlus P p q s :=
  ContinuousMap.Homotopy.PathSlice.trans _ _ (toJ0 P p q) 0 _ _
    (projectionPlus_newPositive P p q) (contractionPlus_newCone P p q) s

/-- The full original word agrees at all seed times, with no reassociation or pause removal. -/
theorem source_seedWord (s : I) :
    toJ0 P p q (seedWord P p
      q (s, 0)) =
      ((CoefficientBassCompositeJ0PairedNull.newNullMinus P p q).symm.trans
        ((CoefficientBassCompositeJ0TypedUnitRails.newUnit P p q).trans
          (CoefficientBassCompositeJ0PairedNull.newNullPlus P p q))) s :=
  ContinuousMap.Homotopy.PathSlice.trans _ _ (toJ0 P p q) 0 _ _
    (ContinuousMap.Homotopy.PathSlice.symm _ (toJ0 P p q) 0 _ (source_nullMinus P p q))
    (ContinuousMap.Homotopy.PathSlice.trans _ _ (toJ0 P p q) 0 _ _
      (source_unit_typed P p q) (source_nullPlus P p q)) s

/-- The exit of the single reversed C0 face is precisely the complete J0 new seed. -/
theorem reversedFace_exit (s : I) :
    toJ0 P p q (reversedFace P p
      q (1, s)) =
      ((CoefficientBassCompositeJ0PairedNull.newNullMinus P p q).symm.trans
        ((CoefficientBassCompositeJ0TypedUnitRails.newUnit P p q).trans
          (CoefficientBassCompositeJ0PairedNull.newNullPlus P p q))) s := by
  change toJ0 P p q (seedWord P p
    q (s, unitInterval.symm 1)) = _
  rw [unitInterval.symm_one]
  exact source_seedWord P p q s

end Quillen.PerfectComplexes.CoefficientBassCompositeJ0C0SeedSeam
