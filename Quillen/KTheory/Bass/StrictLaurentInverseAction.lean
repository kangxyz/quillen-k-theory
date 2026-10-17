/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.StrictLaurentUnitQuotient
public import Quillen.Waldhausen.SConstruction.Iterated.ModelSelfTrackStableOperation

/-!
# The actual inverse Laurent Model action

Invert the specified identity automorphisms on the original Laurent Models, retaining their
coefficient-preservation equations. The original Model composition triangle proves that this
actual inverse action has the negative stable operation and the negative original quotient.
The inverse operation is constructed geometrically before its algebraic sign is identified.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum CommRingCat.PolynomialLaurent
open Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
universe u w
namespace Quillen.KTheory.Bass.LaurentSeed
variable {R : CommRingCat.{u}} {C : Under R ⥤ Model.{w}} (A : ModelAction C)

/-- The inverse of the same specified Laurent unit, with its original coefficient functors. -/
def ModelAction.symm : ModelAction C where
  unit a := (A.unit a).symm
  naturality {a b} g x := map_inv_app_eq
    (C.map ((laurentUnderFunctor R).map g)).functor (A.unit a) (A.unit b) x
      (A.naturality g x)

/-- The actual inverse unit track induces the negative original degree-raising operation. -/
theorem ModelAction.symm_stableOperation (a : Under R) (d : ℤ) :
    (A.symm.track.homotopy a).stableOperation d =
      -(A.track.homotopy a).stableOperation d :=
  prespectrumIsoHomotopy_stableOperation_symm
    (C.map ((laurentUnderCoefficient R).app a))
    (onFunctor (C.map ((laurentUnderCoefficient R).app a)).functor (A.unit a)) d

/-- The whole original inverse-unit operation is the negative natural forward operation. -/
theorem ModelAction.symm_stableOperationNatTrans (d : ℤ) :
    A.symm.track.stableOperationNatTrans d = -A.track.stableOperationNatTrans d := by
  apply NatTrans.ext
  funext a
  exact A.symm_stableOperation a d

/-- The actual inverse unit uses the same original quotient and induces its negative. -/
theorem ModelAction.symm_stableUnitQuotient (d : ℤ) :
    A.symm.track.stableUnitQuotient d = -A.track.stableUnitQuotient d := by
  rw [Track.stableUnitQuotient, A.symm_stableOperationNatTrans, Preadditive.neg_comp]
  rfl

/-- Invertibility of the original forward quotient implies invertibility of the actual inverse
unit quotient, with no choice of a replacement operation. -/
theorem ModelAction.symm_stableUnitQuotient_isIso (d : ℤ)
    [IsIso (A.track.stableUnitQuotient d)] :
    IsIso (A.symm.track.stableUnitQuotient d) := by
  rw [A.symm_stableUnitQuotient]
  change IsIso (-(asIso (A.track.stableUnitQuotient d))).hom
  infer_instance

end Quillen.KTheory.Bass.LaurentSeed
