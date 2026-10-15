/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionRestrictionModel

/-! The original full-open Model map retains its actual functor and literal inherited zero. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace QuillenTest.FullOpenSectionRestrictionModel

open Quillen
open Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The internal source expression is the exact original pointwise Model. -/
theorem originalSource (a : Under R) :
    (boundedFlatAffineSectionOpenModelFunctor j).obj a =
      boundedFlatAffineSectionOpenModel (inclusion j a) := rfl

/-- The genuine Model arrow uses exactly the previously constructed restriction functor. -/
theorem originalFunctor (a : Under R) :
    (boundedFlatAffineSectionFullOpenModelMap j a).functor =
      boundedFlatAffineFullOpenSectionRestriction j a := rfl

/-- The original pointwise source Model retains the specified section zero. -/
private theorem sourceZero (a : Under R) :
    (boundedFlatAffineSectionOpenModel (inclusion j a)).waldhausen.zero =
      boundedFlatAffineSectionZero a.right :=
  boundedFlatAffineSectionWaldhausen_zero a.right

/-- The original pointwise target Model retains its specified whole-section zero. -/
private theorem targetZero (a : Under R) :
    (boundedFlatAffineFullOpenSectionModel j a).waldhausen.zero =
      boundedFlatAffineFullOpenSectionZero j a := rfl

/-- Its actual zero field proves equality of the original whole chosen-zero sections. -/
theorem originalZero (a : Under R) :
    (boundedFlatAffineFullOpenSectionRestriction j a).obj
        (boundedFlatAffineSectionZero a.right) =
      boundedFlatAffineFullOpenSectionZero j a := by
  have h := (boundedFlatAffineSectionFullOpenModelMap j a).zero
  rw [originalFunctor j a, sourceZero j a, targetZero j a] at h
  exact h

/-- Original iterated-S realization accepts this precise zero-preserving Model arrow. -/
def originalPrespectrumMap (a : Under R) :
    prespectrum (boundedFlatAffineSectionOpenModel (inclusion j a)) ⟶
      prespectrum (boundedFlatAffineFullOpenSectionModel j a) :=
  prespectrumMap (boundedFlatAffineSectionFullOpenModelMap j a)

end QuillenTest.FullOpenSectionRestrictionModel
