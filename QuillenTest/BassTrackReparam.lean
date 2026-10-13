/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.RelativeHomotopyReparam
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassSpanMap

/-! Uniform cancellation and reassociation applied to the original Bass coefficient tracks. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes Quillen.LoopPrespectrum
universe u
namespace QuillenTest.BassTrackReparam

open Quillen
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The actual polynomial coefficient track followed by its reversal contracts. -/
def polynomialCancellation :
    (Quillen.LoopPrespectrum.Homotopy.refl _).RelHomotopy
      ((boundedFlatPolynomialSquareHomotopy f).trans
        (boundedFlatPolynomialSquareHomotopy f).symm) :=
  Homotopy.RelHomotopy.reflTransSymm (boundedFlatPolynomialSquareHomotopy f)

/-- The negative Laurent coefficient track has its own literal cancellation. -/
def minusCancellation :
    (Quillen.LoopPrespectrum.Homotopy.refl _).RelHomotopy
      ((boundedFlatMinusSquareHomotopy f).symm.trans
        (boundedFlatMinusSquareHomotopy f)) :=
  Homotopy.RelHomotopy.reflSymmTrans (boundedFlatMinusSquareHomotopy f)

/-- Reassociation retains the actual positive Laurent track at every endpoint. -/
def plusReassociation :
    (((boundedFlatPlusSquareHomotopy f).trans
      (boundedFlatPlusSquareHomotopy f).symm).trans
        (boundedFlatPlusSquareHomotopy f)).RelHomotopy
    ((boundedFlatPlusSquareHomotopy f).trans
      ((boundedFlatPlusSquareHomotopy f).symm.trans
        (boundedFlatPlusSquareHomotopy f))) :=
  Homotopy.RelHomotopy.transAssoc _ _ _

/-- All comparison, original-path, and prespectrum-structure coordinates remain independent. -/
theorem polynomial_structure (n : ℕ) (r s t : unitInterval)
    (x : (Quillen.Waldhausen.IteratedS.originalPrespectrum
      (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (polynomialCancellation f).level (n + 1)
        (r, (s, (Quillen.Waldhausen.IteratedS.originalPrespectrum
          (boundedFlatPerfectWaldhausen (Spec R))).structureMap n x t)) =
      (Quillen.Waldhausen.IteratedS.originalPrespectrum
        (boundedFlatPerfectWaldhausen (Spec (.of (Polynomial S))))).structureMap n
          ((polynomialCancellation f).level n (r, (s, x))) t :=
  (polynomialCancellation f).comm n r s x t

end QuillenTest.BassTrackReparam
