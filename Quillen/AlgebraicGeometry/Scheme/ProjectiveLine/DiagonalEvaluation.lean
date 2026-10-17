/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.AffineDiagonal
public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalAffine
public import Mathlib.RingTheory.Polynomial.Ideal
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Original equal-coordinate affine diagonal

Polynomial evaluation has its literal principal kernel and induces the original
diagonal in the affine rectangle. Both same-chart base-change diagrams retain
the actual relative diagonal and original rectangle maps over an arbitrary base ring.
-/
@[expose] public section

open Quillen.PolynomialBaseChange


open CommRingCat.PolynomialLaurent

open Quillen

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open PolynomialLaurent
/-- Same-chart base change retains the actual polynomial diagonal. -/
theorem sameChart_diagonal_isPullback (R : CommRingCat.{u})
    (j : Spec (.of (Polynomial R)) ⟶ twoChartLine R) [IsOpenImmersion j]
    (hj : j ≫ projection R = polynomialProjection R) :
    IsPullback j (polynomialDiagonal R) (relativeDiagonal R) (rectangleMap R j j hj hj) := by
  apply (rectangle_diagonal_isPullback R j j hj hj).of_iso
    (asIso (pullback.fst j j)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp
  · apply pullback.hom_ext <;>
      simp [intersectionToRectangle, polynomialDiagonal, fst_eq_snd_of_mono_eq]
  · simp
  · simp
end AlgebraicGeometry.Scheme.ProjectiveLine
