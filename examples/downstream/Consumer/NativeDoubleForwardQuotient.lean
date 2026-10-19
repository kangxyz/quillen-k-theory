/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeDoubleForwardQuotient

/-!
# The actual quotient swap in a separate package

Clients retain the original twice-contracted K-two group and the actual
factor-swap map. Swap-fixed quotient classes are two-torsion; no vanishing
of such classes is asserted.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme Quillen.Bass.TwoChart
open Quillen.PerfectComplexes.CoefficientDoubleNativeUnit
universe u
namespace NativeDoubleForwardQuotientConsumer
variable (X : QuasiCompactSchemes.{u}ᵒᵖ) [QuasiSeparatedSpace X.unop.obj]
local notation "p" => NatTrans.op PolynomialLaurent.Relative.plus
local notation "m" => NatTrans.op PolynomialLaurent.Relative.minus

/-- Swapping any actual double-quotient class gives its additive inverse. -/
theorem swapped_class_cancels
    (b : (contraction p m (contraction p m (quasiCompactKFunctor 2))).obj X) :
    PolynomialLaurent.Relative.doubleContractionSwap (quasiCompactKFunctor 2) X b + b = 0 := by
  have h := ConcreteCategory.congr_hom (doubleContractionSwap_KTwo_eq_neg_id X) b
  change PolynomialLaurent.Relative.doubleContractionSwap (quasiCompactKFunctor 2) X b = -b at h
  rw [h, neg_add_cancel]

/-- A class fixed by the actual factor swap is consequently two-torsion. -/
theorem fixed_class_two_torsion
    (b : (contraction p m (contraction p m (quasiCompactKFunctor 2))).obj X)
    (hb : PolynomialLaurent.Relative.doubleContractionSwap (quasiCompactKFunctor 2) X b = b) :
    b + b = 0 := by
  simpa only [hb] using swapped_class_cancels X b

end NativeDoubleForwardQuotientConsumer
