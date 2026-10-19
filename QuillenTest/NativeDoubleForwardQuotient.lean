/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeDoubleForwardQuotient

/-!
# Native twice-positive quotient consumers

Every original double Bass quotient class on a QCQS scheme has a unique
original K-zero preimage. The actual variable swap carries that representative
to the representative of its additive inverse.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme Quillen.Bass.TwoChart
open Quillen.PerfectComplexes.CoefficientDoubleNativeUnit
universe u
namespace QuillenTest.NativeDoubleForwardQuotient
variable (X : QuasiCompactSchemes.{u}ᵒᵖ)
local notation "p" => NatTrans.op PolynomialLaurent.Relative.plus
local notation "m" => NatTrans.op PolynomialLaurent.Relative.minus

/-- Quotient classes are represented uniquely by the actual native K-zero operation. -/
theorem unique_original_preimage [QuasiSeparatedSpace X.unop.obj]
    (b : (contraction p m (contraction p m (quasiCompactKFunctor 2))).obj X) :
    ∃! a : (quasiCompactKFunctor 0).obj X, doubleForwardQuotient.app X a = b := by
  have h : Function.Bijective (doubleForwardQuotient.app X) :=
    (ConcreteCategory.isIso_iff_bijective (doubleForwardQuotient.app X)).mp inferInstance
  exact h.existsUnique b

/-- The actual swapped representative is the original representative of the additive inverse. -/
theorem swap_representative (a : (quasiCompactKFunctor 0).obj X) :
    PolynomialLaurent.Relative.doubleContractionSwap (quasiCompactKFunctor 2) X
        (doubleForwardQuotient.app X a) =
      doubleForwardQuotient.app X (-a) := by
  have h := ConcreteCategory.congr_hom (doubleForwardQuotient_swap X) a
  change PolynomialLaurent.Relative.doubleContractionSwap (quasiCompactKFunctor 2) X
    (doubleForwardQuotient.app X a) = -(doubleForwardQuotient.app X a) at h
  simpa only [map_neg] using h

end QuillenTest.NativeDoubleForwardQuotient
