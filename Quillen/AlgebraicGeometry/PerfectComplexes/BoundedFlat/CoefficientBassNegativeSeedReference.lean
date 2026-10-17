/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeCarrierReference
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeSeedEndpointHEq

/-! Full carrier equality transport preserves both complete original source seeds. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassNegativeSeedReference
open CoefficientBassNegativeCarrierReference
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b b' c : Under R} (p : a ⟶ b) (q : b ⟶ c) (p' : a ⟶ b') (q' : b' ⟶ c)

/-- Equality transport preserves every point of the complete original C0 source face. -/
theorem c0_source (h : p ≫ q = p' ≫ q') (s : I) :
    transport P p q p' q' h (CoefficientBassPositiveC0CarrierSeed.face P p q (0, s)) =
      CoefficientBassPositiveC0CarrierSeed.face P p' q' (0, s) :=
  eq_of_heq ((transport_heq P p q p' q' h _).trans
    (c0_source_heq P p q p' q' h s))

/-- Equality transport preserves every point of the complete original C1 source face. -/
theorem c1_source (h : p ≫ q = p' ≫ q') (s : I) :
    transport P p q p' q' h (CoefficientBassPositiveC1SeedFace.face P p q (0, s)) =
      CoefficientBassPositiveC1SeedFace.face P p' q' (0, s) :=
  eq_of_heq ((transport_heq P p q p' q' h _).trans
    (c1_source_heq P p q p' q' h s))

end Quillen.PerfectComplexes.CoefficientBassNegativeSeedReference
