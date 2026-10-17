/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialTripleFiller

/-! The six literal coordinate faces of the actual polynomial split-triple filler. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialTripleFiller
open CoefficientBassRaw1PolynomialTripleRoutes
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d) (negative : Bool)

/-- The first comparison face retains the entire original left route. -/
theorem extension_zero (r h : I) :
    extension P p q w negative ![0, r, h] = left P p q w negative (r, h) :=
  extension_face P p q w negative (0, false)
    ⟨⟨![0, r, h], ⟨0, Or.inl rfl⟩⟩, rfl⟩

/-- The final comparison face retains the entire original right route. -/
theorem extension_one (r h : I) :
    extension P p q w negative ![1, r, h] = right P p q w negative (r, h) :=
  extension_face P p q w negative (0, true)
    ⟨⟨![1, r, h], ⟨0, Or.inr rfl⟩⟩, rfl⟩

/-- The initial route edge is fixed for every comparison coordinate. -/
theorem extension_route_zero (s h : I) :
    extension P p q w negative ![s, 0, h] = left P p q w negative (0, h) :=
  extension_face P p q w negative (1, false)
    ⟨⟨![s, 0, h], ⟨1, Or.inl rfl⟩⟩, rfl⟩

/-- The final route edge is fixed for every comparison coordinate. -/
theorem extension_route_one (s h : I) :
    extension P p q w negative ![s, 1, h] = left P p q w negative (1, h) :=
  extension_face P p q w negative (1, true)
    ⟨⟨![s, 1, h], ⟨1, Or.inr rfl⟩⟩, rfl⟩

/-- The bottom retains both original split-triple coordinates without reparameterization. -/
theorem extension_bottom (s r : I) :
    extension P p q w negative ![s, r, 0] =
      CoefficientBassRaw1PolynomialTripleBottom.family P (chartChoice negative) p q w (s, r) :=
  extension_face P p q w negative (2, false)
    ⟨⟨![s, r, 0], ⟨2, Or.inl rfl⟩⟩, rfl⟩

/-- The entire top is the original polynomial postcomposition tip. -/
theorem extension_top (s r : I) :
    extension P p q w negative ![s, r, 1] =
      CoefficientBassRaw1PolynomialPostcomp.tip P p q w (chartChoice negative) :=
  extension_face P p q w negative (2, true)
    ⟨⟨![s, r, 1], ⟨2, Or.inr rfl⟩⟩, rfl⟩

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialTripleFiller
