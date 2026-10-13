/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.CoveringHomologyComparison

/-! Original twisted maps yield actual integral homology isomorphisms upstairs. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LocalCoefficients
universe u

namespace Quillen.Consumer.CoverCoefficientTransport
variable {E B E' B' : Type u}
variable [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace E'] [TopologicalSpace B']
variable {p : E → B} {p' : E' → B'} (hp : IsCoveringMap p) (hp' : IsCoveringMap p')
variable [SimplyConnectedSpace E] [SimplyConnectedSpace E'] [PathConnectedSpace B]
variable (k : C(E, E')) (f : C(B, B')) (h : ∀ e, p' (k e) = f (p e))
variable (e₀ : E) (hπ : Function.Bijective (piMap 0 f (x := p e₀) rfl))

include hp hp' h e₀ hπ

/-- The exact upstairs map has invertible homology in every degree from
all the original UniverseLift twisted chain maps on the base. -/
theorem originalIntegralHomology
    (hH : ∀ A : System.{u, u} B', QuasiIso (UniverseLift.chainMap.{u, u, u} f A))
    (n : ℕ) : IsIso (pushforwardHomologyMap k (constant E' integralCoefficients) n) := by
  let := covering_integral_quasiIso_of_all_localCoefficients hp hp' k f h e₀ hπ hH
  change IsIso (HomologicalComplex.homologyMap
    (pushforwardChainMap k (constant E' integralCoefficients)) n)
  infer_instance

/-- The literal mathlib singular-chain map, with the displayed original k,
is a quasi-isomorphism without any covering assumption on k or f. -/
theorem originalSingularChains
    (hH : ∀ A : System.{u, u} B', QuasiIso (UniverseLift.chainMap.{u, u, u} f A)) :
    QuasiIso (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj
      integralCoefficients).map (TopCat.ofHom k)) :=
  covering_singular_quasiIso_of_all_localCoefficients hp hp' k f h e₀ hπ hH

end Quillen.Consumer.CoverCoefficientTransport
