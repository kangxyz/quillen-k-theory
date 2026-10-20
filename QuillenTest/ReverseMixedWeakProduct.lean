/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.RealizationReverseMixedWeakProduct
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexWeakPrependLift

/-! Regression: an arbitrary original weak transformation runs after the whole independent
source-isomorphism family, with original time and level-zero loop input preserved. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity
open scoped Simplicial Topology unitInterval
universe u
namespace QuillenTest
open Quillen Quillen.Waldhausen.IteratedS

example {V W T : Model.{u}} {F H : W ⟶ T}
    (η : F.functor ⟶ H.functor) (hη : ∀ X, T.waldhausen.weq (η.app X))
    {q : ℕ} (G₀ : V ⟶ W) (G : Fin (q + 1) → (V ⟶ W))
    (anchor : ∀ i, G₀.functor ≅ (G i).functor)
    (n : ℕ) (t : unitInterval) (z : StdSimplex ℝ (Fin (q + 1)))
    (x : (prespectrum V).space n) :
    prespectrumSimplexFamily
      (ReverseMixedWeakProduct.simplex
        (ModelSimplex.prependWeak
          (ModelSimplex.ofIsos H (fun _ : Fin 1 ↦ H) (fun _ ↦ Iso.refl _)) η hη)
        G₀ G anchor) n
      (SimplexGrid.parameter.{u} 1 q ((SimplexParameters.edge 0 1) t, z), x) =
      (prespectrumTransformationHomotopy η hη).level n
        (t, prespectrumSimplexFamily (ModelSimplex.ofIsos G₀ G anchor) n (z, x)) := by
  rw [ReverseMixedWeakProduct.prespectrum_comp]
  exact ModelSimplex.prependWeak_edge_native
    (ModelSimplex.ofIsos H (fun _ : Fin 1 ↦ H) (fun _ ↦ Iso.refl _)) η hη n t _

end QuillenTest
