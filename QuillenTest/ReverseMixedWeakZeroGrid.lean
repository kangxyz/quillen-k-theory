/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Quillen.Waldhausen.SConstruction.Iterated.ReverseMixedWeakZeroGrid

/-! Regression of the original composite null and independent normalization parameter. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory Convexity
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace QuillenTest.ReverseMixedWeakZeroGrid
open Quillen.SimplexGrid.WeakZeroCollapse

/-- Evaluate the original level-zero path without changing its loop coordinate. -/
def loopValue {M : Model.{u}} (y : (prespectrum M).space 0) (t : I) : stageSpace 0 M :=
  (show Path (stagePoint 0 M) (stagePoint 0 M) from y) t

variable {V W T U : Model.{u}} (f : W ⟶ T) (g : T ⟶ U)
  (η : (zeroHom W U).functor ⟶ (f ≫ g).functor)
  (hη : ∀ X, U.waldhausen.weq (η.app X))
  {q : ℕ} (G₀ : V ⟶ W) (G : Fin (q + 1) → (V ⟶ W))
  (τ : ∀ j, G₀.functor ≅ (G j).functor)

/-- Both clocks remain independent for the original composite-null constructor. -/
theorem original_composite_null (n : ℕ) (r : I)
    (w : StdSimplex ℝ (Fin (q + 1))) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily (ReverseMixedWeakZeroGrid.target (f ≫ g) η hη G₀ G τ) n
      (parameter.{u} ((Quillen.SimplexParameters.edge (k := 1) 0 1).symm r, w), x) =
      (prespectrumCompositeZeroNullHomotopy f g η hη).level n
        (r, prespectrumSimplexFamily (ModelSimplex.ofIsos G₀ G τ) n (w, x)) :=
  ReverseMixedWeakZeroGrid.native_null (f ≫ g) η hη G₀ G τ n r w x

/-- The original level-zero loop input stays independent of the two family parameters. -/
theorem original_loop_input (r t : I)
    (w : StdSimplex ℝ (Fin (q + 1))) (x : (prespectrum V).space 0) :
    loopValue (prespectrumSimplexFamily
      (ReverseMixedWeakZeroGrid.target (f ≫ g) η hη G₀ G τ) 0
      (parameter.{u} ((Quillen.SimplexParameters.edge (k := 1) 0 1).symm r, w), x)) t =
      loopValue ((prespectrumCompositeZeroNullHomotopy f g η hη).level 0
        (r, prespectrumSimplexFamily (ModelSimplex.ofIsos G₀ G τ) 0 (w, x))) t :=
  congrArg (fun y : (prespectrum U).space 0 ↦ loopValue y t)
    (original_composite_null f g η hη G₀ G τ 0 r w x)

/-- The whole terminal normalization face retains the actual original family. -/
theorem terminal_normalization (n : ℕ) (w : StdSimplex ℝ (Fin (q + 1)))
    (x : (prespectrum V).space n) :
    prespectrumSimplexFamily (ReverseMixedWeakZeroGrid.target (f ≫ g) η hη G₀ G τ) n
      (parameter.{u} (StdSimplex.single 1, w), x) =
      CommonReferenceNerve.prespectrumFamily (G₀ ≫ (f ≫ g))
        (ReverseMixedWeakZeroGrid.nodes (f ≫ g) G₀ G τ) n (w, x) := by
  rw [parameter_one]
  exact CommonReferenceWeakZero.normalization_native _ _ _ _ n w x

end QuillenTest.ReverseMixedWeakZeroGrid
