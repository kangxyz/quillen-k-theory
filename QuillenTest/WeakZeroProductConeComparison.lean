/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Quillen.Waldhausen.SConstruction.Iterated.MixedWeakZeroProductConeComparison
import Quillen.Waldhausen.SConstruction.Iterated.ReverseMixedWeakZeroProductConeComparison

/-! The local comparison retains both original composite-null orders and independent loop time. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory Convexity Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace QuillenTest.WeakZeroProductConeComparison
variable {V W T U : Model.{u}} {q : ℕ} {i j : Fin (q + 1)}
  (P : Path (StdSimplex.single i : StdSimplex ℝ (Fin (q + 1))) (StdSimplex.single j))

/-- The entire initial forward face keeps the originally selected composite null. -/
theorem forward_composite (f : V ⟶ W) (g : W ⟶ T)
    (η : (zeroHom V T).functor ⟶ (f ≫ g).functor)
    (hη : ∀ X, T.waldhausen.weq (η.app X))
    (G₀ : T ⟶ U) (G : Fin (q + 1) → (T ⟶ U))
    (τ : ∀ j, G₀.functor ≅ (G j).functor)
    (n : ℕ) (r s : I) (x : (prespectrum V).space n) :
    MixedWeakZeroGrid.productConeComparison (f ≫ g) η hη G₀ G τ P n ((0, (r, s)), x) =
      prespectrumSimplexFamily (ModelSimplex.ofIsos G₀ G τ) n
        (P s, (prespectrumCompositeZeroNullHomotopy f g η hη).level n (r, x)) :=
  MixedWeakZeroGrid.productConeComparison_zero (f ≫ g) η hη G₀ G τ P n r s x

/-- The entire reverse face keeps source normalization before the original composite null. -/
theorem reverse_composite (f : W ⟶ T) (g : T ⟶ U)
    (η : (zeroHom W U).functor ⟶ (f ≫ g).functor)
    (hη : ∀ X, U.waldhausen.weq (η.app X))
    (G₀ : V ⟶ W) (G : Fin (q + 1) → (V ⟶ W))
    (τ : ∀ j, G₀.functor ≅ (G j).functor)
    (n : ℕ) (r s : I) (x : (prespectrum V).space n) :
    ReverseMixedWeakZeroGrid.productConeComparison (f ≫ g) η hη G₀ G τ P n
        ((0, (r, s)), x) =
      (prespectrumCompositeZeroNullHomotopy f g η hη).level n
        (r, prespectrumSimplexFamily (ModelSimplex.ofIsos G₀ G τ) n (P s, x)) :=
  ReverseMixedWeakZeroGrid.productConeComparison_zero (f ≫ g) η hη G₀ G τ P n r s x

/-- Every interpolation time preserves the original independent level-zero loop input. -/
theorem independent_loop (F : V ⟶ W)
    (η : (zeroHom V W).functor ⟶ F.functor)
    (hη : ∀ X, W.waldhausen.weq (η.app X))
    (G₀ : W ⟶ T) (G : Fin (q + 1) → (W ⟶ T))
    (τ : ∀ j, G₀.functor ≅ (G j).functor)
    (a r s t : I) (x : Path (stagePoint 0 V) (stagePoint 0 V)) :
    (show Path (stagePoint 0 T) (stagePoint 0 T) from
      MixedWeakZeroGrid.productConeComparison F η hη G₀ G τ P 0 ((a, (r, s)), x)) t =
      stageSimplexBarycentric (MixedWeakZeroGrid.target F η hη G₀ G τ) 0
        (Quillen.SimplexGrid.WeakZeroProductComparison.comparison.{u} P (a, (r, s)), x t) := rfl

end QuillenTest.WeakZeroProductConeComparison
