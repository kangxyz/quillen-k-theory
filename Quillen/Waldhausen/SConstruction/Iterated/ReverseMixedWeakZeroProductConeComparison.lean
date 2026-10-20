/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.WeakZeroProductConeParameter
public import Quillen.Waldhausen.SConstruction.Iterated.ReverseMixedWeakZeroGrid

/-!
# Weak-null precomposition compared with its affine cone

Realize the scalar product-to-cone interpolation with source normalization before the
original weak null. All six complete faces, chosen endpoint nulls, and independent structure
time are retained. This local comparison is not an assembled localization overlap cube.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity
open Quillen.SimplexParameters Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.ReverseMixedWeakZeroGrid
open Quillen.SimplexGrid.WeakZeroProductComparison
variable {V W T : Model.{u}} (F : W ⟶ T)
  (η : (zeroHom W T).functor ⟶ F.functor)
  (hη : ∀ X, T.waldhausen.weq (η.app X))
  {q : ℕ} (G₀ : V ⟶ W) (G : Fin (q + 1) → (V ⟶ W))
  (τ : ∀ j, G₀.functor ≅ (G j).functor)
  {i j : Fin (q + 1)}
  (P : Path (StdSimplex.single i : StdSimplex ℝ (Fin (q + 1))) (StdSimplex.single j))

/-- Realization of the specified scalar comparison, with independent original level input. -/
def productConeComparison (n : ℕ) :
    C((I × (I × I)) × (prespectrum V).space n, (prespectrum T).space n) :=
  (prespectrumSimplexFamily (target F η hη G₀ G τ) n).comp
    ⟨fun z ↦ (comparison.{u} P z.1, z.2), by fun_prop⟩

/-- The whole initial surface is the original weak null after the full source normalization. -/
theorem productConeComparison_zero (n : ℕ) (r s : I) (x : (prespectrum V).space n) :
    productConeComparison F η hη G₀ G τ P n ((0, (r, s)), x) =
      (prespectrumTransformationHomotopy η hη).level n
        (unitInterval.symm r,
          prespectrumSimplexFamily (ModelSimplex.ofIsos G₀ G τ) n (P s, x)) := by
  change prespectrumSimplexFamily (target F η hη G₀ G τ) n
    (comparison.{u} P (0, (r, s)), x) = _
  rw [comparison_zero]
  exact native_null F η hη G₀ G τ n r (P s) x

/-- The opposite surface is the separately specified cone, not a replacement for the product. -/
theorem productConeComparison_one (n : ℕ) (r s : I) (x : (prespectrum V).space n) :
    productConeComparison F η hη G₀ G τ P n ((1, (r, s)), x) =
      CommonReferenceWeakZero.coneFamily (G₀ ≫ F) (nodes F G₀ G τ)
        (ModelZeroNormalization.preZero η G₀)
        (ModelZeroNormalization.preZero_weak η hη G₀) n
        ((r, StdSimplex.map Fin.succ (P s)), x) := by
  change prespectrumSimplexFamily (target F η hη G₀ G τ) n
    (comparison.{u} P (1, (r, s)), x) = _
  rw [comparison_one]
  rfl

/-- The endpoint columns are the independently specified original weak nulls, at all times. -/
theorem productConeComparison_source (θ : (zeroHom V T).functor ⟶ (G i ≫ F).functor)
    (hθ : ∀ X, T.waldhausen.weq (θ.app X))
    (n : ℕ) (a r : I) (x : (prespectrum V).space n) :
    productConeComparison F η hη G₀ G τ P n ((a, (r, 0)), x) =
      (prespectrumTransformationHomotopy θ hθ).level n (unitInterval.symm r, x) := by
  change prespectrumSimplexFamily (target F η hη G₀ G τ) n
    (comparison.{u} P (a, (r, 0)), x) = _
  rw [comparison_source]
  exact CommonReferenceWeakZero.vertex_edge_native (G₀ ≫ F) (nodes F G₀ G τ)
    (ModelZeroNormalization.preZero η G₀)
    (ModelZeroNormalization.preZero_weak η hη G₀) i θ hθ n (unitInterval.symm r) x

/-- The unchanged complete normalization path is fixed at every interpolation time. -/
theorem productConeComparison_null_zero (n : ℕ) (a s : I)
    (x : (prespectrum V).space n) :
    productConeComparison F η hη G₀ G τ P n ((a, (0, s)), x) =
      prespectrumSimplexFamily
        (CommonReferenceWeakZero.normalizationSimplex (G₀ ≫ F) (nodes F G₀ G τ)) n
        (StdSimplex.map Fin.succ (P s), x) := by
  change prespectrumSimplexFamily (target F η hη G₀ G τ) n
    (comparison.{u} P (a, (0, s)), x) = _
  rw [comparison_null_zero]
  have h := CommonReferenceWeakZero.coneFamily_zero (G₀ ≫ F) (nodes F G₀ G τ)
    (ModelZeroNormalization.preZero η G₀)
    (ModelZeroNormalization.preZero_weak η hη G₀) n
    (StdSimplex.map Fin.succ (P s)) x
  change prespectrumSimplexFamily (target F η hη G₀ G τ) n
    (CommonReferenceWeakZero.coneParameter (0, StdSimplex.map Fin.succ (P s)), x) = _ at h
  rw [CommonReferenceWeakZero.cone_zero] at h
  exact h

/-- The complete terminal face remains the original chosen native zero. -/
theorem productConeComparison_null_one (n : ℕ) (a s : I)
    (x : (prespectrum V).space n) :
    productConeComparison F η hη G₀ G τ P n ((a, (1, s)), x) =
      (prespectrum T).point n := by
  change prespectrumSimplexFamily (target F η hη G₀ G τ) n
    (comparison.{u} P (a, (1, s)), x) = _
  rw [comparison_null_one]
  have h := CommonReferenceWeakZero.coneFamily_one (G₀ ≫ F) (nodes F G₀ G τ)
    (ModelZeroNormalization.preZero η G₀)
    (ModelZeroNormalization.preZero_weak η hη G₀) n
    (StdSimplex.map Fin.succ (P s)) x
  change prespectrumSimplexFamily (target F η hη G₀ G τ) n
    (CommonReferenceWeakZero.coneParameter (1, StdSimplex.map Fin.succ (P s)), x) = _ at h
  rw [CommonReferenceWeakZero.cone_one] at h
  exact h

/-- The other endpoint column retains its independently chosen original weak null. -/
theorem productConeComparison_target (θ : (zeroHom V T).functor ⟶ (G j ≫ F).functor)
    (hθ : ∀ X, T.waldhausen.weq (θ.app X))
    (n : ℕ) (a r : I) (x : (prespectrum V).space n) :
    productConeComparison F η hη G₀ G τ P n ((a, (r, 1)), x) =
      (prespectrumTransformationHomotopy θ hθ).level n (unitInterval.symm r, x) := by
  change prespectrumSimplexFamily (target F η hη G₀ G τ) n
    (comparison.{u} P (a, (r, 1)), x) = _
  rw [comparison_target]
  exact CommonReferenceWeakZero.vertex_edge_native (G₀ ≫ F) (nodes F G₀ G τ)
    (ModelZeroNormalization.preZero η G₀)
    (ModelZeroNormalization.preZero_weak η hη G₀) j θ hθ n (unitInterval.symm r) x

/-- All three independent scalar coordinates preserve the original pointed condition. -/
theorem productConeComparison_point (n : ℕ) (a r s : I) :
    productConeComparison F η hη G₀ G τ P n ((a, (r, s)), (prespectrum V).point n) =
      (prespectrum T).point n :=
  prespectrumSimplexFamily_point (target F η hη G₀ G τ) n (comparison.{u} P (a, (r, s)))

/-- The original structure coordinate is independent of every comparison parameter. -/
theorem productConeComparison_structure (n : ℕ) (a r s t : I)
    (x : (prespectrum V).space n) :
    productConeComparison F η hη G₀ G τ P (n + 1)
        ((a, (r, s)), (prespectrum V).structureMap n x t) =
      (prespectrum T).structureMap n
        (productConeComparison F η hη G₀ G τ P n ((a, (r, s)), x)) t :=
  prespectrumSimplexFamily_structure (target F η hη G₀ G τ) n
    (comparison.{u} P (a, (r, s))) x t

end Quillen.Waldhausen.IteratedS.ReverseMixedWeakZeroGrid
