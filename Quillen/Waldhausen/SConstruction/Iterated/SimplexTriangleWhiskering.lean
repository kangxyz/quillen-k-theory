/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.SimplexWhiskering
public import Quillen.Topology.Prespectrum.RelativeHomotopyWhiskering

/-! The actual old whole composition triangle retains both whiskering operations. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS
variable {V W T : Model.{u}} {F G H : V ⟶ W}
  (η : F.functor ⟶ G.functor) (θ : G.functor ⟶ H.functor)
  (hη : ∀ A, W.waldhausen.weq (η.app A)) (hθ : ∀ A, W.waldhausen.weq (θ.app A))

theorem ModelSimplex.triangle_postcomp (J : W ⟶ T) :
    (ModelSimplex.triangle η θ hη hθ).postcomp J =
      ModelSimplex.triangle (F := F ≫ J) (G := G ≫ J) (H := H ≫ J)
        (whiskerRight η J.functor) (whiskerRight θ J.functor)
        (fun A ↦ J.exact.weak _ (hη A)) (fun A ↦ J.exact.weak _ (hθ A)) := by
  apply ModelSimplex.ext_diagram
  refine ComposableArrows.ext₂ rfl rfl rfl ?_ ?_ <;>
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] <;> rfl

theorem ModelSimplex.triangle_precomp (J : T ⟶ V) :
    (ModelSimplex.triangle η θ hη hθ).precomp J =
      ModelSimplex.triangle (F := J ≫ F) (G := J ≫ G) (H := J ≫ H)
        (whiskerLeft J.functor η) (whiskerLeft J.functor θ)
        (fun A ↦ hη (J.functor.obj A)) (fun A ↦ hθ (J.functor.obj A)) := by
  apply ModelSimplex.ext_diagram
  refine ComposableArrows.ext₂ rfl rfl rfl ?_ ?_ <;>
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] <;> rfl

/-- The old entire two-time composition comparison commutes with literal postcomposition. -/
theorem transformationComposition_postcomp (J : W ⟶ T) (n : ℕ)
    (r s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumTransformationCompositionHomotopy
      (F := F ≫ J) (G := G ≫ J) (H := H ≫ J)
      (whiskerRight η J.functor) (whiskerRight θ J.functor)
      (fun A ↦ J.exact.weak _ (hη A)) (fun A ↦ J.exact.weak _ (hθ A))).level n (r, (s, x)) =
      ((prespectrumTransformationCompositionHomotopy η θ hη hθ).postcomp
        (prespectrumMap J)).level n (r, (s, x)) := by
  rw [← prespectrumSimplexFamily_triangle, ← ModelSimplex.triangle_postcomp,
    prespectrumSimplexFamily_postcomp, prespectrumSimplexFamily_triangle]
  rfl

/-- The old entire two-time composition comparison commutes with literal precomposition. -/
theorem transformationComposition_precomp (J : T ⟶ V) (n : ℕ)
    (r s : unitInterval) (x : (prespectrum T).space n) :
    (prespectrumTransformationCompositionHomotopy
      (F := J ≫ F) (G := J ≫ G) (H := J ≫ H)
      (whiskerLeft J.functor η) (whiskerLeft J.functor θ)
      (fun A ↦ hη (J.functor.obj A)) (fun A ↦ hθ (J.functor.obj A))).level n (r, (s, x)) =
      (Homotopy.RelHomotopy.precomp (prespectrumMap J)
        (prespectrumTransformationCompositionHomotopy η θ hη hθ)).level n (r, (s, x)) := by
  rw [← prespectrumSimplexFamily_triangle, ← ModelSimplex.triangle_precomp,
    prespectrumSimplexFamily_precomp, prespectrumSimplexFamily_triangle]
  rfl

end Quillen.Waldhausen.IteratedS
