/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.SimplexTriangleLift

/-! The whole old triangle is unchanged by equality transport of its first exact functor. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS
variable {V W : Model.{u}} {F F' G H : V ⟶ W}
  (e : F.functor = F'.functor)
  (η : F'.functor ⟶ G.functor) (θ : G.functor ⟶ H.functor)
  (hη : ∀ A, W.waldhausen.weq (η.app A)) (hθ : ∀ A, W.waldhausen.weq (θ.app A))
  (hη' : ∀ A, W.waldhausen.weq (((eqToHom e) ≫ η).app A))

/-- Equality of the first functor preserves the complete old two-arrow diagram. -/
theorem ModelSimplex.triangle_source_transport :
    ModelSimplex.triangle (F := F) ((eqToHom e) ≫ η) θ hη' hθ =
      ModelSimplex.triangle η θ hη hθ := by
  have hF : F = F' := Model.Hom.ext e
  subst F'
  simp only [eqToHom_refl, Category.id_comp]

/-- The actual whole two-time triangle survives the source transport at every original level. -/
theorem transformationComposition_source_transport (n : ℕ) (r s : unitInterval)
    (x : (prespectrum V).space n) :
    (prespectrumTransformationCompositionHomotopy (F := F)
      ((eqToHom e) ≫ η) θ hη' hθ).level n (r, (s, x)) =
      (prespectrumTransformationCompositionHomotopy η θ hη hθ).level n (r, (s, x)) := by
  rw [← prespectrumSimplexFamily_triangle, ModelSimplex.triangle_source_transport e η θ hη hθ hη',
    prespectrumSimplexFamily_triangle]

end Quillen.Waldhausen.IteratedS
