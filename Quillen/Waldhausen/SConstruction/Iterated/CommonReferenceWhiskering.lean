/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceFaces
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexWhiskering

/-! Precomposition of a whole common-reference diagram. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor
universe u
namespace Quillen.Waldhausen.IteratedS.ModelSimplex
variable {V W T : Model.{u}}

/-- Precomposition keeps all vertices and their actual reference transformations. -/
theorem ofIsos_precomp {k : ℕ} (F₀ : V ⟶ W) (F : Fin (k + 1) → (V ⟶ W))
    (ρ : ∀ i, F₀.functor ≅ (F i).functor) (J : T ⟶ V) :
    (ofIsos F₀ F ρ).precomp J =
      ofIsos (J ≫ F₀) (fun i ↦ J ≫ F i) (fun i ↦ isoWhiskerLeft J.functor (ρ i)) := by
  apply ext_diagram
  refine CategoryTheory.Functor.hext (fun _ ↦ rfl) ?_
  intro i j f
  apply heq_of_eq
  change whiskerLeft J.functor ((ρ i).inv ≫ (ρ j).hom) =
    whiskerLeft J.functor (ρ i).inv ≫ whiskerLeft J.functor (ρ j).hom
  exact whiskerLeft_comp _ _ _

end Quillen.Waldhausen.IteratedS.ModelSimplex
