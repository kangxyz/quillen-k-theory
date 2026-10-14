/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceFaces

/-! Exact equality transport of an existing common-reference node. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor
universe u v w z
namespace Quillen.Waldhausen.IteratedS.ModelSimplex
variable {V W : Model.{u}}

/-- A functor equality and its actual reference equation identify the complete node. -/
theorem reference_node_eq {F₀ F G : V ⟶ W} (h : F.functor = G.functor)
    (ρ : F₀.functor ≅ F.functor) (σ : F₀.functor ≅ G.functor)
    (he : ρ.hom ≫ eqToHom h = σ.hom) :
    (⟨F, ρ⟩ : Σ H : V ⟶ W, F₀.functor ≅ H.functor) = ⟨G, σ⟩ := by
  have hFG : F = G := Model.Hom.ext h
  subst G
  have hρ : ρ = σ := Iso.ext (by simpa only [eqToHom_refl, Category.comp_id] using he)
  subst σ
  rfl

/-- The original parameter-dependent isomorphism, anchored only by the supplied functor equality. -/
def transportedReferenceNode {I : Type v} (F₀ : V ⟶ W) (S T : I → (V ⟶ W))
    (ρ : ∀ i, (S i).functor ≅ (T i).functor) (i : I) (e : F₀.functor = (S i).functor) :
    Σ F : V ⟶ W, F₀.functor ≅ F.functor := ⟨T i, eqToIso e ≪≫ ρ i⟩

/-- Equality of the original parameter retains the entire anchored node. -/
theorem transportedReferenceNode_congr {I : Type v} (F₀ : V ⟶ W) (S T : I → (V ⟶ W))
    (ρ : ∀ i, (S i).functor ≅ (T i).functor) {i j : I} (h : i = j)
    (ei : F₀.functor = (S i).functor) (ej : F₀.functor = (S j).functor) :
    transportedReferenceNode F₀ S T ρ i ei = transportedReferenceNode F₀ S T ρ j ej := by
  subst j
  rfl
end Quillen.Waldhausen.IteratedS.ModelSimplex

namespace CategoryTheory
/-- Whiskering retains a literal equality transport before the original isomorphism. -/
theorem whiskering_eqToIso_trans {A : Type u} {B : Type v} {C : Type w} {D : Type z}
    [Category A] [Category B] [Category C] [Category D]
    (L : A ⥤ B) (R : C ⥤ D) {F G H : B ⥤ C} (e : F = G) (ρ : G ≅ H) :
    isoWhiskerLeft L (isoWhiskerRight (eqToIso e ≪≫ ρ) R) =
      eqToIso (congrArg (fun K ↦ L ⋙ K ⋙ R) e) ≪≫ isoWhiskerLeft L (isoWhiskerRight ρ R) := by
  subst G
  simp
end CategoryTheory
