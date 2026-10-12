/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.CategoryTheory.Functor.IdentityAutomorphism

/-! Transport an identity-action formula along its specified genuine evaluation isomorphism. -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u v u' v'
namespace Quillen.FunctorIdentityAutomorphism
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- A genuine natural isomorphism transports the same supplied forward identity action. -/
theorem map_hom_eq_of_iso (F G : C ⥤ D) (η : F ≅ G)
    (a : 𝟭 C ≅ 𝟭 C) (b : 𝟭 D ≅ 𝟭 D)
    (h : ∀ x, G.map (a.hom.app x) = b.hom.app (G.obj x)) (x : C) :
    F.map (a.hom.app x) = b.hom.app (F.obj x) := by
  have h₁ := η.hom.naturality (a.hom.app x)
  rw [h x] at h₁
  have h₂ := b.hom.naturality (η.hom.app x)
  simp only [Functor.id_map] at h₂
  exact (cancel_mono (η.hom.app x)).mp (h₁.trans h₂)

end Quillen.FunctorIdentityAutomorphism
