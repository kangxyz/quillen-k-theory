/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.CategoryTheory.FiberedCategory.CocartesianSections

/-!
# Actual postcomposition of strict sections

A functor over the unchanged base maps actual strict sections by postcomposition. If it
preserves the given strongly cocartesian arrows, it maps their full subcategory as well.
No new lift or replacement section is chosen.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u v u' v' u'' v'' uJ vJ
namespace Quillen.CategoryTheory.StrictSections
variable {C : Type u} [Category.{v} C] {E : Type u'} [Category.{v'} E]
    {E' : Type u''} [Category.{v''} E'] {J : Type uJ} [Category.{vJ} J]
    (π : E ⥤ C) (π' : E' ⥤ C) (F : E ⥤ E') (h : F ⋙ π' = π) (q : J ⥤ C)

include h in
/-- Original postcomposition lies over the identical base diagram. -/
theorem postcompose_over :
    ((Functor.Fiber.fiberInclusion : StrictSections π q ⥤ (J ⥤ E)) ⋙
        (Functor.whiskeringRight J E E').obj F) ⋙
          (Functor.whiskeringRight J E' C).obj π' =
      (Functor.const (StrictSections π q)).obj q := by
  have hc : (Functor.whiskeringRight J E E').obj F ⋙
      (Functor.whiskeringRight J E' C).obj π' =
        (Functor.whiskeringRight J E C).obj π := by
    subst π
    rfl
  change (Functor.Fiber.fiberInclusion : StrictSections π q ⥤ (J ⥤ E)) ⋙
    ((Functor.whiskeringRight J E E').obj F ⋙
      (Functor.whiskeringRight J E' C).obj π') = _
  rw [hc]
  exact Functor.Fiber.fiberInclusion_comp_eq_const

/-- Map the original section and every vertical map by the specified functor. -/
def postcompose : StrictSections π q ⥤ StrictSections π' q :=
  Functor.Fiber.inducedFunctor (postcompose_over π π' F h q)

/-- Every section value is mapped by the original functor, with no replacement choice. -/
theorem postcompose_obj (s : StrictSections π q) (j : J) :
    ((postcompose π π' F h q).obj s).val.obj j = F.obj (s.val.obj j) := rfl

/-- Every original vertical component is mapped literally. -/
theorem postcompose_map {s t : StrictSections π q} (a : s ⟶ t) (j : J) :
    ((postcompose π π' F h q).map a).val.app j = F.map (a.val.app j) := rfl

/-- Actual preservation of cocartesian arrows restricts postcomposition to cocartesian sections. -/
def cocartesianPostcompose
    (hF : ∀ {R S : C} {a b : E} (f : R ⟶ S) (φ : a ⟶ b),
      π.IsStronglyCocartesian f φ → π'.IsStronglyCocartesian f (F.map φ)) :
    CocartesianSections π q ⥤ CocartesianSections π' q :=
  (cocartesian π' q).lift
    ((cocartesian π q).ι ⋙ postcompose π π' F h q)
    (fun s _ _ f => hF (q.map f) (s.obj.val.map f) (s.property f))

end Quillen.CategoryTheory.StrictSections
