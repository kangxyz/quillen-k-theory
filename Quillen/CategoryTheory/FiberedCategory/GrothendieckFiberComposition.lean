/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.FiberedCategory.GrothendieckFiberMap

/-!
# Original fiber components of composite lifted arrows

The equations retain the actual pseudofunctor unit and composition comparisons, including the
canonical transports from the given strict fibers.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Bicategory
universe u v u' v'
namespace Quillen.CategoryTheory.GrothendieckFiber
variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'})

/-- Equality of actual lifted arrows preserves their original fiber components. -/
theorem liftedMap_congr {R S : C} (f : R ⟶ S)
    {x : Functor.Fiber (Pseudofunctor.Grothendieck.forget F) R}
    {y : Functor.Fiber (Pseudofunctor.Grothendieck.forget F) S}
    (φ ψ : x.val ⟶ y.val)
    [(Pseudofunctor.Grothendieck.forget F).IsHomLift f φ]
    [(Pseudofunctor.Grothendieck.forget F).IsHomLift f ψ] (h : φ = ψ) :
    liftedMap F f φ = liftedMap F f ψ := by
  subst ψ
  rfl

/-- Fiber extraction preserves composition with the actual pseudofunctor comparison. -/
theorem liftedMap_comp {R S T : C} (f : R ⟶ S) (g : S ⟶ T)
    {x : Functor.Fiber (Pseudofunctor.Grothendieck.forget F) R}
    {y : Functor.Fiber (Pseudofunctor.Grothendieck.forget F) S}
    {z : Functor.Fiber (Pseudofunctor.Grothendieck.forget F) T}
    (φ : x.val ⟶ y.val) (ψ : y.val ⟶ z.val)
    [(Pseudofunctor.Grothendieck.forget F).IsHomLift f φ]
    [(Pseudofunctor.Grothendieck.forget F).IsHomLift g ψ] :
    liftedMap F (f ≫ g) (φ ≫ ψ) =
      (F.mapComp f.toLoc g.toLoc).hom.toNatTrans.app (originalObject F R x) ≫
        (F.map g.toLoc).toFunctor.map (liftedMap F f φ) ≫ liftedMap F g ψ := by
  rcases x with ⟨⟨R', x⟩, hx⟩
  rcases y with ⟨⟨S', y⟩, hy⟩
  rcases z with ⟨⟨T', z⟩, hz⟩
  change R' = R at hx
  change S' = S at hy
  change T' = T at hz
  subst R'
  subst S'
  subst T'
  have hf : φ.base = f := by
    simpa using IsHomLift.fac' (Pseudofunctor.Grothendieck.forget F) f φ
  have hg : ψ.base = g := by
    simpa using IsHomLift.fac' (Pseudofunctor.Grothendieck.forget F) g ψ
  subst f
  subst g
  rw [liftedMap_mk F (φ.base ≫ ψ.base) x z (φ ≫ ψ) rfl]
  simp only [liftedMap_mk, eqToHom_refl, Category.id_comp,
    Pseudofunctor.Grothendieck.categoryStruct_comp_fiber]
  rfl

/-- Fiber extraction of the identity retains the actual pseudofunctor unit. -/
theorem liftedMap_id {R : C}
    (x : Functor.Fiber (Pseudofunctor.Grothendieck.forget F) R) :
    letI := IsHomLift.id x.property
    liftedMap F (𝟙 R) (𝟙 x.val) =
      (F.mapId ⟨R⟩).hom.toNatTrans.app (originalObject F R x) := by
  rcases x with ⟨⟨R', x⟩, hx⟩
  change R' = R at hx
  subst R'
  have : (Pseudofunctor.Grothendieck.forget F).IsHomLift (𝟙 R)
      (𝟙 (⟨R, x⟩ : Pseudofunctor.Grothendieck F)) := IsHomLift.id rfl
  rw [liftedMap_mk F (𝟙 R) x x (𝟙 _) rfl]
  simp only [eqToHom_refl, Category.id_comp,
    Pseudofunctor.Grothendieck.categoryStruct_id_fiber]
  rfl

end Quillen.CategoryTheory.GrothendieckFiber
