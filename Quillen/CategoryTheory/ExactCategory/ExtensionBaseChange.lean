/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.ExactCategory.ExtensionFiber
public import Quillen.CategoryTheory.QConstruction.Basic

/-!
# Base change of extension fibers

Pullback is required only for admissible epimorphisms, as supplied by the exact
structure. No ambient finite-limit assumption is imposed. A Q span transports
extensions by pullback along its inflation followed by composition with its
deflation. Descent and compositional coherence remain separate obligations.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
namespace Quillen.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C)

local instance extensionHasPullback {X Y : C} (f : X ⟶ Y) (p : E.ExtensionOver Y) :
    HasPullback p.obj.hom f := E.deflation.hasPullback f p.property

/-- Pull back admissible epimorphisms along any map, using exactly the existing
exact-category pullback axiom. -/
def extensionPullback {X Y : C} (f : X ⟶ Y) : E.ExtensionOver Y ⥤ E.ExtensionOver X where
  obj p := ⟨Over.mk (pullback.snd p.obj.hom f),
    E.deflation.pullback_snd _ _ p.property⟩
  map {p q} g := ObjectProperty.homMk (Over.homMk
    (pullback.lift (pullback.fst _ _ ≫ g.hom.left) (pullback.snd _ _)
      (by rw [Category.assoc, Over.w, pullback.condition])) (by simp))
  map_id p := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp
  map_comp g h := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp [Category.assoc]

/-- Pullback on the isomorphism groupoids of extensions. -/
def extensionFiberPullback {X Y : C} (f : X ⟶ Y) :
    E.ExtensionFiber Y ⥤ E.ExtensionFiber X := (E.extensionPullback f).core

/-- Contravariant transport attached to an actual original Q-span representative.
This is not yet a functor out of the quotient Q category. -/
def extensionSpanTransport {X Y : C} (s : Span E.deflation E.inflation X Y) :
    E.ExtensionFiber Y ⥤ E.ExtensionFiber X :=
  E.extensionFiberPullback s.r ⋙ E.extensionFiberPostcompose s.l s.wl

end Quillen.ExactStructure
