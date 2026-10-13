/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.Monoidal.TranslationTelescope
public import Quillen.CategoryTheory.Grothendieck.TelescopeShift

/-! # Right stabilization and index shift on the monoidal translation telescope -/

@[expose] public section
noncomputable section
open CategoryTheory MonoidalCategory
universe u v
namespace Quillen.TranslationTelescope
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The actual stagewise right stabilization, retained through the common-universe model. -/
def rightStabilization (e : C) : Model e ⥤ Model e :=
  (modelEquivalence e).functor ⋙ EndofunctorTelescope.stabilization (tensorRight e) ⋙
    (modelEquivalence e).inverse

/-- The actual index shift in the same model as the original left translations. -/
def indexShift (e : C) : Model e ⥤ Model e :=
  (modelEquivalence e).functor ⋙ EndofunctorTelescope.shift (tensorRight e) ⋙
    (modelEquivalence e).inverse

/-- On every original stage, right stabilization is precisely right tensoring by `e`. -/
theorem inclusion_rightStabilization (e : C) (n : ℕ) :
    Grothendieck.ι (diagram e) n ⋙ rightStabilization e =
      (AsSmall.down ⋙ tensorRight e ⋙ AsSmall.up) ⋙ Grothendieck.ι (diagram e) n := by
  rw [rightStabilization, ← Functor.assoc, inclusion_forward]
  rw [Functor.assoc, ← Functor.assoc (Grothendieck.ι _ n),
    EndofunctorTelescope.inclusion_stabilization, Functor.assoc, inclusion_inverse]
  rfl

/-- The common-universe index shift retains the original successor stage. -/
theorem inclusion_indexShift (e : C) (n : ℕ) :
    Grothendieck.ι (diagram e) n ⋙ indexShift e = Grothendieck.ι (diagram e) (n + 1) := by
  rw [indexShift, ← Functor.assoc, inclusion_forward]
  rw [Functor.assoc, ← Functor.assoc (Grothendieck.ι _ n),
    EndofunctorTelescope.inclusion_shift, inclusion_inverse]
  rfl

end Quillen.TranslationTelescope
