/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# The underlying functor of a full-subcategory lift

The literal lifted functor forgets its object-property proof by the original identity comparison.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueDiagonal
/-- Forgetting a full-subcategory lift retains its entire original functor. -/
def liftUnderlyingIso {C D : Type*} [Category C] [Category D]
    (P : ObjectProperty D) (F : C ⥤ D) (hF : ∀ K, P (F.obj K)) :
    P.lift F hF ⋙ P.ι ≅ F := Iso.refl _


end Quillen.PerfectComplexes.ProjectiveLine.FlasqueDiagonal
end
end
