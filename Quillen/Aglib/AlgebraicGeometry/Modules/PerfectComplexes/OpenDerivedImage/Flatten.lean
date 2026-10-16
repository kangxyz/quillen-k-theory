/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.OpenDerivedImage.Exact

/-!
# Flattening the actual derived-image categories

The redundant perfect-object wrapper is forgotten and restored by a literal equivalence. Objects, chain maps and original inclusions are unchanged.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.PerfectComplexes.OpenDerivedImage
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Forget only the redundant perfect-object wrapper. -/
def flatten : Obj j ⥤ ComplexObj j where
  obj A := ⟨A.obj.obj, A.property⟩
  map f := (complexObjects j).homMk f.hom.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Restore the proved local perfectness of the same original complex. -/
def nest : ComplexObj j ⥤ Obj j where
  obj A := ⟨⟨A.obj, locallyPerfect_of_mem j A.property⟩, A.property⟩
  map f := (objects j).homMk ((locallyPerfect U).homMk f.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem flatten_comp_nest : flatten j ⋙ nest j = 𝟭 (Obj j) := rfl
@[simp] theorem nest_comp_flatten : nest j ⋙ flatten j = 𝟭 (ComplexObj j) := rfl

/-- A genuine equivalence on unchanged original complexes and chain maps. -/
def flattenEquivalence : Obj j ≌ ComplexObj j where
  functor := flatten j
  inverse := nest j
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
    (by intros; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)
    (by intros; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)

/-- Flattening retains the literal original perfect-complex inclusion. -/
@[simp] theorem flatten_comp_inclusion : flatten j ⋙ inclusion j = (objects j).ι := rfl
@[simp] theorem nest_comp_inclusion : nest j ⋙ (objects j).ι = inclusion j := rfl

end Quillen.PerfectComplexes.OpenDerivedImage

end

end
