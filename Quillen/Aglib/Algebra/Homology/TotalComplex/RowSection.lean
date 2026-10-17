/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.Algebra.Homology.TotalComplex.Coordinates

/-! # Degreewise sections of the actual total map from split rows -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Quillen.HomologicalAlgebra

variable {K L : HomologicalComplex₂ (ModuleCat.{u} ℤ)
  (ComplexShape.down ℕ) (ComplexShape.down ℕ)}
  (s : ∀ i, L.X i ⟶ K.X i)

/-- Totalizing row sections only as a degreewise map requires no outer naturality. -/
def totalRowSection (n : ℕ) :
    (L.total (ComplexShape.down ℕ)).X n ⟶ (K.total (ComplexShape.down ℕ)).X n :=
  L.totalDesc fun i p hip ↦ (s i).f p ≫ K.ιTotal (ComplexShape.down ℕ) i p n hip

@[reassoc (attr := simp)]
theorem ι_totalRowSection (n i p : ℕ) (hip : i + p = n) :
    L.ιTotal (ComplexShape.down ℕ) i p n hip ≫ totalRowSection s n =
      (s i).f p ≫ K.ιTotal (ComplexShape.down ℕ) i p n hip := by
  simp [totalRowSection]

/-- Strict row sections provide strict degreewise sections of the original total map. -/
@[reassoc]
theorem totalRowSection_map (f : K ⟶ L) (hs : ∀ i, s i ≫ f.f i = 𝟙 _) (n : ℕ) :
    totalRowSection s n ≫ (HomologicalComplex₂.total.map f (ComplexShape.down ℕ)).f n =
      𝟙 _ := by
  apply HomologicalComplex₂.total.hom_ext
  intro i p hip
  rw [ι_totalRowSection_assoc, HomologicalComplex₂.ιTotal_map,
    ← Category.assoc]
  have heq := congrArg (fun a ↦ a.f p) (hs i)
  change (s i).f p ≫ (f.f i).f p = 𝟙 _ at heq
  rw [heq, Category.id_comp, Category.comp_id]

/-- Consequently the actual total augmentation is surjective in every degree. -/
theorem total_map_surjective (f : K ⟶ L) (hs : ∀ i, s i ≫ f.f i = 𝟙 _) (n : ℕ) :
    Function.Surjective ((HomologicalComplex₂.total.map f (ComplexShape.down ℕ)).f n) := by
  intro y
  exact ⟨totalRowSection s n y, congrArg (fun a ↦ a y) (totalRowSection_map s f hs n)⟩

end Quillen.HomologicalAlgebra
