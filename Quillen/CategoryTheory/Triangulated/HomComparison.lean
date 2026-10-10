/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.HomCongr
import Mathlib.Algebra.FiveLemma

/-!
# Original Hom-map comparison through distinguished triangles

For an additive triangulated functor, bijectivity of the original map on Hom
sets propagates through actual distinguished triangles by the five lemma.
Both variables, shifts, and isomorphism transport are treated explicitly.
The resulting source and target object properties are proved triangulated;
no full-faithfulness or replacement hypothesis is packaged into a new record.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject
namespace Quillen.DerivedHomComparison

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)

lemma map_bijective_of_iso {X Y X' Y' : C} (eX : X ≅ X') (eY : Y ≅ Y')
    (h : Function.Bijective (F.map : (X ⟶ Y) → _)) :
    Function.Bijective (F.map : (X' ⟶ Y') → _) := by
  let e := Iso.homCongr eX eY
  let e' := Iso.homCongr (F.mapIso eX) (F.mapIso eY)
  have hc (f : X ⟶ Y) : F.map (e f) = e' (F.map f) := by
    simp [e, e', Iso.homCongr_apply]
  convert (e'.bijective.comp h).comp e.symm.bijective using 1
  funext f
  exact (congrArg F.map (e.apply_symm_apply f)).symm.trans (hc (e.symm f))

variable [HasShift C ℤ] [HasShift D ℤ] [F.CommShift ℤ]

lemma map_bijective_shift {X Y : C}
    (h : Function.Bijective (F.map : (X ⟶ Y) → _)) (n : ℤ) :
    Function.Bijective (F.map : (X⟦n⟧ ⟶ Y⟦n⟧) → _) := by
  let e := (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor C n)).homEquiv (X := X) (Y := Y)
  let e' := (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor D n)).homEquiv
    (X := F.obj X) (Y := F.obj Y)
  let e'' := Iso.homCongr ((F.commShiftIso n).app X).symm ((F.commShiftIso n).app Y).symm
  have hc (f : X ⟶ Y) : F.map (e f) = e'' (e' (F.map f)) := by
    change F.map (f⟦n⟧') = (F.commShiftIso n).hom.app X ≫
      (F.map f)⟦n⟧' ≫ (F.commShiftIso n).inv.app Y
    rw [← F.commShiftIso_hom_naturality_assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  convert! ((e''.bijective.comp e'.bijective).comp h).comp e.symm.bijective using 1
  funext f
  exact (congrArg F.map (e.apply_symm_apply f)).symm.trans (hc (e.symm f))

end Quillen.DerivedHomComparison

namespace Quillen.DerivedHomComparison

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

lemma rightComp_exact₁₂ (X : C) (T : Triangle C) (hT : T ∈ distTriang C) :
    Function.Exact (Preadditive.rightComp X T.mor₁) (Preadditive.rightComp X T.mor₂) := by
  intro f
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := T.coyoneda_exact₂ hT f hf
    exact ⟨g, hg.symm⟩
  · rintro ⟨g, rfl⟩
    change (g ≫ T.mor₁) ≫ T.mor₂ = 0
    rw [Category.assoc, comp_distTriang_mor_zero₁₂ T hT, comp_zero]

lemma rightComp_exact₂₃ (X : C) (T : Triangle C) (hT : T ∈ distTriang C) :
    Function.Exact (Preadditive.rightComp X T.mor₂) (Preadditive.rightComp X T.mor₃) := by
  intro f
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := T.coyoneda_exact₃ hT f hf
    exact ⟨g, hg.symm⟩
  · rintro ⟨g, rfl⟩
    change (g ≫ T.mor₂) ≫ T.mor₃ = 0
    rw [Category.assoc, comp_distTriang_mor_zero₂₃ T hT, comp_zero]

lemma rightComp_exact₃₁ (X : C) (T : Triangle C) (hT : T ∈ distTriang C) :
    Function.Exact (Preadditive.rightComp X T.mor₃)
      (Preadditive.rightComp X (T.mor₁⟦(1 : ℤ)⟧')) := by
  intro f
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := T.coyoneda_exact₁ hT f hf
    exact ⟨g, hg.symm⟩
  · rintro ⟨g, rfl⟩
    change (g ≫ T.mor₃) ≫ T.mor₁⟦(1 : ℤ)⟧' = 0
    rw [Category.assoc, comp_distTriang_mor_zero₃₁ T hT, comp_zero]

variable (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]

def shiftedMapAddHom (X Y : C) (n : ℤ) :
    (X ⟶ Y⟦n⟧) →+ (F.obj X ⟶ (F.obj Y)⟦n⟧) :=
  (Preadditive.rightComp (F.obj X) ((F.commShiftIso n).hom.app Y)).comp F.mapAddHom

omit [HasZeroObject C] [HasZeroObject D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D] [F.IsTriangulated] in
lemma shiftedMapAddHom_bijective (X Y : C) (n : ℤ)
    (h : Function.Bijective (F.map : (X ⟶ Y⟦n⟧) → _)) :
    Function.Bijective (shiftedMapAddHom F X Y n) :=
  ((F.commShiftIso n).app Y).homToEquiv.bijective.comp h

lemma map_bijective_target_triangle₃ (X : C) (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : Function.Bijective (F.map : (X ⟶ T.obj₁) → _))
    (h₂ : Function.Bijective (F.map : (X ⟶ T.obj₂) → _))
    (h₁s : Function.Bijective (F.map : (X ⟶ T.obj₁⟦(1 : ℤ)⟧) → _))
    (h₂s : Function.Bijective (F.map : (X ⟶ T.obj₂⟦(1 : ℤ)⟧) → _)) :
    Function.Bijective (F.map : (X ⟶ T.obj₃) → _) := by
  let T' := F.mapTriangle.obj T
  have hT' : T' ∈ distTriang D := F.map_distinguished T hT
  exact AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (Preadditive.rightComp X T.mor₁) (Preadditive.rightComp X T.mor₂)
    (Preadditive.rightComp X T.mor₃) (Preadditive.rightComp X (T.mor₁⟦(1 : ℤ)⟧'))
    (Preadditive.rightComp (F.obj X) T'.mor₁) (Preadditive.rightComp (F.obj X) T'.mor₂)
    (Preadditive.rightComp (F.obj X) T'.mor₃)
    (Preadditive.rightComp (F.obj X) (T'.mor₁⟦(1 : ℤ)⟧'))
    F.mapAddHom F.mapAddHom F.mapAddHom
    (shiftedMapAddHom F X T.obj₁ 1) (shiftedMapAddHom F X T.obj₂ 1)
    (by ext f; exact (F.map_comp f T.mor₁).symm)
    (by ext f; exact (F.map_comp f T.mor₂).symm)
    (by
      ext f
      change F.map f ≫ (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app _) =
        F.map (f ≫ T.mor₃) ≫ (F.commShiftIso (1 : ℤ)).hom.app _
      rw [Functor.map_comp, Category.assoc])
    (by
      ext f
      change (F.map f ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
        (F.map T.mor₁)⟦(1 : ℤ)⟧' =
        F.map (f ≫ T.mor₁⟦(1 : ℤ)⟧') ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₂
      rw [Functor.map_comp, Category.assoc, Category.assoc,
        F.commShiftIso_hom_naturality])
    (rightComp_exact₁₂ X T hT) (rightComp_exact₂₃ X T hT) (rightComp_exact₃₁ X T hT)
    (rightComp_exact₁₂ (F.obj X) T' hT') (rightComp_exact₂₃ (F.obj X) T' hT')
    (rightComp_exact₃₁ (F.obj X) T' hT') h₁.surjective h₂
    (shiftedMapAddHom_bijective F X T.obj₁ 1 h₁s)
    (shiftedMapAddHom_bijective F X T.obj₂ 1 h₂s).injective

end Quillen.DerivedHomComparison

namespace Quillen.DerivedHomComparison

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

lemma leftComp_exact₂₁ (Y : C) (T : Triangle C) (hT : T ∈ distTriang C) :
    Function.Exact (Preadditive.leftComp Y T.mor₂) (Preadditive.leftComp Y T.mor₁) := by
  intro f
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := T.yoneda_exact₂ hT f hf
    exact ⟨g, hg.symm⟩
  · rintro ⟨g, rfl⟩
    change T.mor₁ ≫ (T.mor₂ ≫ g) = 0
    rw [← Category.assoc, comp_distTriang_mor_zero₁₂ T hT, zero_comp]

lemma leftComp_exact₃₂ (Y : C) (T : Triangle C) (hT : T ∈ distTriang C) :
    Function.Exact (Preadditive.leftComp Y T.mor₃) (Preadditive.leftComp Y T.mor₂) := by
  intro f
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := T.yoneda_exact₃ hT f hf
    exact ⟨g, hg.symm⟩
  · rintro ⟨g, rfl⟩
    change T.mor₂ ≫ (T.mor₃ ≫ g) = 0
    rw [← Category.assoc, comp_distTriang_mor_zero₂₃ T hT, zero_comp]

lemma leftComp_exact₁₃ (Y : C) (T : Triangle C) (hT : T ∈ distTriang C) :
    Function.Exact (Preadditive.leftComp Y (T.mor₁⟦(1 : ℤ)⟧'))
      (Preadditive.leftComp Y T.mor₃) := by
  intro f
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := T.rotate.yoneda_exact₃ (rot_of_distTriang _ hT) f hf
    refine ⟨-g, ?_⟩
    change T.mor₁⟦(1 : ℤ)⟧' ≫ (-g) = f
    simpa using hg.symm
  · rintro ⟨g, rfl⟩
    change T.mor₃ ≫ (T.mor₁⟦(1 : ℤ)⟧' ≫ g) = 0
    rw [← Category.assoc, comp_distTriang_mor_zero₃₁ T hT, zero_comp]

variable (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]

def shiftedSourceMapAddHom (X Y : C) (n : ℤ) :
    (X⟦n⟧ ⟶ Y) →+ ((F.obj X)⟦n⟧ ⟶ F.obj Y) :=
  (Preadditive.leftComp (F.obj Y) ((F.commShiftIso n).inv.app X)).comp F.mapAddHom

omit [HasZeroObject C] [HasZeroObject D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D] [F.IsTriangulated] in
lemma shiftedSourceMapAddHom_bijective (X Y : C) (n : ℤ)
    (h : Function.Bijective (F.map : (X⟦n⟧ ⟶ Y) → _)) :
    Function.Bijective (shiftedSourceMapAddHom F X Y n) :=
  ((F.commShiftIso n).app X).homFromEquiv.bijective.comp h

lemma map_bijective_source_triangle₃ (Y : C) (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : Function.Bijective (F.map : (T.obj₁ ⟶ Y) → _))
    (h₂ : Function.Bijective (F.map : (T.obj₂ ⟶ Y) → _))
    (h₁s : Function.Bijective (F.map : (T.obj₁⟦(1 : ℤ)⟧ ⟶ Y) → _))
    (h₂s : Function.Bijective (F.map : (T.obj₂⟦(1 : ℤ)⟧ ⟶ Y) → _)) :
    Function.Bijective (F.map : (T.obj₃ ⟶ Y) → _) := by
  let T' := F.mapTriangle.obj T
  have hT' : T' ∈ distTriang D := F.map_distinguished T hT
  exact AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (Preadditive.leftComp Y (T.mor₁⟦(1 : ℤ)⟧')) (Preadditive.leftComp Y T.mor₃)
    (Preadditive.leftComp Y T.mor₂) (Preadditive.leftComp Y T.mor₁)
    (Preadditive.leftComp (F.obj Y) (T'.mor₁⟦(1 : ℤ)⟧'))
    (Preadditive.leftComp (F.obj Y) T'.mor₃)
    (Preadditive.leftComp (F.obj Y) T'.mor₂) (Preadditive.leftComp (F.obj Y) T'.mor₁)
    (shiftedSourceMapAddHom F T.obj₂ Y 1) (shiftedSourceMapAddHom F T.obj₁ Y 1)
    F.mapAddHom F.mapAddHom F.mapAddHom
    (by
      ext f
      change (F.map T.mor₁)⟦(1 : ℤ)⟧' ≫ ((F.commShiftIso 1).inv.app T.obj₂ ≫ F.map f) =
        (F.commShiftIso 1).inv.app T.obj₁ ≫ F.map (T.mor₁⟦(1 : ℤ)⟧' ≫ f)
      rw [Functor.map_comp, ← Category.assoc, F.commShiftIso_inv_naturality, Category.assoc])
    (by
      ext f
      change (F.map T.mor₃ ≫ (F.commShiftIso 1).hom.app _) ≫
        ((F.commShiftIso 1).inv.app _ ≫ F.map f) = F.map (T.mor₃ ≫ f)
      simp)
    (by ext f; exact (F.map_comp T.mor₂ f).symm)
    (by ext f; exact (F.map_comp T.mor₁ f).symm)
    (leftComp_exact₁₃ Y T hT) (leftComp_exact₃₂ Y T hT) (leftComp_exact₂₁ Y T hT)
    (leftComp_exact₁₃ (F.obj Y) T' hT') (leftComp_exact₃₂ (F.obj Y) T' hT')
    (leftComp_exact₂₁ (F.obj Y) T' hT')
    (shiftedSourceMapAddHom_bijective F T.obj₂ Y 1 h₂s).surjective
    (shiftedSourceMapAddHom_bijective F T.obj₁ Y 1 h₁s) h₂ h₁.injective

end Quillen.DerivedHomComparison

namespace Quillen.DerivedHomComparison

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]

def rightHomComparison (X : C) : ObjectProperty C :=
  fun Y => ∀ n : ℤ, Function.Bijective (F.map : (X ⟶ Y⟦n⟧) → _)

instance (X : C) : (rightHomComparison F X).IsClosedUnderIsomorphisms where
  of_iso e h n := map_bijective_of_iso F (Iso.refl X) ((shiftFunctor C n).mapIso e) (h n)

instance (X : C) : (rightHomComparison F X).IsStableUnderShift ℤ where
  isStableUnderShiftBy a := ⟨fun Y h n =>
    map_bijective_of_iso F (Iso.refl X) ((shiftFunctorAdd C a n).app Y) (h (a + n))⟩

instance (X : C) : (rightHomComparison F X).IsTriangulatedClosed₃ :=
  .mk' (fun T hT h₁ h₂ n =>
    map_bijective_target_triangle₃ F X ((Triangle.shiftFunctor C n).obj T)
      (T.shift_distinguished hT n) (h₁ n) (h₂ n)
      (map_bijective_of_iso F (Iso.refl X) ((shiftFunctorAdd C n 1).app T.obj₁) (h₁ (n + 1)))
      (map_bijective_of_iso F (Iso.refl X) ((shiftFunctorAdd C n 1).app T.obj₂) (h₂ (n + 1))))

instance (X : C) : (rightHomComparison F X).IsTriangulatedClosed₂ :=
  .of_isTriangulatedClosed₃

end Quillen.DerivedHomComparison

namespace Quillen.DerivedHomComparison

section General
variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]

def leftHomComparison (Y : C) : ObjectProperty C :=
  fun X => ∀ n : ℤ, Function.Bijective (F.map : (X⟦n⟧ ⟶ Y) → _)

instance (Y : C) : (leftHomComparison F Y).IsClosedUnderIsomorphisms where
  of_iso e h n := map_bijective_of_iso F ((shiftFunctor C n).mapIso e) (Iso.refl Y) (h n)

instance (Y : C) : (leftHomComparison F Y).IsStableUnderShift ℤ where
  isStableUnderShiftBy a := ⟨fun X h n =>
    map_bijective_of_iso F ((shiftFunctorAdd C a n).app X) (Iso.refl Y) (h (a + n))⟩

instance (Y : C) : (leftHomComparison F Y).IsTriangulatedClosed₃ :=
  .mk' (fun T hT h₁ h₂ n =>
    map_bijective_source_triangle₃ F Y ((Triangle.shiftFunctor C n).obj T)
      (T.shift_distinguished hT n) (h₁ n) (h₂ n)
      (map_bijective_of_iso F ((shiftFunctorAdd C n 1).app T.obj₁) (Iso.refl Y) (h₁ (n + 1)))
      (map_bijective_of_iso F ((shiftFunctorAdd C n 1).app T.obj₂) (Iso.refl Y) (h₂ (n + 1))))

instance (Y : C) : (leftHomComparison F Y).IsTriangulatedClosed₂ :=
  .of_isTriangulatedClosed₃
end General
end Quillen.DerivedHomComparison
