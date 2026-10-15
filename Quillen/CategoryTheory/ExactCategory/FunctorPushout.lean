/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Basic
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.CategoryTheory.ExactCategory.MatrixInflation
public import Quillen.CategoryTheory.ExactCategory.Functor
public import Quillen.KTheory.GrothendieckComparison.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# Genuine exact functors preserve pushouts along admissible monomorphisms

A pushout is expressed by its actual biproduct cokernel sequence. Its first
map is admissible, so exactness preserves this conflation. The canonical
biproduct comparison then recovers the original mapped pushout square.
-/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe v u v' u'
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  preservesBinaryBiproducts_of_preservesBiproducts

namespace Quillen

section PushoutCokernel
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  {A B D P : C} {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ P} {j : D ⟶ P}

/-- The actual biproduct sequence of a commutative square. -/
def pushoutShortComplex (w : i ≫ g = f ≫ j) : ShortComplex C :=
  ShortComplex.mk (biprod.lift i (-f)) (biprod.desc g j) (by simp [w])

/-- A genuine pushout is the cokernel of its actual difference map. -/
def isCokernelOfBiprodPushout (h : IsPushout i f g j) :
    IsColimit (CokernelCofork.ofπ (pushoutShortComplex h.w).g (pushoutShortComplex h.w).zero) := by
  refine CokernelCofork.IsColimit.ofπ _ _ (fun a ha ↦
    h.desc (biprod.inl ≫ a) (biprod.inr ≫ a) (by
      have hh : i ≫ biprod.inl ≫ a - f ≫ biprod.inr ≫ a = 0 := by
        simpa [pushoutShortComplex, biprod.lift_eq, Category.assoc, sub_eq_add_neg] using ha
      exact sub_eq_zero.mp hh)) ?_ ?_
  · intro W a ha
    apply biprod.hom_ext' <;> simp [pushoutShortComplex]
  · intro W a ha m hm
    apply h.hom_ext
    · simpa [pushoutShortComplex] using congrArg (fun k ↦ biprod.inl ≫ k) hm
    · simpa [pushoutShortComplex] using congrArg (fun k ↦ biprod.inr ≫ k) hm

/-- Conversely, the actual biproduct cokernel universal property gives the pushout. -/
theorem isPushoutOfBiprodCokernel (w : i ≫ g = f ≫ j)
    (hc : IsColimit (CokernelCofork.ofπ (pushoutShortComplex w).g (pushoutShortComplex w).zero)) :
    IsPushout i f g j := by
  apply IsPushout.mk' w
  · intro W a b ha hb
    apply Cofork.IsColimit.hom_ext hc
    apply biprod.hom_ext'
    · simpa [pushoutShortComplex] using ha
    · simpa [pushoutShortComplex] using hb
  · intro W a b hab
    let z : (pushoutShortComplex w).f ≫ biprod.desc a b = 0 := by
      simp [pushoutShortComplex, hab]
    let q := hc.desc (CokernelCofork.ofπ (biprod.desc a b) z)
    have hq : (pushoutShortComplex w).g ≫ q = biprod.desc a b :=
      hc.fac _ WalkingParallelPair.one
    exact ⟨q,
      by simpa [pushoutShortComplex] using congrArg (fun k ↦ biprod.inl ≫ k) hq,
      by simpa [pushoutShortComplex] using congrArg (fun k ↦ biprod.inr ≫ k) hq⟩

end PushoutCokernel

end Quillen

namespace CategoryTheory.ExactCategory.ExactFunctor
open Quillen
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D} (F : ExactFunctor EC ED)

/-- A genuine exact functor preserves any actual pushout along an admissible mono. -/
theorem map_isPushout {A B T P : C} {i : A ⟶ B} {f : A ⟶ T}
    {g : B ⟶ P} {j : T ⟶ P} (hi : EC.inflation i) (h : IsPushout i f g j) :
    IsPushout (F.toFunctor.map i) (F.toFunctor.map f)
      (F.toFunctor.map g) (F.toFunctor.map j) := by
  let S := pushoutShortComplex h.w
  have hS : EC.conflation S := EC.conflation_of_inflation_of_isCokernel
    (EC.inflation_biprod_lift i (-f) hi) (isCokernelOfBiprodPushout h)
  have w : F.toFunctor.map i ≫ F.toFunctor.map g =
      F.toFunctor.map f ≫ F.toFunctor.map j := by
    simp only [← F.toFunctor.map_comp, h.w]
  let e : S.map F.toFunctor ≅ pushoutShortComplex w :=
    ShortComplex.isoMk (Iso.refl _) (F.toFunctor.mapBiprod B T) (Iso.refl _)
      (by
        change 𝟙 _ ≫ biprod.lift (F.toFunctor.map i) (-F.toFunctor.map f) =
          F.toFunctor.map (biprod.lift i (-f)) ≫ (F.toFunctor.mapBiprod B T).hom
        rw [Category.id_comp, biprod.map_lift_mapBiprod, F.toFunctor.map_neg])
      (by
        change (F.toFunctor.mapBiprod B T).hom ≫
          biprod.desc (F.toFunctor.map g) (F.toFunctor.map j) =
          F.toFunctor.map (biprod.desc g j) ≫ 𝟙 _
        rw [Category.comp_id, biprod.mapBiprod_hom_desc])
  exact isPushoutOfBiprodCokernel w
    (ED.cokernel _ (ED.iso_closed e (F.map_conflation S hS)))

end CategoryTheory.ExactCategory.ExactFunctor

namespace Quillen
end Quillen
