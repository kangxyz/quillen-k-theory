/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.CategoryTheory.ExactCategory.Functor
public import Quillen.CategoryTheory.ExactCategory.ExtensionTotal
public import Quillen.CategoryTheory.SubdivisionFunctor

/-! # Exact functors on total extensions and their original cokernels -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactCategory.ExactStructure
open Quillen
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

/-- Any actual cokernel of an admissible inflation belongs to its conflation. -/
lemma conflation_of_isCokernel (E : ExactStructure C) {X Y Z : C}
    {i : X ⟶ Y} {p : Y ⟶ Z} (h : i ≫ p = 0)
    (hp : IsColimit (CokernelCofork.ofπ p h)) (hi : E.inflation i) :
    E.conflation (ShortComplex.mk i p h) := by
  obtain ⟨Z', p', h', hs⟩ := hi
  let hp' := E.cokernel (ShortComplex.mk i p' h') hs
  let e : Z' ≅ Z := hp'.coconePointUniqueUpToIso hp
  have he : p' ≫ e.hom = p :=
    hp'.comp_coconePointUniqueUpToIso_hom hp WalkingParallelPair.one
  let se : ShortComplex.mk i p' h' ≅ ShortComplex.mk i p h :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e (by simp) (by simpa using he.symm)
  exact E.iso_closed se hs

end CategoryTheory.ExactCategory.ExactStructure

namespace CategoryTheory.ExactCategory.ExactFunctor
open Quillen
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {E : ExactStructure C} {E' : ExactStructure D} (F : ExactFunctor E E')

/-- Exactness preserves the specified cokernel of an admissible inflation. -/
def mapInflationCokernel {X Y Z : C} {i : X ⟶ Y} {p : Y ⟶ Z}
    (h : i ≫ p = 0) (hp : IsColimit (CokernelCofork.ofπ p h)) (hi : E.inflation i) :
    IsColimit (CokernelCofork.ofπ (F.toFunctor.map p)
      (show F.toFunctor.map i ≫ F.toFunctor.map p = 0 by
        rw [← F.toFunctor.map_comp, h, F.toFunctor.map_zero])) :=
  E'.cokernel _ (F.map_conflation _ (E.conflation_of_isCokernel h hp hi))

/-- An exact functor sends the actual admissible-inflation category to its target. -/
def inflationFunctor : E.InflationCategory ⥤ E'.InflationCategory where
  obj X := ⟨F.toFunctor.obj X.obj⟩
  map f := ⟨F.toFunctor.map f.hom, F.map_inflation f.hom f.property⟩
  map_id X := WideSubcategory.hom_ext E'.inflation (F.toFunctor.map_id X.obj)
  map_comp f g := WideSubcategory.hom_ext E'.inflation (F.toFunctor.map_comp f.hom g.hom)

/-- The map acts on the original subdivision model of total extensions. -/
def extensionTotalFunctor : E.ExtensionTotal ⥤ E'.ExtensionTotal :=
  Subdivision.map F.inflationFunctor

/-- The original middle-object projection commutes with the exact functor. -/
theorem extensionTotalFunctor_middle :
    F.extensionTotalFunctor ⋙ E'.extensionTotalMiddle = E.extensionTotalMiddle ⋙ F.toFunctor := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro x y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- The genuine original quotient presentation after applying the exact functor. -/
def mapExtensionQuotientData (x : E.ExtensionTotal) :
    E'.ExtensionQuotientData (F.extensionTotalFunctor.obj x) where
  obj := F.toFunctor.obj (E.extensionQuotientData x).obj
  π := F.toFunctor.map (E.extensionQuotientData x).π
  zero := by
    change F.toFunctor.map x.fiber.unop.hom.hom ≫
      F.toFunctor.map (E.extensionQuotientData x).π = 0
    rw [← F.toFunctor.map_comp, (E.extensionQuotientData x).zero, F.toFunctor.map_zero]
  conflation := F.map_conflation _ (E.extensionQuotientData x).conflation

/-- The canonical comparison of the mapped quotient and the chosen target quotient. -/
def extensionQuotientIso (x : E.ExtensionTotal) :
    F.toFunctor.obj (E.extensionQuotientData x).obj ≅
      (E'.extensionQuotientData (F.extensionTotalFunctor.obj x)).obj :=
  (F.mapExtensionQuotientData x).iso E' (E'.extensionQuotientData _)

/-- The canonical comparison retains the original quotient projection. -/
@[reassoc] theorem extensionQuotientIso_π (x : E.ExtensionTotal) :
    F.toFunctor.map (E.extensionQuotientData x).π ≫ (F.extensionQuotientIso x).hom =
      (E'.extensionQuotientData (F.extensionTotalFunctor.obj x)).π :=
  (F.mapExtensionQuotientData x).π_iso_hom E' (E'.extensionQuotientData _)

end CategoryTheory.ExactCategory.ExactFunctor
