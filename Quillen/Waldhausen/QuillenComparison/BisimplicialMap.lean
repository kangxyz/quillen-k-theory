/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.QuillenComparison.RowFull
public import Quillen.Waldhausen.QuillenComparison.ChainClassification
public import Quillen.Waldhausen.QuillenComparison.SimplicialMap
public import Quillen.Waldhausen.QuillenComparison.MixedNerve

/-! # The actual bisimplicial row comparison -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe v u

namespace Quillen.Waldhausen.QuillenComparison

/-- Reindexing central intervals gives the original ordinal-reindexed chain. -/
theorem centralIntervalFunctor_naturality {n m : SimplexCategory} (α : n ⟶ m) :
    centralIntervalFunctor n ⋙ nestedIntervalMap (Edgewise.ε.map α) =
      (SimplexCategory.toCat.map α).toFunctor ⋙ centralIntervalFunctor m := by
  apply CategoryTheory.Functor.ext (fun i ↦ centralInterval_naturality α i)

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : CategoryTheory.ExactCategory.ExactStructure C)

/-- The Q-valued interval functor of an exact row commutes strictly with reindexing. -/
theorem rowIntervalFunctor_reindex {n m : SimplexCategory} (α : n ⟶ m) (F : Row E m) :
    rowIntervalFunctor E ((rowReindex E α).obj F) =
      nestedIntervalMap α ⋙ rowIntervalFunctor E F := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- Changing an interval by equality conjugates its Q-isomorphism by the
corresponding object equalities, with no choice of representatives. -/
theorem qIso_app_congr {I : Type*} [Category I] {F G : I ⥤ C} (e : F ≅ G)
    (p q : I) (h : p = q) :
    (E.qIsoOfIso (e.app p)).hom =
      eqToHom (congrArg (fun i ↦ Q.of E.deflation E.inflation (F.obj i)) h) ≫
        (E.qIsoOfIso (e.app q)).hom ≫
          eqToHom (congrArg (fun i ↦ Q.of E.deflation E.inflation (G.obj i)) h.symm) := by
  subst q
  simp

/-- The row comparison is strictly simplicially natural, including its actual
natural-isomorphism morphisms. -/
theorem rowChainComparison_reindex {n m : SimplexCategory} (α : n ⟶ m) :
    rowReindex E (Edgewise.ε.map α) ⋙ rowChainComparison E n =
      rowChainComparison E m ⋙ chainCoreReindex (Q E.deflation E.inflation) α := by
  have hobj (F : Row E (Edgewise.ε.obj m)) :
      ((rowReindex E (Edgewise.ε.map α) ⋙ rowChainComparison E n).obj F) =
        ((rowChainComparison E m ⋙ chainCoreReindex (Q E.deflation E.inflation) α).obj F) := by
    change Core.mk _ = Core.mk _
    apply congrArg Core.mk
    change centralIntervalFunctor n ⋙ rowIntervalFunctor E ((rowReindex E (Edgewise.ε.map
      α)).obj F) =
      (SimplexCategory.toCat.map α).toFunctor ⋙ centralIntervalFunctor m ⋙ rowIntervalFunctor E F
    rw [rowIntervalFunctor_reindex, ← Functor.assoc, centralIntervalFunctor_naturality,
      Functor.assoc]
  refine CategoryTheory.Functor.ext hobj ?_
  intro F G e
  apply Core.hom_ext
  ext i
  change _ = (eqToHom (hobj F) : _ ⟶ _).iso.hom.app i ≫
    ((rowChainComparison E m ⋙ chainCoreReindex (Q E.deflation E.inflation) α).map
      e).iso.hom.app i ≫
      (eqToHom (hobj G).symm : _ ⟶ _).iso.hom.app i
  simp only [chainCore_eqToHom_app]
  exact qIso_app_congr E e _ _
    (congrArg nestedToInterval (centralInterval_naturality α i))

/-- The canonical map of bisimplicial sets from subdivided exact rows to
isomorphism groupoids of composable Q-arrows. -/
def rowChainNerveMap : Edgewise.ε.op ⋙ rowNerve E ⟶ chainCoreNerve (Q E.deflation E.inflation) where
  app n := MixedNerve.map.{u, v, max u v} (rowChainComparison E n.unop)
  naturality n m α := by
    ext k G
    change G ⋙ rowReindex E (Edgewise.ε.map α.unop) ⋙ rowChainComparison E m.unop =
      G ⋙ rowChainComparison E n.unop ⋙ chainCoreReindex (Q E.deflation E.inflation) α.unop
    rw [rowChainComparison_reindex]

end Quillen.Waldhausen.QuillenComparison
