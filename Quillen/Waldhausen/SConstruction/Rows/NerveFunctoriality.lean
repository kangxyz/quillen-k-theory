import Quillen.Waldhausen.SConstruction.Rows.NervePresentation
import Quillen.Waldhausen.SConstruction.Rows.Functoriality

/-! # The original-grid nerve presentation preserves exact functors

The forward presentation is strictly natural for actual exact functors and
original ordinal restrictions. Consequently the diagonal identification
intertwines the existing S-map with the actual weak-row nerve map.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u v u' v'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.QuotientRows
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (V : Structure C) (W : Structure D) {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)

/-- The original postcomposition restricted to actual pointwise weak arrows. -/
def weakRowsPostcompose (n : SimplexCategory) : WeakRows V n ⥤ WeakRows W n where
  obj X := ⟨(postcompose V W hF n).obj X.obj⟩
  map f := ⟨(postcompose V W hF n).map f.hom, (postcompose_exact V W hF n).weak f.hom f.property⟩
  map_id X := WideSubcategory.hom_ext _ ((postcompose V W hF n).map_id X.obj)
  map_comp f g := WideSubcategory.hom_ext _ ((postcompose V W hF n).map_comp f.hom g.hom)

/-- Weak-row postcomposition strictly commutes with every original ordinal restriction. -/
theorem weakRowsPostcompose_reindex {n m : SimplexCategory} (α : m ⟶ n) :
    weakRowsPostcompose V W hF n ⋙ weakRowsReindex W α =
      weakRowsReindex V α ⋙ weakRowsPostcompose V W hF m := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The grid-to-chain map retains the original exact functor at every component. -/
theorem gridToWeakChain_postcompose {n k : SimplexCategory} (G : Grid₂ n k ⥤ C)
    (hG : IsSimplex₂ V.cof V.weq G) :
    gridToWeakChain W (G ⋙ F) (hG.postcomp V.cof V.weq hF) =
      gridToWeakChain V G hG ⋙ weakRowsPostcompose V W hF n := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

end Quillen.Waldhausen.QuotientRows
namespace Quillen.Waldhausen.QuotientRows
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)

/-- The original exact functor acts on the actual weak-row nerves. -/
def weakRowNerveMap : weakRowNerve V ⟶ weakRowNerve W where
  app n := nerveMap (weakRowsPostcompose V W hF n.unop)
  naturality n m α := by
    ext k G : 4
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The genuine bisimplicial presentation strictly retains the original exact map. -/
theorem gridNerveIso_naturality :
    bisimplicialSSetMap V.cof V.weq hF ≫ (gridNerveIso W).hom =
      (gridNerveIso V).hom ≫ weakRowNerveMap V W hF := by
  ext n k G : 5
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The canonical diagonal presentation intertwines the unchanged original S-map. -/
theorem sSetWeakRowDiagonalIso_naturality :
    sSetMap hF ≫ (sSetWeakRowDiagonalIso W).hom =
      (sSetWeakRowDiagonalIso V).hom ≫ TheoremA.diagonalMap (weakRowNerveMap V W hF) := by
  ext n G : 4
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The diagonal nerve map is literal original postcomposition at every component. -/
@[simp] theorem weakRowNerveMap_component (n k : SimplexCategory)
    (G : ComposableArrows (WeakRows V n) k.len) (t : Fin (k.len+1)) (p : Interval n) :
    (((((weakRowNerveMap V W hF).app (op n)).app (op k) G).obj t).obj.obj.obj p) =
      F.obj ((G.obj t).obj.obj.obj p) := rfl

end Quillen.Waldhausen.QuotientRows
