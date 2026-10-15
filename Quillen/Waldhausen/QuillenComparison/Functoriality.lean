/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.QuillenComparison.SimplicialMap
public import Quillen.Waldhausen.QuillenComparison.QuotientCalculus
public import Quillen.Waldhausen.Functor

/-!
# Exact-functor naturality of the canonical simplicial Q/S comparison

Postcomposition by a genuine exact functor preserves the quotient squares
of exact S-diagrams by their cokernel universal properties. The comparison
commutes with these actual postcomposition maps and the existing Q-functor.
This is an equality of simplicial maps before any basepoint normalization.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe v u

namespace Quillen.Waldhausen.QuillenComparison

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {EC : CategoryTheory.ExactCategory.ExactStructure C} {ED :
    CategoryTheory.ExactCategory.ExactStructure D}
  (F : CategoryTheory.ExactCategory.ExactFunctor EC ED)

/-- A genuine exact functor preserves exact S-diagrams. Cokernel squares
are derived from the actual mapped conflations, rather than hypothesized. -/
theorem exactPostcompSimplex {n : SimplexCategory} {A : Grid n ⥤ C}
    (hA : IsSimplex EC.inflation (MorphismProperty.isomorphisms C) A) :
    IsSimplex ED.inflation (MorphismProperty.isomorphisms D) (A ⋙ F.toFunctor) where
  zero t i := F.toFunctor.map_isZero (hA.zero t i)
  cofibration t i j k hij hjk := F.map_inflation _ (hA.cofibration t i j k hij hjk)
  quotient t i j k hij hjk := by
    let S := ShortComplex.mk _ _ (rowMap_zero EC hA t i j k hij hjk)
    have hS := F.map_conflation S (row_conflation EC hA t i j k hij hjk)
    exact isPushoutOfZeroCokernel (S.map F.toFunctor).zero (ED.cokernel _ hS)
      (F.toFunctor.map_isZero (hA.zero t j)) _ _
  weak s t i j hst hij := by
    let : IsIso (A.map (homOfLE
      (show grid s i j hij ≤ grid t i j hij from ⟨hst, le_rfl, le_rfl⟩))) :=
      hA.weak s t i j hst hij
    exact F.toFunctor.map_isIso _

/-- The canonical exact-category S-map, with precisely postcomposition on grids. -/
def exactSSetMap : sSet EC.inflation (MorphismProperty.isomorphisms C) ⟶
    sSet ED.inflation (MorphismProperty.isomorphisms D) where
  app _ := ↾fun A ↦ ⟨A.1 ⋙ F.toFunctor, exactPostcompSimplex F A.2⟩
  naturality _ _ _ := by ext A; rfl

/-- Postcomposition by the identity exact functor is the identity simplicial map. -/
@[simp] theorem exactSSetMap_id (E : CategoryTheory.ExactCategory.ExactStructure C) :
    exactSSetMap (CategoryTheory.ExactCategory.ExactFunctor.id E) = 𝟙 _ := by
  ext n A
  apply Subtype.ext
  exact CategoryTheory.Functor.comp_id A.1

/-- Exact-functor composition acts by the actual composite simplicial map. -/
@[simp] theorem exactSSetMap_comp {T : Type u} [Category.{v} T]
    [Preadditive T] [HasFiniteBiproducts T] {ET : CategoryTheory.ExactCategory.ExactStructure T}
    (G : CategoryTheory.ExactCategory.ExactFunctor ED ET) :
    exactSSetMap (F.comp G) = exactSSetMap F ≫ exactSSetMap G := rfl

/-- When expressed through the general Waldhausen adapter, this is the same
actual S-map; the choice of exactness proof carries no extra information. -/
theorem exactSSetMap_eq_sSetMap
    (hF : IsExact EC.inflation (MorphismProperty.isomorphisms C)
      ED.inflation (MorphismProperty.isomorphisms D) F.toFunctor) :
    exactSSetMap F = sSetMap hF := rfl

/-- Exact functors take the actual vertical isomorphism to the actual image isomorphism. -/
theorem verticalIso_postcomp {n : SimplexCategory} {A : Grid n ⥤ C}
    (hA : IsSimplex EC.inflation (MorphismProperty.isomorphisms C) A)
    (s t : Fin (n.len + 1)) (hst : s ≤ t) {i j : Fin (n.len + 1)} (hij : i ≤ j) :
    verticalIso ED (exactPostcompSimplex F hA) s t hst hij =
      F.toFunctor.mapIso (verticalIso EC hA s t hst hij) := by
  apply Iso.ext
  rfl

/-- The canonical interval span is mapped termwise by the genuine exact functor. -/
theorem intervalSpan_postcomp {n : SimplexCategory} {A : Grid n ⥤ C}
    (hA : IsSimplex EC.inflation (MorphismProperty.isomorphisms C) A)
    (t : Fin (n.len + 1)) {p q : NestedInterval n} (h : p ≤ q) :
    intervalSpan ED (exactPostcompSimplex F hA) t h =
      F.toQCompatibleFunctor.mapSpan (intervalSpan EC hA t h) := rfl

/-- The entire Q-valued grid, including its nerve direction, is exactly natural. -/
theorem gridQFunctor_postcomp {n : SimplexCategory} {A : Grid n ⥤ C}
    (hA : IsSimplex EC.inflation (MorphismProperty.isomorphisms C) A) :
    gridQFunctor ED (exactPostcompSimplex F hA) = gridQFunctor EC hA ⋙ F.mapQ := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro p q f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (ED.qIsoOfIso (verticalIso ED (exactPostcompSimplex F hA) _ _ _ _)).hom ≫
      Q.mkHom _ _ (intervalSpan ED (exactPostcompSimplex F hA) _ _) =
    F.mapQ.map ((EC.qIsoOfIso (verticalIso EC hA _ _ _ _)).hom ≫
      Q.mkHom _ _ (intervalSpan EC hA _ _))
  rw [Functor.map_comp, verticalIso_postcomp F hA, intervalSpan_postcomp F hA]
  congr 1
  exact congrArg Iso.hom (F.mapQ_qIsoOfIso _).symm

/-- The canonical Q/S map commutes strictly with genuine exact functors. -/
theorem comparisonMap_naturality :
    Edgewise.subdivisionFunctor.map (exactSSetMap F) ≫ comparisonMap ED =
      comparisonMap EC ≫ CategoryTheory.nerveMap F.mapQ := by
  ext n A
  change comparisonIndices n.unop ⋙ gridQFunctor ED (exactPostcompSimplex F A.2) =
    (comparisonIndices n.unop ⋙ gridQFunctor EC A.2) ⋙ F.mapQ
  rw [gridQFunctor_postcomp, Functor.assoc]

end Quillen.Waldhausen.QuillenComparison
