/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.Functoriality
public import Quillen.Waldhausen.SmallModel.Basic

/-!
# The exact category of models for iterated S-constructions

The objects are actual small Waldhausen categories. Morphisms are exact functors together
with equality of the chosen zero objects. Actual quotient rows, ordinal reindexing, and the
original diagonal S-construction produce all finite stages by recursive prolongation.
The genuine small-model construction handles independent original object and morphism universes.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite MonoidalCategory
open scoped Simplicial
universe u
namespace Quillen.Waldhausen.IteratedS

/-- A genuine small category with its actual Waldhausen structure. -/
structure Model where
  category : Cat.{u,u}
  waldhausen : Structure category

instance : CoeSort Model (Type u) := ⟨fun W ↦ W.category⟩
instance (W : Model.{u}) : SmallCategory W := inferInstanceAs (SmallCategory W.category)

/-- Actual exact functors preserving the displayed zero object. -/
@[ext] structure Model.Hom (V W : Model.{u}) where
  functor : V ⥤ W
  exact : IsExact V.waldhausen.cof V.waldhausen.weq W.waldhausen.cof W.waldhausen.weq functor
  zero : functor.obj V.waldhausen.zero = W.waldhausen.zero

instance : Category Model.{u} where
  Hom := Model.Hom
  id W := ⟨𝟭 W, IsExact.id _ _, rfl⟩
  comp F G := ⟨F.functor ⋙ G.functor, F.exact.comp G.exact, by
    change G.functor.obj (F.functor.obj _) = _
    rw [F.zero, G.zero]⟩
  id_comp F := by apply Model.Hom.ext; rfl
  comp_id F := by apply Model.Hom.ext; rfl
  assoc F G H := by apply Model.Hom.ext; rfl

/-- Actual quotient rows are functorial on the genuine zero-preserving exact category. -/
def rows (n : SimplexCategory) : Model.{u} ⥤ Model.{u} where
  obj W := ⟨Cat.of (QuotientRows.Obj W.waldhausen n), QuotientRows.waldhausenStructure
    W.waldhausen n⟩
  map F := ⟨QuotientRows.postcompose _ _ F.exact n,
    QuotientRows.postcompose_exact _ _ F.exact n,
    postcompose_zero _ _ F.exact F.zero n⟩
  map_id W := by apply Model.Hom.ext; exact QuotientRows.postcompose_id _ n
  map_comp F G := by
    apply Model.Hom.ext;
    exact (QuotientRows.postcompose_comp_postcompose _ _ F.exact _ G.exact n).symm

/-- The original ordinal restrictions, with their proved exactness and original zero equality. -/
def rowsReindex {m n : SimplexCategory} (α : m ⟶ n) : rows n ⟶ rows m where
  app W := ⟨QuotientRows.reindex W.waldhausen α, QuotientRows.reindex_exact W.waldhausen α,
    QuotientRows.reindex_zero W.waldhausen α⟩
  naturality V W F := by
    apply Model.Hom.ext
    exact QuotientRows.postcompose_reindex V.waldhausen W.waldhausen F.exact α

/-- All actual row categories and exact ordinal maps form one simplicial diagram. -/
def rowDiagram (W : Model.{u}) : SimplexCategoryᵒᵖ ⥤ Model.{u} where
  obj n := (rows n.unop).obj W
  map α := (rowsReindex α.unop).app W
  map_id n := by apply Model.Hom.ext; exact QuotientRows.reindex_id _ _
  map_comp α β := by apply Model.Hom.ext; exact QuotientRows.reindex_comp _ _ _

/-- Exact zero-preserving functors act on every original row simultaneously. -/
def rowDiagramFunctor : Model.{u} ⥤ (SimplexCategoryᵒᵖ ⥤ Model.{u}) where
  obj := rowDiagram
  map F := {
    app n := (rows n.unop).map F
    naturality n m α := ((rowsReindex α.unop).naturality F).symm }
  map_id W := by ext n : 1; exact (rows n.unop).map_id W
  map_comp F G := by ext n : 1; exact (rows n.unop).map_comp F G

/-- The original diagonal S-construction, retaining its exact original maps. -/
def initialS : Model.{u} ⥤ SSet.{u} where
  obj W := sSet W.waldhausen.cof W.waldhausen.weq
  map F := sSetMap F.exact
  map_id W := by ext n A; rfl
  map_comp F G := by ext n A; rfl

/-- Iterate a genuine simplicial invariant by the actual quotient-row construction. -/
def prolong (H : Model.{u} ⥤ SSet.{u}) : Model.{u} ⥤ SSet.{u} :=
  rowDiagramFunctor ⋙ (whiskeringRight _ _ _).obj H ⋙ TheoremA.diagonalFunctor

/-- Every finite iterated S-stage is constructed by actual rows, nerves and diagonals. -/
def stages (r : ℕ) : Model.{u} ⥤ SSet.{u} :=
  Nat.rec initialS (fun _ H ↦ prolong H) r

/-- The original one-row insertion, as an actual natural transformation. -/
def insertion {n : SimplexCategory} (τ : n ⟶ ⦋1⦌) : 𝟭 Model.{u} ⟶ rows n where
  app W := ⟨suspensionRow W.waldhausen τ, suspensionRow_exact W.waldhausen τ,
    suspensionRow_zero_obj W.waldhausen τ⟩
  naturality V W F := by
    apply Model.Hom.ext
    exact (suspensionRow_postcompose V.waldhausen W.waldhausen F.exact F.zero τ).symm

lemma insertion_reindex {m n : SimplexCategory} (α : m ⟶ n) (τ : n ⟶ ⦋1⦌)
    (W : Model.{u}) :
    (insertion (α ≫ τ)).app W = (insertion τ).app W ≫ (rowsReindex α).app W := by
  apply Model.Hom.ext
  exact suspensionRow_reindex W.waldhausen α τ

/-- This bundle retains the actual accepted small-model equivalence for arbitrary original
universes. -/
def modelOf {C : Type*} [Category C] (W : Structure C) : Model :=
  ⟨Cat.of (SmallModel C), W.smallModel⟩

end Quillen.Waldhausen.IteratedS
