import Quillen.Waldhausen.QuillenComparison.RowSimplicial
import Quillen.Topology.Realization.Classification

/-! # The simplicial groupoid of Q-chains

This is the categorical row model of the classification diagram. It will be
compared with the actual rectangular-grid model, with diagonal evaluation
retaining the canonical comparison map.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open scoped Simplicial
universe v u

namespace Quillen.Waldhausen.QuillenComparison

variable (D : Type u) [Category.{v} D]

/-- Reindex a composable chain and all its invertible natural transformations. -/
def chainCoreReindex {m n : SimplexCategory} (α : m ⟶ n) :
    Core (ComposableArrows D n.len) ⥤ Core (ComposableArrows D m.len) where
  obj F := ⟨(SimplexCategory.toCat.map α).toFunctor ⋙ F.of⟩
  map e := ⟨Functor.isoWhiskerLeft (SimplexCategory.toCat.map α).toFunctor e.iso⟩
  map_id _ := by apply Core.hom_ext; rfl
  map_comp _ _ := by apply Core.hom_ext; rfl

/-- The isomorphism groupoids of composable chains form a simplicial category. -/
def chainCoreSimplicial : SimplexCategoryᵒᵖ ⥤ Cat.{v, max u v} where
  obj n := Cat.of (Core (ComposableArrows D n.unop.len))
  map α := Cat.Hom.ofFunctor (chainCoreReindex D α.unop)
  map_id _ := by
    apply Cat.Hom.ext
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
  map_comp _ _ := by
    apply Cat.Hom.ext
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The genuine bisimplicial classification nerve. -/
def chainCoreNerve : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} :=
  chainCoreSimplicial D ⋙ nerveFunctor

variable {D} {n : SimplexCategory}

/-- One horizontal row in a classification grid. -/
def classificationRestriction (t : Fin (n.len + 1)) :
    Fin (n.len + 1) ⥤ Classification.Grid n :=
  (show Monotone (fun i : Fin (n.len + 1) ↦ ((t, i) : Classification.Grid n)) from
    fun _ _ h ↦ ⟨le_rfl, h⟩).functor

/-- An actual classification grid reorganizes as a chain of chains. -/
def classificationRows (F : Classification.Grid n ⥤ D) (hF : Classification.IsVerticalIso F) :
    ComposableArrows (Core (ComposableArrows D n.len)) n.len where
  obj t := ⟨classificationRestriction t ⋙ F⟩
  map {s t} f := ⟨NatIso.ofComponents (fun i ↦ by
    letI : IsIso (Classification.verticalMap F s t i (leOfHom f)) := hF s t i (leOfHom f)
    exact asIso (Classification.verticalMap F s t i (leOfHom f))) (by
      intro i j g
      change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
      simp only [← F.map_comp]
      congr 1)⟩
  map_id t := by
    apply Core.hom_ext
    ext i
    exact F.map_id _
  map_comp f g := by
    apply Core.hom_ext
    ext i
    exact F.map_comp _ _

/-- Reassemble a chain of natural isomorphisms of chains into a grid. -/
def classificationGrid (G : ComposableArrows (Core (ComposableArrows D n.len)) n.len) :
    Classification.Grid n ⥤ D where
  obj p := (G.obj p.1).of.obj p.2
  map {p q} f := (G.map (homOfLE (leOfHom f).1)).iso.hom.app p.2 ≫
    (G.obj q.1).of.map (homOfLE (leOfHom f).2)
  map_id p := by
    rcases p with ⟨t, p⟩
    change (G.map (𝟙 t)).iso.hom.app p ≫ (G.obj t).of.map (𝟙 p) = _
    rw [G.map_id, (G.obj t).of.map_id]
    exact Category.id_comp _
  map_comp {p q r} f g := by
    rcases p with ⟨s, p⟩
    rcases q with ⟨t, q⟩
    rcases r with ⟨u, r⟩
    change (G.map ((homOfLE (leOfHom f).1) ≫ (homOfLE (leOfHom g).1))).iso.hom.app p ≫
      (G.obj u).of.map ((homOfLE (leOfHom f).2) ≫ (homOfLE (leOfHom g).2)) = _
    rw [G.map_comp, (G.obj u).of.map_comp]
    change (_ ≫ _) ≫ (_ ≫ _) = (_ ≫ _) ≫ (_ ≫ _)
    simp only [Category.assoc]
    congr 1
    rw [← (G.map (homOfLE (leOfHom g).1)).iso.hom.naturality_assoc]

/-- Every vertical arrow in the reassembled grid is the original component isomorphism. -/
theorem classificationGrid_isVerticalIso
    (G : ComposableArrows (Core (ComposableArrows D n.len)) n.len) :
    Classification.IsVerticalIso (classificationGrid G) := by
  intro s t i hst
  change IsIso ((G.map (homOfLE hst)).iso.hom.app i ≫ (G.obj t).of.map (𝟙 i))
  rw [(G.obj t).of.map_id, Category.comp_id]
  infer_instance

@[simp]
theorem classificationGrid_rows (F : Classification.Grid n ⥤ D)
    (hF : Classification.IsVerticalIso F) : classificationGrid (classificationRows F hF) = F := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro p q f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact (F.map_comp _ _).symm

@[simp]
theorem chainCore_eqToHom_app {F G : Core (ComposableArrows D n.len)} (h : F = G)
    (i : Fin (n.len + 1)) :
    (eqToHom h : F ⟶ G).iso.hom.app i = eqToHom (congrArg (fun F ↦ F.of.obj i) h) := by
  cases h
  rfl

@[simp]
theorem classificationRows_grid
    (G : ComposableArrows (Core (ComposableArrows D n.len)) n.len) :
    classificationRows (classificationGrid G) (classificationGrid_isVerticalIso G) = G := by
  have hobj (t : Fin (n.len + 1)) :
      (classificationRows (classificationGrid G) (classificationGrid_isVerticalIso G)).obj t = G.obj t := by
    change Core.mk _ = Core.mk (G.obj t).of
    apply congrArg Core.mk
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro i j f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change (G.map (𝟙 t)).iso.hom.app i ≫ (G.obj t).of.map f = _
    rw [G.map_id]
    exact Category.id_comp _
  refine CategoryTheory.Functor.ext hobj ?_
  intro s t f
  apply Core.hom_ext
  ext i
  change _ = (eqToHom (hobj s) : _ ⟶ _).iso.hom.app i ≫ (G.map f).iso.hom.app i ≫
    (eqToHom (hobj t).symm : _ ⟶ _).iso.hom.app i
  simp only [chainCore_eqToHom_app, eqToHom_refl, Category.id_comp, Category.comp_id]
  change (G.map f).iso.hom.app i ≫ (G.obj t).of.map (𝟙 i) = _
  rw [(G.obj t).of.map_id, Category.comp_id]

variable (D)

/-- The rectangular and categorical classification diagonals agree as actual simplicial sets. -/
def chainCoreDiagonalIso : Classification.sSet D ≅ TheoremA.diagonalSSet (chainCoreNerve D) where
  hom := {
    app _ := ↾fun F ↦ classificationRows F.1 F.2
    naturality n m α := by
      ext F
      apply CategoryTheory.Functor.ext (fun _ ↦ rfl) }
  inv := {
    app _ := ↾fun G ↦ ⟨classificationGrid G, classificationGrid_isVerticalIso G⟩
    naturality n m α := by ext G; rfl }
  hom_inv_id := by
    ext n F
    apply Subtype.ext
    exact classificationGrid_rows F.1 F.2
  inv_hom_id := by
    ext n G
    exact classificationRows_grid G

end Quillen.Waldhausen.QuillenComparison
