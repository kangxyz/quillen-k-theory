/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Realization.Homotopy
public import Mathlib.Topology.Category.TopCat.ULift

/-!
# Geometric realization across universes

Compatible maps on the original topological simplices descend to geometric
realization with a target in any universe. The construction uses preservation
of colimits by `TopCat.uliftFunctor`. Consequently it retains every original
simplex and its barycentric coordinates.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite Convexity
open scoped Simplicial Topology
universe u v w

namespace Quillen

/-- Lift a compatible family into one common universe. -/
def topologicalColimitDescCocone {J : Type w} [Category J] {F : J ⥤ TopCat.{u}}
    {Z : Type v} [TopologicalSpace Z] (f : ∀ j, C(F.obj j, Z))
    (hf : ∀ {j k} (a : j ⟶ k) (x : F.obj j), f k (F.map a x) = f j x) :
    Cocone (F ⋙ TopCat.uliftFunctor.{v}) where
  pt := TopCat.of (ULift.{u} Z)
  ι := {
    app j := TopCat.ofHom ⟨fun x ↦ ULift.up (f j x.down), by fun_prop⟩
    naturality j k a := by
      ext x
      exact congrArg ULift.up (hf a x.down) }

/-- A colimit in topological spaces also descends to targets in other universes. -/
def topologicalColimitDesc {J : Type w} [Category J] {F : J ⥤ TopCat.{u}}
    (c : Cocone F) (hc : IsColimit c) {Z : Type v} [TopologicalSpace Z]
    (f : ∀ j, C(F.obj j, Z))
    (hf : ∀ {j k} (a : j ⟶ k) (x : F.obj j), f k (F.map a x) = f j x) :
    C(c.pt, Z) := by
  let g := (isColimitOfPreserves TopCat.uliftFunctor.{v} hc).desc
    (topologicalColimitDescCocone f hf)
  exact ⟨fun x ↦ (show ULift.{u} Z from g (ULift.up x)).down, by
    exact continuous_uliftDown.comp (g.hom.continuous.comp continuous_uliftUp)⟩

@[simp] theorem topologicalColimitDesc_ι
    {J : Type w} [Category J] {F : J ⥤ TopCat.{u}}
    (c : Cocone F) (hc : IsColimit c) {Z : Type v} [TopologicalSpace Z]
    (f : ∀ j, C(F.obj j, Z))
    (hf : ∀ {j k} (a : j ⟶ k) (x : F.obj j), f k (F.map a x) = f j x)
    (j : J) (x : F.obj j) :
    dsimp% topologicalColimitDesc c hc f hf (c.ι.app j x) = f j x := by
  exact congrArg (fun z : ULift.{u} Z ↦ z.down) (ConcreteCategory.congr_hom
    ((isColimitOfPreserves TopCat.uliftFunctor.{v} hc).fac
      (topologicalColimitDescCocone f hf) j) (ULift.up x))

/-- The original simplex cocone defining geometric realization. -/
def realizationSimplexCocone (X : SSet.{u}) :
    Cocone (CostructuredArrow.proj SSet.stdSimplex X ⋙ SimplexCategory.toTop) :=
  (Functor.LeftExtension.mk SSet.toTop SSet.toTopSimplex.inv).coconeAt X

/-- Geometric realization is the colimit of its original topological simplices. -/
def realizationSimplexCoconeIsColimit (X : SSet.{u}) :
    IsColimit (realizationSimplexCocone X) :=
  Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
    SSet.toTop SSet.toTopSimplex.inv X

/-- The characteristic map of an original simplex in ordinary barycentric coordinates. -/
def realizationSimplex {X : SSet.{u}} {n : SimplexCategory} (x : X.obj (op n)) :
    C(StdSimplex ℝ (Fin (n.len + 1)), |X|) :=
  (SSet.toTop.map (SSet.yonedaEquiv.symm x)).hom.comp
    ⟨(SimplexCategory.toTopHomeo n).symm, (SimplexCategory.toTopHomeo n).symm.continuous⟩

/-- Characteristic maps respect every simplicial operator. -/
theorem realizationSimplex_naturality {X : SSet.{u}} {n m : SimplexCategory}
    (a : n ⟶ m) (x : X.obj (op m)) (t : StdSimplex ℝ (Fin (n.len + 1))) :
    realizationSimplex x (StdSimplex.map a t) =
      realizationSimplex (X.map a.op x) t := by
  change SSet.toTop.map (SSet.yonedaEquiv.symm x)
    ((SimplexCategory.toTopHomeo m).symm (StdSimplex.map a t)) = _
  rw [SimplexCategory.toTopHomeo_symm_naturality_apply]
  change (SSet.toTop.map (SSet.stdSimplex.map a) ≫
    SSet.toTop.map (SSet.yonedaEquiv.symm x)) _ = _
  rw [← Functor.map_comp, SSet.yonedaEquiv_symm_naturality_left]
  rfl

theorem realizationSimplexCocone_ι_apply {X : SSet.{u}}
    (j : CostructuredArrow SSet.stdSimplex X)
    (t : StdSimplex ℝ (Fin (j.left.len + 1))) :
    (realizationSimplexCocone X).ι.app j (ULift.up t) =
      realizationSimplex (SSet.yonedaEquiv j.hom) t := by
  simp only [realizationSimplex, Equiv.symm_apply_apply]
  rfl

/-- Descend a compatible family on the original simplices to a target in any universe. -/
def realizationDesc {X : SSet.{u}} {Z : Type v} [TopologicalSpace Z]
    (f : ∀ (n : SimplexCategory), X.obj (op n) →
      C(StdSimplex ℝ (Fin (n.len + 1)), Z))
    (hf : ∀ {n m} (a : n ⟶ m) (x : X.obj (op m))
      (t : StdSimplex ℝ (Fin (n.len + 1))),
      f m x (StdSimplex.map a t) = f n (X.map a.op x) t) : C(|X|, Z) :=
  topologicalColimitDesc (realizationSimplexCocone X)
    (realizationSimplexCoconeIsColimit X)
    (fun j ↦ ⟨fun t ↦ f j.left (SSet.yonedaEquiv j.hom) t.down, by fun_prop⟩)
    (by
      intro j k a t
      change f k.left (SSet.yonedaEquiv k.hom) (StdSimplex.map a.left t.down) = _
      rw [hf]
      congr 2
      rw [SSet.yonedaEquiv_naturality, CostructuredArrow.w a])

@[simp] theorem realizationDesc_simplex {X : SSet.{u}} {Z : Type v} [TopologicalSpace Z]
    (f : ∀ (n : SimplexCategory), X.obj (op n) →
      C(StdSimplex ℝ (Fin (n.len + 1)), Z))
    (hf : ∀ {n m} (a : n ⟶ m) (x : X.obj (op m))
      (t : StdSimplex ℝ (Fin (n.len + 1))),
      f m x (StdSimplex.map a t) = f n (X.map a.op x) t)
    (n : SimplexCategory) (x : X.obj (op n)) (t : StdSimplex ℝ (Fin (n.len + 1))) :
    realizationDesc f hf (realizationSimplex x t) = f n x t := by
  have hx : realizationSimplex x t = (realizationSimplexCocone X).ι.app
      (CostructuredArrow.mk (SSet.yonedaEquiv.symm x)) (ULift.up t) := by
    rw [realizationSimplexCocone_ι_apply]
    simp
  unfold realizationDesc
  rw [hx]
  erw [topologicalColimitDesc_ι]
  · simp
  · intro j k a s
    change f k.left (SSet.yonedaEquiv k.hom) (StdSimplex.map a.left s.down) = _
    rw [hf]
    congr 2
    rw [SSet.yonedaEquiv_naturality, CostructuredArrow.w a]

/-- Functions out of realization are determined on its original simplices. -/
theorem realization_ext {X : SSet.{u}} {Z : Type v} (f g : |X| → Z)
    (h : ∀ (n : SimplexCategory) (x : X.obj (op n))
      (t : StdSimplex ℝ (Fin (n.len + 1))),
      f (realizationSimplex x t) = g (realizationSimplex x t)) : f = g := by
  funext z
  obtain ⟨j, t, rfl⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget TopCat) (realizationSimplexCoconeIsColimit X)) z
  change f ((realizationSimplexCocone X).ι.app j t) =
    g ((realizationSimplexCocone X).ι.app j t)
  change SimplexCategory.toTop.obj j.left at t
  obtain ⟨t⟩ := t
  rw [realizationSimplexCocone_ι_apply]
  exact h _ _ _

/-- A map of simplicial sets whose source and target may inhabit different universes. -/
structure SimplicialUniverseMap (X : SSet.{u}) (Y : SSet.{v}) where
  /-- The degreewise function on the original simplices. -/
  app (n : SimplexCategoryᵒᵖ) : X.obj n → Y.obj n
  naturality {n m : SimplexCategoryᵒᵖ} (a : n ⟶ m) (x : X.obj n) :
    app m (X.map a x) = Y.map a (app n x)

/-- Realize a simplicial map without imposing an equality of universes. -/
def realizationUniverseMap {X : SSet.{u}} {Y : SSet.{v}} (f : SimplicialUniverseMap X Y) :
    C(|X|, |Y|) :=
  realizationDesc (fun n x ↦ realizationSimplex (f.app (op n) x)) (by
    intro n m a x t
    rw [realizationSimplex_naturality, f.naturality])

@[simp] theorem realizationUniverseMap_simplex {X : SSet.{u}} {Y : SSet.{v}}
    (f : SimplicialUniverseMap X Y) (n : SimplexCategory) (x : X.obj (op n))
    (t : StdSimplex ℝ (Fin (n.len + 1))) :
    realizationUniverseMap f (realizationSimplex x t) =
      realizationSimplex (f.app (op n) x) t :=
  realizationDesc_simplex _ (by
    intro n m a x t
    rw [realizationSimplex_naturality, f.naturality]) _ _ _

@[simp] theorem realizationSimplex_zero {X : SSet.{u}} (x : X _⦋0⦌)
    (t : StdSimplex ℝ (Fin 1)) :
    realizationSimplex x t = realizationPoint x := by
  exact congrArg (SSet.toTop.map (SSet.yonedaEquiv.symm x))
    (Subsingleton.elim ((SimplexCategory.toTopHomeo ⦋0⦌).symm t) default)

@[simp] theorem realizationUniverseMap_point {X : SSet.{u}} {Y : SSet.{v}}
    (f : SimplicialUniverseMap X Y) (x : X _⦋0⦌) :
    realizationUniverseMap f (realizationPoint x) = realizationPoint (f.app _ x) := by
  rw [← realizationSimplex_zero x default, realizationUniverseMap_simplex,
    realizationSimplex_zero]

namespace SimplicialUniverseMap

/-- The identity simplicial map across the universe-independent interface. -/
def id (X : SSet.{u}) : SimplicialUniverseMap X X where
  app _ x := x
  naturality _ _ := rfl

/-- Composition retains the original degreewise functions. -/
def comp {X : SSet.{u}} {Y : SSet.{v}} {Z : SSet.{w}}
    (f : SimplicialUniverseMap X Y) (g : SimplicialUniverseMap Y Z) :
    SimplicialUniverseMap X Z where
  app n x := g.app n (f.app n x)
  naturality a x := by rw [f.naturality, g.naturality]

/-- An ordinary simplicial morphism gives a universe-independent simplicial map. -/
def ofHom {X Y : SSet.{u}} (f : X ⟶ Y) : SimplicialUniverseMap X Y where
  app n := f.app n
  naturality a x := ConcreteCategory.congr_hom (f.naturality a) x

end SimplicialUniverseMap

@[simp] theorem realizationUniverseMap_id (X : SSet.{u}) :
    realizationUniverseMap (SimplicialUniverseMap.id X) = ContinuousMap.id |X| := by
  apply DFunLike.coe_injective
  apply realization_ext
  intro n x t
  simp only [realizationUniverseMap_simplex, SimplicialUniverseMap.id, ContinuousMap.id_apply]

@[simp] theorem realizationUniverseMap_comp {X : SSet.{u}} {Y : SSet.{v}} {Z : SSet.{w}}
    (f : SimplicialUniverseMap X Y) (g : SimplicialUniverseMap Y Z) :
    realizationUniverseMap (f.comp g) =
      (realizationUniverseMap g).comp (realizationUniverseMap f) := by
  apply DFunLike.coe_injective
  apply realization_ext
  intro n x t
  simp only [realizationUniverseMap_simplex, SimplicialUniverseMap.comp,
    ContinuousMap.comp_apply]

@[simp] theorem realizationUniverseMap_ofHom {X Y : SSet.{u}} (f : X ⟶ Y) :
    realizationUniverseMap (SimplicialUniverseMap.ofHom f) = (SSet.toTop.map f).hom := by
  apply DFunLike.coe_injective
  apply realization_ext
  intro n x t
  rw [realizationUniverseMap_simplex]
  change SSet.toTop.map (SSet.yonedaEquiv.symm (f.app _ x))
    ((SimplexCategory.toTopHomeo n).symm t) =
      (SSet.toTop.map (SSet.yonedaEquiv.symm x) ≫ SSet.toTop.map f)
        ((SimplexCategory.toTopHomeo n).symm t)
  rw [← Functor.map_comp, SSet.yonedaEquiv_symm_comp]

end Quillen
