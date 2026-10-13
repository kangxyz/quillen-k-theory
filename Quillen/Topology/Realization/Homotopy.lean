/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.ClassifyingSpace.Basic

/-!
# Realizing vertices and edges as points and paths

These are low-dimensional, genuine topological realization constructions.
Every edge of a simplicial set supplies a path in its realization. In
particular, every categorical morphism supplies a path in the classifying
space, and a natural transformation supplies paths between the images of
all object vertices. No general realization-of-homotopy theorem is assumed.
-/
@[expose] public section

noncomputable section

open CategoryTheory Opposite Convexity
open scoped Simplicial Topology unitInterval

universe u v

namespace Quillen

/-- The point represented by a vertex in a simplicial set. -/
def realizationPoint {X : SSet.{u}} (x : X _⦋0⦌) : |X| :=
  SSet.toTop.map (SSet.yonedaEquiv.symm x) default

/-- A point of the realized interval with its ordinary unit-interval parameter. -/
def realizationInterval (t : unitInterval) : |(Δ[1] : SSet.{u})| :=
  SSet.stdSimplex.toTopObjIsoI.inv (ULift.up t)

@[fun_prop]
theorem continuous_realizationInterval : Continuous (realizationInterval.{u}) := by
  unfold realizationInterval
  fun_prop

@[simp]
theorem realizationInterval_zero :
    realizationInterval.{u} 0 = SSet.toTop.map (SSet.stdSimplex.δ 1) default := by
  apply (SimplexCategory.toTopHomeo ⦋1⦌).injective
  change SimplexCategory.toTopHomeo ⦋1⦌
    ((SimplexCategory.toTopHomeo ⦋1⦌).symm (StdSimplex.homeomorphI.symm 0)) = _
  rw [Homeomorph.apply_symm_apply]
  rw [StdSimplex.homeomorphI_symm_zero]
  change StdSimplex.single 0 = SimplexCategory.toTopHomeo ⦋1⦌
    (SSet.toTop.map (SSet.stdSimplex.map (SimplexCategory.δ 1)) default)
  rw [SimplexCategory.toTopHomeo_naturality_apply]
  rw [Subsingleton.elim (SimplexCategory.toTopHomeo ⦋0⦌ default) (StdSimplex.single 0),
    StdSimplex.map_single]
  rfl

@[simp]
theorem realizationInterval_one :
    realizationInterval.{u} 1 = SSet.toTop.map (SSet.stdSimplex.δ 0) default := by
  apply (SimplexCategory.toTopHomeo ⦋1⦌).injective
  change SimplexCategory.toTopHomeo ⦋1⦌
    ((SimplexCategory.toTopHomeo ⦋1⦌).symm (StdSimplex.homeomorphI.symm 1)) = _
  rw [Homeomorph.apply_symm_apply]
  rw [StdSimplex.homeomorphI_symm_one]
  change StdSimplex.single 1 = SimplexCategory.toTopHomeo ⦋1⦌
    (SSet.toTop.map (SSet.stdSimplex.map (SimplexCategory.δ 0)) default)
  rw [SimplexCategory.toTopHomeo_naturality_apply]
  rw [Subsingleton.elim (SimplexCategory.toTopHomeo ⦋0⦌ default) (StdSimplex.single 0),
    StdSimplex.map_single]
  rfl

/-- An edge realizes to a path with exactly its prescribed vertex endpoints. -/
def realizationEdgePath {X : SSet.{u}} {x y : X _⦋0⦌} (e : X.Edge x y) :
    Path (realizationPoint x) (realizationPoint y) where
  toFun t := SSet.toTop.map (SSet.yonedaEquiv.symm e.edge) (realizationInterval t)
  continuous_toFun := by fun_prop
  source' := by
    rw [realizationInterval_zero]
    change (SSet.toTop.map (SSet.stdSimplex.δ 1) ≫
      SSet.toTop.map (SSet.yonedaEquiv.symm e.edge)) default = _
    rw [← Functor.map_comp, e.δ_one_yonedaEquiv_symm]
    rfl
  target' := by
    rw [realizationInterval_one]
    change (SSet.toTop.map (SSet.stdSimplex.δ 0) ≫
      SSet.toTop.map (SSet.yonedaEquiv.symm e.edge)) default = _
    rw [← Functor.map_comp, e.δ_zero_yonedaEquiv_symm]
    rfl

@[simp]
theorem realizationEdgePath_apply {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : X.Edge x y) (t : unitInterval) :
    realizationEdgePath e t =
      SSet.toTop.map (SSet.yonedaEquiv.symm e.edge) (realizationInterval t) := rfl

@[simp]
theorem realizationPoint_naturality {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    SSet.toTop.map f (realizationPoint x) = realizationPoint (f.app _ x) := by
  change (SSet.toTop.map (SSet.yonedaEquiv.symm x) ≫ SSet.toTop.map f) default = _
  rw [← Functor.map_comp, SSet.yonedaEquiv_symm_comp]
  rfl

/-- The realized edge map is natural at every interval parameter. -/
@[simp] theorem realizationEdgePath_naturality_apply {X Y : SSet.{u}} (f : X ⟶ Y)
    {x y : X _⦋0⦌} (e : X.Edge x y) (t : unitInterval) :
    SSet.toTop.map f
      (SSet.toTop.map (SSet.yonedaEquiv.symm e.edge) (realizationInterval t)) =
        SSet.toTop.map (SSet.yonedaEquiv.symm (e.map f).edge) (realizationInterval t) := by
  change (SSet.toTop.map (SSet.yonedaEquiv.symm e.edge) ≫ SSet.toTop.map f)
    (realizationInterval t) = _
  rw [← Functor.map_comp, SSet.yonedaEquiv_symm_comp]
  rfl

@[simp]
theorem realizationEdgePath_id {X : SSet.{u}} (x : X _⦋0⦌) :
    realizationEdgePath (SSet.Edge.id x) = Path.refl (realizationPoint x) := by
  ext t
  change SSet.toTop.map (SSet.yonedaEquiv.symm (X.σ 0 x)) (realizationInterval t) = _
  rw [← SSet.stdSimplex.σ_comp_yonedaEquiv_symm, Functor.map_comp, TopCat.comp_app]
  rw [Subsingleton.elim (SSet.toTop.map (SSet.stdSimplex.σ 0) (realizationInterval t)) default]
  rfl

/-- The path in a classifying space represented by a morphism. -/
def classifyingSpacePath {C : Type u} [Category.{v} C] {c d : C} (f : c ⟶ d) :
    Path (classifyingSpacePoint c) (classifyingSpacePoint d) :=
  realizationEdgePath (CategoryTheory.nerve.edgeMk f)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem classifyingSpacePath_id {C : Type u} [Category.{v} C] (c : C) :
    classifyingSpacePath (𝟙 c) = Path.refl (classifyingSpacePoint c) := by
  unfold classifyingSpacePath
  erw [CategoryTheory.nerve.edgeMk_id, realizationEdgePath_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem classifyingSpacePath_naturality {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {c d : C} (f : c ⟶ d) (t : unitInterval) :
    classifyingSpaceMap F (classifyingSpacePath f t) =
      classifyingSpacePath (F.map f) t := by
  unfold classifyingSpaceMap classifyingSpacePath
  erw [realizationEdgePath_naturality_apply]
  simp only [SSet.Edge.map_edge,
    CategoryTheory.nerve.edgeMk_edge, CategoryTheory.nerveMap_app_mk₁]
  rfl

/-- A natural transformation provides paths between the images of each object. -/
def naturalTransformationPointPath {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (α : F ⟶ G) (c : C) :
    Path (classifyingSpacePoint (F.obj c)) (classifyingSpacePoint (G.obj c)) :=
  classifyingSpacePath (α.app c)

end Quillen
