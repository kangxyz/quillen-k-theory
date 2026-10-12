/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Realization.HomotopyBridge
public import Quillen.Topology.HomotopyGroups.MovingBasepoint

/-!
# Exact vertex tracks of realized natural transformations

The track of an object vertex is the actual edge path of the corresponding
component arrow. This retains the path required for moving-basepoint transport.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval

namespace Quillen

lemma realizationCylinderIso_inv_snd (X : SSet.{u}) (x : |X|) (t : unitInterval) :
    SSet.toTop.map (snd X Δ[1]) ((realizationCylinderIso X).inv (x, ULift.up t)) =
      realizationInterval t := by
  have h : (realizationCylinderIso X).inv ≫ SSet.toTop.map (snd X Δ[1]) ≫
      SSet.stdSimplex.toTopObjIsoI.hom = snd |X| TopCat.I := by
    rw [← realizationCylinderComparison_snd]
    change (realizationCylinderIso X).inv ≫ (realizationCylinderIso X).hom ≫ _ = _
    simp
  apply (TopCat.homeoOfIso SSet.stdSimplex.toTopObjIsoI).injective
  change SSet.stdSimplex.toTopObjIsoI.hom _ =
    SSet.stdSimplex.toTopObjIsoI.hom (SSet.stdSimplex.toTopObjIsoI.inv (ULift.up t))
  have ht := ConcreteCategory.congr_hom SSet.stdSimplex.toTopObjIsoI.inv_hom_id (ULift.up t)
  change SSet.stdSimplex.toTopObjIsoI.hom (SSet.stdSimplex.toTopObjIsoI.inv (ULift.up t)) =
    ULift.up t at ht
  rw [ht]
  exact ConcreteCategory.congr_hom h (x, ULift.up t)

/-- The whole vertex track is the realized component arrow, including its parametrization. -/
theorem classifyingSpaceNaturalTransformationHomotopy_vertex_track
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (α : F ⟶ G) (c : C) (t : unitInterval) :
    classifyingSpaceNaturalTransformationHomotopy α (t, classifyingSpacePoint c) =
      classifyingSpacePath (α.app c) t := by
  let q := (realizationCylinderIso (Δ[0] : SSet.{max u v})).inv (default, ULift.up t)
  have hn := ConcreteCategory.congr_hom
    (realizationCylinderIso_inv_naturality (nerveVertexMap c)) (default, ULift.up t)
  change SSet.toTop.map (nerveVertexMap c ▷ Δ[1]) q =
    (realizationCylinderIso (nerve C)).inv (classifyingSpacePoint c, ULift.up t) at hn
  change SSet.toTop.map (naturalTransformationNerveCylinder α)
    ((realizationCylinderIso (nerve C)).inv (classifyingSpacePoint c, ULift.up t)) = _
  rw [← hn]
  change (SSet.toTop.map (nerveVertexMap c ▷ Δ[1]) ≫
    SSet.toTop.map (naturalTransformationNerveCylinder α)) q = _
  rw [← Functor.map_comp, naturalTransformationNerveCylinder_vertex, Functor.map_comp,
    TopCat.comp_app]
  rw [realizationCylinderIso_inv_snd]
  rfl

/-- The vertex track after recording the actual functorial endpoint identifications. -/
def classifyingSpaceNaturalTransformationTrack
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (α : F ⟶ G) (c : C) :
    Path (classifyingSpacePoint (F.obj c)) (classifyingSpacePoint (G.obj c)) :=
  ((classifyingSpaceNaturalTransformationHomotopy α).evalAt (classifyingSpacePoint c)).cast
    (classifyingSpaceMap_point F c).symm (classifyingSpaceMap_point G c).symm

@[simp]
lemma classifyingSpaceNaturalTransformationTrack_eq
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (α : F ⟶ G) (c : C) :
    classifyingSpaceNaturalTransformationTrack α c = classifyingSpacePath (α.app c) := by
  ext t
  exact classifyingSpaceNaturalTransformationHomotopy_vertex_track α c t

/-- An unbased homotopy with identified endpoints still requires its whole track. -/
theorem pathTransport_homotopyGroupMap_homotopy_cast
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : f.Homotopy g) (x : X) {y₀ y₁ : Y}
    (hf : f x = y₀) (hg : g x = y₁) (n : ℕ) (a : HomotopyGroup.Pi n X x) :
    pathTransport ((H.evalAt x).cast hf.symm hg.symm) n (homotopyGroupMap f hf a) =
      homotopyGroupMap g hg a := by
  subst y₀ y₁
  exact pathTransport_homotopyGroupMap_homotopy H x n a

/-- The change of basepoint for a natural transformation is its original component edge. -/
theorem pathTransport_classifyingSpaceMap_naturalTransformation
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (α : F ⟶ G) (c : C) (n : ℕ)
    (a : HomotopyGroup.Pi n (ClassifyingSpace C) (classifyingSpacePoint c)) :
    pathTransport (classifyingSpacePath (α.app c)) n
      (homotopyGroupMap (classifyingSpaceMap F).hom (classifyingSpaceMap_point F c) a) =
        homotopyGroupMap (classifyingSpaceMap G).hom (classifyingSpaceMap_point G c) a := by
  rw [← classifyingSpaceNaturalTransformationTrack_eq α c]
  exact pathTransport_homotopyGroupMap_homotopy_cast
    (classifyingSpaceNaturalTransformationHomotopy α) (classifyingSpacePoint c)
    (classifyingSpaceMap_point F c) (classifyingSpaceMap_point G c) n a

end Quillen
