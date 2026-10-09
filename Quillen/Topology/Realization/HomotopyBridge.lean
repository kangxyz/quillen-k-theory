import Quillen.Topology.Realization.CylinderIso
import Quillen.Topology.Realization.CylinderEndpoints
import Quillen.Topology.Realization.NerveHomotopy

/-!
# Simplicial homotopies realize to genuine topological homotopies

The cylinder isomorphism is proved from the finite-prism triangulation and
colimit preservation. Its endpoint and naturality identities give actual
continuous homotopies, including relative-to-vertex homotopies required for
based homotopy-group functoriality.
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open scoped Simplicial Topology unitInterval

universe u v

namespace Quillen

@[simp]
theorem realizationCylinderIso_inv_zero (X : SSet.{u}) :
    TopCat.ι₀ ≫ (realizationCylinderIso X).inv = SSet.toTop.map SSet.ι₀ := by
  rw [← realizationCylinderComparison_zero X]
  change ((SSet.toTop.map SSet.ι₀) ≫ (realizationCylinderIso X).hom) ≫
    (realizationCylinderIso X).inv = _
  simp

@[simp]
theorem realizationCylinderIso_inv_one (X : SSet.{u}) :
    TopCat.ι₁ ≫ (realizationCylinderIso X).inv = SSet.toTop.map SSet.ι₁ := by
  rw [← realizationCylinderComparison_one X]
  change ((SSet.toTop.map SSet.ι₁) ≫ (realizationCylinderIso X).hom) ≫
    (realizationCylinderIso X).inv = _
  simp

/-- A simplicial homotopy gives an actual continuous topological homotopy
between the geometric realizations of its endpoint maps. -/
def realizationSimplicialHomotopy {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) : (SSet.toTop.map f).hom.Homotopy (SSet.toTop.map g).hom where
  toFun z := SSet.toTop.map H.h ((realizationCylinderIso X).inv (z.2, ULift.up z.1))
  continuous_toFun :=
    (SSet.toTop.map H.h).hom.continuous.comp ((realizationCylinderIso X).inv.hom.continuous.comp
      (continuous_snd.prodMk (continuous_uliftUp.comp continuous_fst)))
  map_zero_left x := by
    change (TopCat.ι₀ ≫ (realizationCylinderIso X).inv ≫ SSet.toTop.map H.h) x = _
    rw [← Category.assoc, realizationCylinderIso_inv_zero, ← Functor.map_comp, H.h₀]
  map_one_left x := by
    change (TopCat.ι₁ ≫ (realizationCylinderIso X).inv ≫ SSet.toTop.map H.h) x = _
    rw [← Category.assoc, realizationCylinderIso_inv_one, ← Functor.map_comp, H.h₁]

/-- The inverse cylinder comparison is natural. -/
theorem realizationCylinderIso_inv_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    (realizationCylinderIso X).inv ≫ SSet.toTop.map (f ▷ Δ[1]) =
      (SSet.toTop.map f ▷ TopCat.I) ≫ (realizationCylinderIso Y).inv := by
  apply (cancel_mono (realizationCylinderIso Y).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (realizationCylinderIso X).inv ≫
    (SSet.toTop.map (f ▷ Δ[1]) ≫ realizationCylinderComparison Y) = _
  rw [realizationCylinderComparison_naturality, ← Category.assoc]
  change ((realizationCylinderIso X).inv ≫ (realizationCylinderIso X).hom) ≫ _ = _
  simp

/-- A simplicial homotopy that is constant on a vertex realizes to a
homotopy fixed at that actual point of the geometric realization. -/
theorem realizationSimplicialHomotopy_fixed_vertex {X Y : SSet.{u}}
    {f g : X ⟶ Y} (H : SSet.Homotopy f g) (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (h : SSet.yonedaEquiv.symm x ▷ Δ[1] ≫ H.h =
      fst Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm y) (t : unitInterval) :
    realizationSimplicialHomotopy H (t, realizationPoint x) = realizationPoint y := by
  let q := (realizationCylinderIso (Δ[0] : SSet.{u})).inv (default, ULift.up t)
  have hn := ConcreteCategory.congr_hom
    (realizationCylinderIso_inv_naturality (SSet.yonedaEquiv.symm x)) (default, ULift.up t)
  change SSet.toTop.map (SSet.yonedaEquiv.symm x ▷ Δ[1]) q =
    (realizationCylinderIso X).inv (realizationPoint x, ULift.up t) at hn
  change SSet.toTop.map H.h
    ((realizationCylinderIso X).inv (realizationPoint x, ULift.up t)) = _
  rw [← hn]
  change (SSet.toTop.map (SSet.yonedaEquiv.symm x ▷ Δ[1]) ≫ SSet.toTop.map H.h) q = _
  rw [← Functor.map_comp, h, Functor.map_comp, TopCat.comp_app]
  rw [Subsingleton.elim (SSet.toTop.map (fst Δ[0] Δ[1]) q) default]
  rfl

/-- A natural transformation of categories realizes to a genuine homotopy of classifying maps. -/
def classifyingSpaceNaturalTransformationHomotopy
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (α : F ⟶ G) :
    (classifyingSpaceMap F).hom.Homotopy (classifyingSpaceMap G).hom :=
  realizationSimplicialHomotopy (naturalTransformationNerveHomotopy α)

/-- Identity-at-the-basepoint natural transformations induce topological
homotopies relative to the actual basepoint of the classifying space. -/
def classifyingSpaceNaturalTransformationBasedHomotopy
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (α : F ⟶ G) (c : C)
    (h : F.obj c = G.obj c) (hα : α.app c = eqToHom h) :
    (classifyingSpaceMap F).hom.HomotopyRel (classifyingSpaceMap G).hom
      {classifyingSpacePoint c} where
  toHomotopy := classifyingSpaceNaturalTransformationHomotopy α
  prop' t x hx := by
    obtain rfl := Set.mem_singleton_iff.mp hx
    change realizationSimplicialHomotopy (naturalTransformationNerveHomotopy α)
      (t, classifyingSpacePoint c) = classifyingSpaceMap F (classifyingSpacePoint c)
    rw [classifyingSpaceMap_point]
    exact realizationSimplicialHomotopy_fixed_vertex
      (naturalTransformationNerveHomotopy α) (nerveVertex c) (nerveVertex (F.obj c))
      (naturalTransformationNerveCylinder_based α c h hα) t

end Quillen
