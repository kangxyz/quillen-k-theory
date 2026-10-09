import Quillen.Topology.Realization.Prism

/-! # Endpoints of the geometric realization cylinder comparison -/

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open scoped Simplicial Topology unitInterval

universe u

namespace Quillen

/-- A constant simplicial map realizes to the corresponding constant continuous map. -/
theorem realization_const_apply {X Y : SSet.{u}} (y : Y _⦋0⦌) (x : |X|) :
    SSet.toTop.map (SSet.const y) x = realizationPoint y := by
  let p : X ⟶ Δ[0] := SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0)
  have h : (SSet.const y : X ⟶ Y) = p ≫ SSet.yonedaEquiv.symm y := by
    simp [SSet.yonedaEquiv_symm_zero]
  rw [h, Functor.map_comp, TopCat.comp_app]
  change SSet.toTop.map (SSet.yonedaEquiv.symm y) _ =
    SSet.toTop.map (SSet.yonedaEquiv.symm y) default
  congr 1
  exact Subsingleton.elim _ _

@[simp]
theorem realizationIntervalIso_zero :
    SSet.stdSimplex.toTopObjIsoI.hom (realizationPoint
      (SSet.stdSimplex.obj₀Equiv.{u}.symm 0)) = (0 : TopCat.I) := by
  change SSet.stdSimplex.toTopObjIsoI.hom (SSet.toTop.map (SSet.yonedaEquiv.symm _) default) = _
  rw [SSet.yonedaEquiv_symm_zero, ← SSet.stdSimplex.δ_one_eq_const, ← realizationInterval_zero]
  exact ConcreteCategory.congr_hom SSet.stdSimplex.toTopObjIsoI.inv_hom_id _

@[simp]
theorem realizationIntervalIso_one :
    SSet.stdSimplex.toTopObjIsoI.hom (realizationPoint
      (SSet.stdSimplex.obj₀Equiv.{u}.symm 1)) = (1 : TopCat.I) := by
  change SSet.stdSimplex.toTopObjIsoI.hom (SSet.toTop.map (SSet.yonedaEquiv.symm _) default) = _
  rw [SSet.yonedaEquiv_symm_zero, ← SSet.stdSimplex.δ_zero_eq_const, ← realizationInterval_one]
  exact ConcreteCategory.congr_hom SSet.stdSimplex.toTopObjIsoI.inv_hom_id _

/-- The zero endpoint of the simplicial cylinder is the zero endpoint of the topological cylinder. -/
@[simp]
theorem realizationCylinderComparison_zero (X : SSet.{u}) :
    SSet.toTop.map (SSet.ι₀ (X := X)) ≫ realizationCylinderComparison X = TopCat.ι₀ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, realizationCylinderComparison_fst, ← Functor.map_comp]
    simp
  · rw [Category.assoc, realizationCylinderComparison_snd, ← Category.assoc,
      ← Functor.map_comp, SSet.ι₀_snd]
    ext x : 1
    change SSet.stdSimplex.toTopObjIsoI.hom
      (SSet.toTop.map (SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0)) x) = 0
    rw [realization_const_apply, realizationIntervalIso_zero]

/-- The one endpoint of the simplicial cylinder is the one endpoint of the topological cylinder. -/
@[simp]
theorem realizationCylinderComparison_one (X : SSet.{u}) :
    SSet.toTop.map (SSet.ι₁ (X := X)) ≫ realizationCylinderComparison X = TopCat.ι₁ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, realizationCylinderComparison_fst, ← Functor.map_comp]
    simp
  · rw [Category.assoc, realizationCylinderComparison_snd, ← Category.assoc,
      ← Functor.map_comp, SSet.ι₁_snd]
    ext x : 1
    change SSet.stdSimplex.toTopObjIsoI.hom
      (SSet.toTop.map (SSet.const (SSet.stdSimplex.obj₀Equiv.symm 1)) x) = 1
    rw [realization_const_apply, realizationIntervalIso_one]

end Quillen
