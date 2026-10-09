import Quillen.Topology.Realization.Homotopy

/-! # Constant maps and geometric realization -/

noncomputable section
universe u v
open CategoryTheory Opposite
open scoped Simplicial

namespace Quillen

/-- A constant simplicial map realizes to the actual constant continuous map. -/
theorem realization_const {X Y : SSet.{u}} (y : Y _⦋0⦌) (p : |X|) :
    SSet.toTop.map (SSet.const y : X ⟶ Y) p = realizationPoint y := by
  have hv : (SSet.yonedaEquiv.symm y).app _
      (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋0⦌) : (Δ[0] : SSet.{u}) _⦋0⦌) = y := by
    exact SSet.yonedaEquiv.apply_symm_apply y
  have hc : (SSet.const y : X ⟶ Y) =
      SSet.const (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋0⦌) : (Δ[0] : SSet.{u}) _⦋0⦌) ≫ SSet.yonedaEquiv.symm y := by
    rw [SSet.const_comp, hv]
  rw [hc, Functor.map_comp]
  change SSet.toTop.map (SSet.yonedaEquiv.symm y) _ = _
  exact congrArg (SSet.toTop.map (SSet.yonedaEquiv.symm y))
    (Subsingleton.elim _ default)

/-- The nerve map of a constant functor is the constant simplicial map. -/
theorem nerveMap_const {C D : Type u} [Category.{v} C] [Category.{v} D] (d : D) :
    CategoryTheory.nerveMap ((Functor.const C).obj d) = SSet.const (nerveVertex d) := by
  rfl

/-- A constant functor induces a constant continuous map of classifying spaces. -/
@[simp]
theorem classifyingSpaceMap_const_direct {C D : Type u} [Category.{v} C] [Category.{v} D]
    (d : D) : classifyingSpaceMap ((Functor.const C).obj d) =
      TopCat.const (X := ClassifyingSpace C) (classifyingSpacePoint d) := by
  ext p
  exact realization_const (nerveVertex d) p

end Quillen
