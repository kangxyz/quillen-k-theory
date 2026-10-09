import Quillen.Waldhausen.SConstruction.WeakNaturalTransformation
import Quillen.Waldhausen.SConstruction.NerveCylinderZero

/-! # Based exact-functor homotopies with explicit chosen-zero equalities -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite MonoidalCategory
open scoped Simplicial
universe v u

namespace Quillen.Waldhausen

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {F G : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (η : F ⟶ G) (hη : ∀ X, W.weq (η.app X))
  (hF0 : F.obj V.zero = W.zero) (hG0 : G.obj V.zero = W.zero)

include hF0 hG0

/-- Strict chosen-zero equalities force the actual zero-vertex track of the
S-construction cylinder to be constant. Zero uniqueness supplies the
transformation's identity component at that vertex. -/
theorem weakNaturalTransformationCylinder_fixed_zero :
    SSet.yonedaEquiv.symm (zeroSimplex V.cof V.weq V.zero V.isZero (op ⦋0⦌)) ▷ Δ[1] ≫
        weakNaturalTransformationCylinder V W hF hG η hη =
      CartesianMonoidalCategory.fst Δ[0] Δ[1] ≫
        SSet.yonedaEquiv.symm (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌)) := by
  ext n z
  apply Subtype.ext
  exact nerveCylinderDiagram_eq_const_of_zero _ W.zero W.isZero
    (fun _ ↦ hF0) (fun _ ↦ hG0) z.2.down

/-- The actual realization homotopy stays at the chosen Waldhausen basepoint. -/
theorem weakNaturalTransformationRealizationHomotopy_fixed_zero (t : unitInterval) :
    weakNaturalTransformationRealizationHomotopy V W hF hG η hη (t, V.kBasepoint) =
      W.kBasepoint :=
  realizationSimplicialHomotopy_fixed_vertex
    (weakNaturalTransformationHomotopy V W hF hG η hη) _ _
    (weakNaturalTransformationCylinder_fixed_zero V W hF hG η hη hF0 hG0) t

/-- A genuine based homotopy of the original exact functors' realization maps. -/
def weakNaturalTransformationBasedHomotopy :
    (deloopingMap hF).hom.HomotopyRel (deloopingMap hG).hom {V.kBasepoint} where
  toHomotopy := weakNaturalTransformationRealizationHomotopy V W hF hG η hη
  prop' t x hx := by
    obtain rfl := Set.mem_singleton_iff.mp hx
    change weakNaturalTransformationRealizationHomotopy V W hF hG η hη (t, V.kBasepoint) =
      (deloopingMap hF).hom V.kBasepoint
    rw [weakNaturalTransformationRealizationHomotopy_fixed_zero V W hF hG η hη hF0 hG0]
    have h := deloopingMap_basepoint hF V.zero V.isZero
    simpa only [hF0] using h.symm

end Quillen.Waldhausen
