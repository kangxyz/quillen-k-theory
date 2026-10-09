import Quillen.Waldhausen.QuillenComparison.RowFull
import Quillen.Waldhausen.QuillenComparison.BisimplicialMap

/-! # Exact transport formulas for terminal interval spans -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe v u

namespace Quillen.Waldhausen.QuillenComparison

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : Quillen.ExactStructure C)

@[simp]
theorem qIsoOfIso_eqToIso {X Y : C} (h : X = Y) :
    (E.qIsoOfIso (eqToIso h)).hom =
      eqToHom (congrArg (Q.of E.deflation E.inflation) h) := by
  subst Y
  rfl

/-- An interval arrow becomes the actual whole-row span after the displayed
source and target index identifications. -/
theorem rowInterval_map_to_whole {n : SimplexCategory} (F : Row E n)
    {a b : NestedInterval n} (f : a ⟶ b) (p : NestedInterval n)
    (ha : a = p) (hb : b = topNested n) :
    (rowIntervalFunctor E F).map f ≫
        (E.qIsoOfIso (eqToIso (congrArg (fun k ↦ F.diagram.obj (nestedToInterval k)) hb))).hom =
      (E.qIsoOfIso (eqToIso (congrArg (fun k ↦ F.diagram.obj (nestedToInterval k)) ha))).hom ≫
        Q.mkHom E.deflation E.inflation (wholeSpan E F p) := by
  subst a
  subst b
  change Q.mkHom E.deflation E.inflation (intervalSpan E F.simplex 0 (leOfHom f)) ≫
    𝟙 _ = 𝟙 _ ≫ Q.mkHom E.deflation E.inflation (wholeSpan E F p)
  rw [Category.id_comp, Category.comp_id]
  rfl

end Quillen.Waldhausen.QuillenComparison
