import Quillen.Waldhausen.QuillenComparison.FlagPresentation
import Quillen.Waldhausen.QuillenComparison.RowSimplicial

/-! # Completion of admissible flags commutes with restriction -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe v u

namespace Quillen.Waldhausen.QuillenComparison

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : Quillen.ExactStructure C) {m n : SimplexCategory}
variable (A : Fin (n.len + 1) ⥤ C)
variable (hA : ∀ {i j} (f : i ⟶ j), E.inflation (A.map f))

/-- The canonical cokernel completion is strictly compatible with restriction. -/
theorem quotientDiagram_reindex (α : m ⟶ n) :
    quotientDiagram E ((SimplexCategory.toCat.map α).toFunctor ⋙ A)
      (fun f ↦ hA ((SimplexCategory.toCat.map α).toFunctor.map f)) =
      intervalMap α ⋙ quotientDiagram E A hA := rfl

/-- Restriction of a completed row is the completion of the restricted flag. -/
def flagRowReindexIso (α : m ⟶ n) :
    (rowReindex E α).obj (flagRow E A hA) ⟶
      flagRow E ((SimplexCategory.toCat.map α).toFunctor ⋙ A)
        (fun f ↦ hA ((SimplexCategory.toCat.map α).toFunctor.map f)) := Iso.refl _

@[reassoc (attr := simp)]
theorem flagQuotient_reindex (α : m ⟶ n) (p : Interval m) :
    flagQuotient E ((SimplexCategory.toCat.map α).toFunctor ⋙ A)
      (fun f ↦ hA ((SimplexCategory.toCat.map α).toFunctor.map f)) p =
      flagQuotient E A hA ((intervalMap α).obj p) := rfl

end Quillen.Waldhausen.QuillenComparison
