import Quillen.Waldhausen.QuillenComparison.EdgewiseIndices
import Quillen.Waldhausen.QuillenComparison.Reindexing

/-! # The canonical simplicial Q/S comparison map

The edgewise subdivision of the genuine diagonal S-construction maps to the
nerve of the existing Q-category. The i-th vertex is the quotient indexed by
[n-i,n+1+i] in nerve row n+1+i. All simplicial identities follow from the
strict reindexing theorem and the genuine reversed-first-half edgewise indices.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial CategoryTheory.Prod
universe v u

namespace Quillen.Waldhausen.QuillenComparison

@[simp]
theorem centralInterval_naturality {n m : SimplexCategory} (α : n ⟶ m)
    (i : Fin (n.len + 1)) :
    (nestedIntervalMap (Edgewise.ε.map α)).obj (centralInterval n i) =
      centralInterval m (α.toOrderHom i) := by
  apply Subtype.ext
  apply Prod.ext
  · exact lowerIndex_naturality α i
  · exact upperIndex_naturality α i

/-- Naturality of the central interval and nerve indices together. -/
theorem comparisonIndices_naturality {n m : SimplexCategory} (α : n ⟶ m) :
    comparisonIndices n ⋙
      ((SimplexCategory.toCat.map (Edgewise.ε.map α)).toFunctor.prod
        (nestedIntervalMap (Edgewise.ε.map α))) =
      (SimplexCategory.toCat.map α).toFunctor ⋙ comparisonIndices m := by
  apply CategoryTheory.Functor.ext
    (fun i ↦ Prod.ext (upperIndex_naturality α i) (centralInterval_naturality α i))

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : Quillen.ExactStructure C)

/-- An edgewise S-simplex gives an actual chain of Q-arrows. -/
def comparisonSimplex {n : SimplexCategory}
    (F : (sSet E.inflation (MorphismProperty.isomorphisms C)).obj (op (Edgewise.ε.obj n))) :
    (nerve (Q E.deflation E.inflation)).obj (op n) :=
  comparisonIndices n ⋙ gridQFunctor E F.2

/-- The comparison chain commutes with every face and degeneracy. -/
theorem comparisonSimplex_naturality {n m : SimplexCategory} (α : n ⟶ m)
    (F : (sSet E.inflation (MorphismProperty.isomorphisms C)).obj (op (Edgewise.ε.obj m))) :
    comparisonSimplex E ((sSet E.inflation (MorphismProperty.isomorphisms C)).map
      (Edgewise.ε.map α).op F) =
      (nerve (Q E.deflation E.inflation)).map α.op (comparisonSimplex E F) := by
  change comparisonIndices n ⋙ gridQFunctor E
      (F.2.precomp E.inflation (MorphismProperty.isomorphisms C) (Edgewise.ε.map α)) =
    (SimplexCategory.toCat.map α).toFunctor ⋙ comparisonIndices m ⋙ gridQFunctor E F.2
  rw [gridQFunctor_precomp, ← Functor.assoc, comparisonIndices_naturality, Functor.assoc]

/-- The canonical simplicial comparison from the edgewise S-model to Q. -/
def comparisonMap :
    Edgewise.subdivision (sSet E.inflation (MorphismProperty.isomorphisms C)) ⟶
      nerve (Q E.deflation E.inflation) where
  app n := ↾fun F ↦ comparisonSimplex E F
  naturality n m α := by
    ext F
    exact comparisonSimplex_naturality E α.unop F

end Quillen.Waldhausen.QuillenComparison
