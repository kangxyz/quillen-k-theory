/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Waldhausen.Additivity.SeparatedPairMap

/-! # Original first/right product restrictions and their exact zero -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory Opposite Quillen Quillen.Waldhausen
open Quillen.Waldhausen.Additivity Quillen.Waldhausen.ExtensionCategory
open scoped Simplicial Topology
universe u v
namespace QuillenTest.SeparatedPairMap
variable {C : Type u} [Category.{v} C] (V : Structure C)

/-- Both independently bounded degrees use the original pair grid. -/
theorem original_grid (n m : SimplexCategoryᵒᵖ)
    (A : ((OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V).obj n).obj m) :
    (((separatedPairMap V).app n).app m A).1 = separatedPairGrid A.1 :=
  separatedPairMap_grid V n m A

/-- Independent interval and nerve restrictions retain the original whole pair. -/
theorem original_independent_reindex {n n' m m' : SimplexCategory}
    (α : n' ⟶ n) (β : m' ⟶ m)
    (A : Grid₂ (OrdinalSubdivision.δ.obj n) m ⥤ C) :
    separatedPairGrid (gridMap₂ (OrdinalSubdivision.δ.map α) β ⋙ A) =
      gridMap₂ α β ⋙ separatedPairGrid A := separatedPairGrid_reindex α β A

/-- The first projection is the unchanged original subdivision endpoint. -/
theorem original_first_projection :
    separatedPairMap V ≫
        bisimplicialSSetMap (productStructure V V).cof (productStructure V V).weq
          (fst_exact V V) =
      OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V) := separatedPairMap_fst V

/-- The right projection retains the distinct second-half natural transformation. -/
theorem original_right_projection :
    separatedPairMap V ≫
        bisimplicialSSetMap (productStructure V V).cof (productStructure V V).weq
          (snd_exact V V) = rightRestrictionMap V := separatedPairMap_snd V

/-- The actual product realization comparison has both original coordinates. -/
theorem original_realization_projection
    (x : |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    Product.deloopingComparison V V (separatedPairDeloopingMap V x) =
      (separatedFirstDeloopingMap V x, separatedRightDeloopingMap V x) :=
  separatedPairDeloopingMap_projection V x

/-- All three actual maps preserve their specified original chosen zero points. -/
theorem original_chosen_zeros :
    separatedFirstDeloopingMap V (subdivisionBasepoint V) = V.kBasepoint ∧
      separatedRightDeloopingMap V (subdivisionBasepoint V) = V.kBasepoint ∧
      separatedPairDeloopingMap V (subdivisionBasepoint V) = (productStructure V V).kBasepoint :=
  ⟨separatedFirstDeloopingMap_basepoint V, separatedRightDeloopingMap_basepoint V,
    separatedPairDeloopingMap_basepoint V⟩

/-- Every original cube coordinate retains both restrictions without choosing a product lift. -/
theorem original_cube_projection (n : ℕ)
    (p : GenLoop (Fin (n + 1))
      |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|
      (subdivisionBasepoint V)) (z : Fin (n + 1) → unitInterval) :
    Product.deloopingComparison V V (separatedPairDeloopingMap V (p z)) =
      (separatedFirstDeloopingMap V (p z), separatedRightDeloopingMap V (p z)) :=
  separatedPairDeloopingMap_projection V (p z)

/-- Degree zero retains both original restriction coordinates at every input time. -/
theorem original_degree_zero
    (p : GenLoop (Fin (0 + 1))
      |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|
      (subdivisionBasepoint V)) (z : Fin (0 + 1) → unitInterval) :
    Product.deloopingComparison V V (separatedPairDeloopingMap V (p z)) =
      (separatedFirstDeloopingMap V (p z), separatedRightDeloopingMap V (p z)) :=
  separatedPairDeloopingMap_projection V (p z)

end QuillenTest.SeparatedPairMap
