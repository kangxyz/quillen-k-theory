/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.QuillenComparison.BisimplicialMap
public import Quillen.Waldhausen.QuillenComparison.RowDiagonal
public import Quillen.Topology.Realization.EdgewiseBisimplicial
public import Quillen.Topology.Realization.ClassificationHomotopy

/-! # Exact-map factorization of the canonical Q/S comparison

The direct comparison is precisely the composition of the original-model
identification, upper-nerve restriction, rowwise Q comparison, classification
model identification, and natural diagonal evaluation. All model changes
apart from the still-separate rowwise equivalence are already genuine
realization homotopy equivalences.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe v u

namespace Quillen.Waldhausen.QuillenComparison

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : Quillen.ExactStructure C)

/-- The canonical model-identification and upper-index restriction. -/
def subdivisionToRows : Edgewise.subdivision (sSet E.inflation (MorphismProperty.isomorphisms C)) ⟶
    TheoremA.diagonalSSet (Edgewise.ε.op ⋙ rowNerve E) :=
  Edgewise.subdivisionFunctor.map (rowDiagonalIso E).hom ≫
    (Edgewise.doubleDiagonalIso (rowNerve E)).inv ≫
      TheoremA.diagonalMap (Functor.whiskerLeft (Edgewise.ε.op ⋙ rowNerve E)
        Edgewise.endpointNatTrans)

/-- The actual Q comparison in row-groupoid coordinates. -/
def rowsToQ : TheoremA.diagonalSSet (Edgewise.ε.op ⋙ rowNerve E) ⟶
    nerve (Q E.deflation E.inflation) :=
  TheoremA.diagonalMap (rowChainNerveMap E) ≫
    (chainCoreDiagonalIso (Q E.deflation E.inflation)).inv ≫
      Classification.evaluation (Q E.deflation E.inflation)

/-- This is an equality of the actual simplicial maps, not only a comparison
of abstract homotopy types. -/
theorem comparisonMap_factorization :
    subdivisionToRows E ≫ rowsToQ E = comparisonMap E := by
  ext n F
  rfl

/-- All model changes before the rowwise comparison already realize to an
actual homotopy equivalence. -/
def subdivisionToRowsHomotopyEquiv :
    ContinuousMap.HomotopyEquiv
      |Edgewise.subdivision (sSet E.inflation (MorphismProperty.isomorphisms C))|
      |TheoremA.diagonalSSet (Edgewise.ε.op ⋙ rowNerve E)| :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso (Edgewise.subdivisionFunctor.mapIso (rowDiagonalIso
    E)))).toHomotopyEquiv.trans
    ((TopCat.homeoOfIso (SSet.toTop.mapIso (Edgewise.doubleDiagonalIso (rowNerve
      E)).symm)).toHomotopyEquiv.trans
      (Edgewise.upperIndexRealizationHomotopyEquiv (rowNerve E)))

@[simp]
theorem subdivisionToRowsHomotopyEquiv_toFun :
    (subdivisionToRowsHomotopyEquiv E).toFun = (SSet.toTop.map (subdivisionToRows E)).hom := by
  simp only [subdivisionToRowsHomotopyEquiv, ContinuousMap.HomotopyEquiv.trans,
    Edgewise.upperIndexRealizationHomotopyEquiv_toFun, subdivisionToRows, Functor.map_comp]
  rfl

end Quillen.Waldhausen.QuillenComparison
