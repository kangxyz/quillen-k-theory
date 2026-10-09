import Quillen.Topology.Realization.TwoSidedBar
import Quillen.Topology.Realization.BisimplicialEquivalence
import Quillen.Topology.Realization.ProductComparison
import Quillen.Topology.ClassifyingSpace.Equivalence

/-! # The first genuine two-sided bar augmentation equivalence

Each last-ordinal standard simplex is finite and contractible. Its actual
first projection is therefore a realization homotopy equivalence. Coproduct
assembly and rowwise diagonal invariance retain the original drop map.
-/
noncomputable section
open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen.TwoSidedBar
open TheoremA

/-- Projection away from an actual finite standard simplex is an ordinary
homotopy equivalence, using only the permitted finite-factor product map. -/
def simplexProjectionHomotopyEquiv (X : SSet.{u}) (n : SimplexCategory) :
    ContinuousMap.HomotopyEquiv |X ⊗ SSet.stdSimplex.obj n| |X| := by
  letI : ContractibleSpace |SSet.stdSimplex.{u}.obj n| := by
    let : ContractibleSpace |nerve (ULift.{u} (Fin (n.len + 1)))| := by
      change ContractibleSpace (ClassifyingSpace (ULift.{u} (Fin (n.len + 1))))
      infer_instance
    exact (TopCat.homeoOfIso (SSet.toTop.mapIso (SSet.stdSimplex.isoNerve n.len))).contractibleSpace
  let E := (ProductRealization.finiteRightHomeomorph X (SSet.stdSimplex.obj n)).toHomotopyEquiv.trans
    (((ContinuousMap.HomotopyEquiv.refl |X|).prodCongr
      (ContractibleSpace.hequiv_unit |SSet.stdSimplex.obj n|).some).trans
        (Homeomorph.prodUnique |X| Unit).toHomotopyEquiv)
  exact {
    E with toFun := (SSet.toTop.map (fst X (SSet.stdSimplex.obj n))).hom
           left_inv := E.left_inv
           right_inv := E.right_inv }

@[simp] theorem simplexProjectionHomotopyEquiv_toFun (X : SSet.{u}) (n : SimplexCategory) :
    (simplexProjectionHomotopyEquiv X n).toFun =
      (SSet.toTop.map (fst X (SSet.stdSimplex.obj n))).hom := rfl

variable {D : Type u} [SmallCategory D]
  (L : D ⥤ SimplexCategoryᵒᵖ) (H : D ⥤ SSet.{u})

/-- The actual coordinate-dropping map is an equivalence on each row. -/
def dropRowHomotopyEquiv (p : SimplexCategoryᵒᵖ) :
    ContinuousMap.HomotopyEquiv |row L H p| |replacementRow H p| :=
  realizationSigmaHomotopyEquiv fun s : (nerve D).obj p ↦
    simplexProjectionHomotopyEquiv (H.obj (s.obj 0))
      (L.obj (s.obj (Fin.last p.unop.len))).unop

@[simp] theorem dropRowHomotopyEquiv_toFun (p : SimplexCategoryᵒᵖ) :
    (dropRowHomotopyEquiv L H p).toFun = (SSet.toTop.map (dropRow L H p)).hom :=
  realizationSigmaHomotopyEquiv_toFun
    (fun s : (nerve D).obj p ↦ fst (H.obj (s.obj 0))
      (SSet.stdSimplex.obj (L.obj (s.obj (Fin.last p.unop.len))).unop))
    (fun s ↦ simplexProjectionHomotopyEquiv (H.obj (s.obj 0))
      (L.obj (s.obj (Fin.last p.unop.len))).unop)
    (fun _ ↦ rfl)

/-- The prescribed bar-drop map realizes to a genuine homotopy equivalence. -/
def dropRealizationHomotopyEquiv :
    ContinuousMap.HomotopyEquiv |diagonalSSet (object L H)| |replacementDiagonal H| :=
  BisimplicialRealization.diagonalRealizationHomotopyEquiv (drop L H)
    (fun n ↦ dropRowHomotopyEquiv L H (op ⦋n⦌))
    (fun n ↦ dropRowHomotopyEquiv_toFun L H (op ⦋n⦌))

@[simp] theorem dropRealizationHomotopyEquiv_toFun :
    (dropRealizationHomotopyEquiv L H).toFun =
      (SSet.toTop.map (diagonalMap (drop L H))).hom := rfl

end Quillen.TwoSidedBar
