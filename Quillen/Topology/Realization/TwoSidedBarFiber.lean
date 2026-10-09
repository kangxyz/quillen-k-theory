import Quillen.Topology.Realization.TwoSidedBarEquivalence
import Quillen.Topology.HomotopyFiber.Map

/-! # The actual augmentation maps on homotopy fibers

The original drop and evaluation squares induce their literal source/path
maps on the compact-open-path homotopy fibers. No weak-equivalence conclusion
is inserted into these constructions. These are the prescribed maps to which
the separate weak square-transport theorem will apply.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open scoped Simplicial Topology
universe u
namespace Quillen.TwoSidedBar
open TheoremA

/-- The diagonal of the actual coefficientwise bar map. -/
def barMap {H J : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (η : H ⟶ J) :
    diagonalSSet (bar H) ⟶ diagonalSSet (bar J) :=
  diagonalMap (map indexProjection (Functor.whiskerLeft indexProjection η))

/-- The original map of the universe-aligned simplicial replacements. -/
def replacementMap {H J : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (η : H ⟶ J) :
    replacementDiagonal (liftedDiagram H) ⟶ replacementDiagonal (liftedDiagram J) :=
  diagonalMap (simplicialReplacementMap (Functor.whiskerLeft indexProjection η))

/-- The actual first augmentation at diagonal level. -/
def dropMap (H : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    diagonalSSet (bar H) ⟶ replacementDiagonal (liftedDiagram H) :=
  diagonalMap (drop indexProjection (liftedDiagram H))

variable {H J : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (η : H ⟶ J)

/-- The complete drop square commutes in the actual simplicial category. -/
theorem dropMap_naturality :
    barMap η ≫ dropMap J = dropMap H ≫ replacementMap η :=
  congrArg diagonalMap (drop_naturality indexProjection (Functor.whiskerLeft indexProjection η))

/-- The actual realized drop square, in the orientation of the fiber-map API. -/
theorem realizedDropSquare :
    (SSet.toTop.map (dropMap J)).hom.comp (SSet.toTop.map (barMap η)).hom =
      (SSet.toTop.map (replacementMap η)).hom.comp (SSet.toTop.map (dropMap H)).hom := by
  simpa only [Functor.map_comp, TopCat.hom_comp] using
    congrArg (fun f ↦ (SSet.toTop.map f).hom) (dropMap_naturality η)

/-- The actual realized evaluation square, retaining the original diagonal map. -/
theorem realizedEvaluationSquare :
    (SSet.toTop.map (evaluationMap J)).hom.comp (SSet.toTop.map (barMap η)).hom =
      (SSet.toTop.map (diagonalMap η)).hom.comp (SSet.toTop.map (evaluationMap H)).hom := by
  have h : barMap η ≫ evaluationMap J = evaluationMap H ≫ diagonalMap η :=
    evaluationMap_naturality η
  simpa only [Functor.map_comp, TopCat.hom_comp] using
    congrArg (fun f ↦ (SSet.toTop.map f).hom) h

/-- The literal drop augmentation on original homotopy fibers. -/
def dropFiberMap (y : |diagonalSSet (bar J)|) :
    C(HomotopyFiber (SSet.toTop.map (barMap η)).hom y,
      HomotopyFiber (SSet.toTop.map (replacementMap η)).hom (SSet.toTop.map (dropMap J) y)) :=
  HomotopyFiber.map (SSet.toTop.map (dropMap H)).hom (SSet.toTop.map (dropMap J)).hom
    (realizedDropSquare η) y

/-- The literal evaluation augmentation on original homotopy fibers. -/
def evaluationFiberMap (y : |diagonalSSet (bar J)|) :
    C(HomotopyFiber (SSet.toTop.map (barMap η)).hom y,
      HomotopyFiber (SSet.toTop.map (diagonalMap η)).hom (SSet.toTop.map (evaluationMap J) y)) :=
  HomotopyFiber.map (SSet.toTop.map (evaluationMap H)).hom (SSet.toTop.map (evaluationMap J)).hom
    (realizedEvaluationSquare η) y

@[simp] theorem dropFiberMap_source (y : |diagonalSSet (bar J)|)
    (p : HomotopyFiber (SSet.toTop.map (barMap η)).hom y) :
    (dropFiberMap η y p).1.1 = SSet.toTop.map (dropMap H) p.1.1 := rfl

@[simp] theorem dropFiberMap_path (y : |diagonalSSet (bar J)|)
    (p : HomotopyFiber (SSet.toTop.map (barMap η)).hom y) :
    (dropFiberMap η y p).1.2 = (SSet.toTop.map (dropMap J)).hom.comp p.1.2 := rfl

@[simp] theorem evaluationFiberMap_source (y : |diagonalSSet (bar J)|)
    (p : HomotopyFiber (SSet.toTop.map (barMap η)).hom y) :
    (evaluationFiberMap η y p).1.1 = SSet.toTop.map (evaluationMap H) p.1.1 := rfl

@[simp] theorem evaluationFiberMap_path (y : |diagonalSSet (bar J)|)
    (p : HomotopyFiber (SSet.toTop.map (barMap η)).hom y) :
    (evaluationFiberMap η y p).1.2 = (SSet.toTop.map (evaluationMap J)).hom.comp p.1.2 := rfl

/-- Coefficient maps retain the prescribed vertex at the original zero ordinal. -/
@[simp] theorem barMap_vertex (x : (diagonalSSet H) _⦋0⦌) :
    (barMap η).app (op ⦋0⦌) (vertex H x) = vertex J ((diagonalMap η).app (op ⦋0⦌) x) := rfl

/-- Realized evaluation preserves the prescribed original point exactly. -/
@[simp] theorem evaluationMap_realizationPoint (x : (diagonalSSet H) _⦋0⦌) :
    SSet.toTop.map (evaluationMap H) (realizationPoint (vertex H x)) = realizationPoint x := by
  rw [realizationPoint_naturality, evaluationMap_vertex]

end Quillen.TwoSidedBar
