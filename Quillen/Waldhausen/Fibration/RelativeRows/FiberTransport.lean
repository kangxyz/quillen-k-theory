import Quillen.Waldhausen.Fibration.RelativeRows.TransitionHELP
import Quillen.Topology.HomotopyFiber.BasepointHELP

/-! # Full compact HELP at every original relative-row fiber

Actual row connectedness provides one path from the chosen zero for each
individual assertion. The proved genuine transport and arbitrary-square
naturality propagate full HELP to the original fiber map at that point.
No continuously chosen family of paths or inverse maps is used.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open scoped Simplicial Topology
universe u
namespace Quillen.Waldhausen.Fibration.RelativeRows
variable {C : Type u} [Category.{u} C] {V : Structure C}
  (N : NestedWeakEquivalences V) {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n)

/-- The original ordinal-transition fiber map over an arbitrary actual point. -/
def rowTransitionFiberAt (b : |(ordinarySRows (acyclicStructure N)).obj m|) : C(
    HomotopyFiber (SSet.toTop.map ((tailSRows N).app m)).hom b,
    HomotopyFiber (SSet.toTop.map ((tailSRows N).app n)).hom
      (SSet.toTop.map ((ordinarySRows (acyclicStructure N)).map α) b)) :=
  HomotopyPullback.transitionFiber
    (SSet.toTop.map ((tailSRows N).app m)).hom
    (SSet.toTop.map ((tailSRows N).app n)).hom
    (SSet.toTop.map ((relativeSRows N).map α)).hom
    (SSet.toTop.map ((ordinarySRows (acyclicStructure N)).map α)).hom
    (rowTransitionSquare N α) b

/-- The source restriction and complete postcomposed original path are literal. -/
@[simp] theorem rowTransitionFiberAt_apply
    (b : |(ordinarySRows (acyclicStructure N)).obj m|)
    (z : HomotopyFiber (SSet.toTop.map ((tailSRows N).app m)).hom b) :
    (rowTransitionFiberAt N α b z).val =
      (SSet.toTop.map ((relativeSRows N).map α) z.val.1,
       (SSet.toTop.map ((ordinarySRows (acyclicStructure N)).map α)).hom.comp z.val.2) := rfl

/-- At the chosen zero this is the original previously defined fiber map. -/
@[simp] theorem rowTransitionFiberAt_zero :
    rowTransitionFiberAt N α (realizationPoint (tailZeroVertex N m.unop)) =
      rowTransitionFiber N α := rfl

/-- Every actual fiber transition satisfies full compact HELP, including its
entire prescribed boundary homotopy. Only individual path connectedness is used. -/
theorem rowTransitionFiberAt_compactHELP
    (b : |(ordinarySRows (acyclicStructure N)).obj m|) :
    CompactHomotopyExtensionLiftingProperty (rowTransitionFiberAt N α b) :=
  HomotopyFiber.compactHELP_map_of_path
    (SSet.toTop.map ((tailSRows N).app m)).hom
    (SSet.toTop.map ((relativeSRows N).map α)).hom
    (SSet.toTop.map ((tailSRows N).app n)).hom
    (SSet.toTop.map ((ordinarySRows (acyclicStructure N)).map α)).hom
    (rowTransitionSquare N α).symm
    (PathConnectedSpace.somePath (realizationPoint (tailZeroVertex N m.unop)) b)
    (rowTransitionFiber_compactHELP N α)

end Quillen.Waldhausen.Fibration.RelativeRows
