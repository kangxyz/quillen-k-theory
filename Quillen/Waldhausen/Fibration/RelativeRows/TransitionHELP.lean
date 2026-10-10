/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.Fibration.RelativeRows.TransitionCartesian
public import Quillen.Topology.Realization.SplitFiberTransitionHELP

/-! # Full compact HELP for the original chosen relative-row fiber transition

The source fiber is over the actual chosen zero tail. The target fiber is over
its literal image under the actual base restriction. The entire original path
is postcomposed, with no change to the original square or source map.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology
universe u
namespace Quillen.Waldhausen.Fibration.RelativeRows
variable {C : Type u} [Category.{u} C] {V : Structure C}
  (N : NestedWeakEquivalences V) {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n)

/-- The original fiber transition over the genuine chosen source zero tail,
with target over its literal image under the original realized base map. -/
def rowTransitionFiber : C(
    HomotopyFiber (SSet.toTop.map ((tailSRows N).app m)).hom
      (realizationPoint (tailZeroVertex N m.unop)),
    HomotopyFiber (SSet.toTop.map ((tailSRows N).app n)).hom
      (SSet.toTop.map ((ordinarySRows (acyclicStructure N)).map α)
        (realizationPoint (tailZeroVertex N m.unop)))) :=
  HomotopyPullback.transitionFiber
    (SSet.toTop.map ((tailSRows N).app m)).hom
    (SSet.toTop.map ((tailSRows N).app n)).hom
    (SSet.toTop.map ((relativeSRows N).map α)).hom
    (SSet.toTop.map ((ordinarySRows (acyclicStructure N)).map α)).hom
    (rowTransitionSquare N α) (realizationPoint (tailZeroVertex N m.unop))

/-- The actual source restriction and whole original postcomposed path are literal. -/
@[simp] theorem rowTransitionFiber_apply
    (z : HomotopyFiber (SSet.toTop.map ((tailSRows N).app m)).hom
      (realizationPoint (tailZeroVertex N m.unop))) :
    (rowTransitionFiber N α z).val =
      (SSet.toTop.map ((relativeSRows N).map α) z.val.1,
       (SSet.toTop.map ((ordinarySRows (acyclicStructure N)).map α)).hom.comp z.val.2) := rfl

/-- Actual degreewise additivity and strict split naturality give full compact
HELP of the original chosen-fiber transition, retaining prescribed boundaries. -/
theorem rowTransitionFiber_compactHELP :
    CompactHomotopyExtensionLiftingProperty (rowTransitionFiber N α) := by
  have hsquare : (relativeSRows N).map α ≫ firstTailSSet N n.unop ≫ snd _ _ =
      firstTailSSet N m.unop ≫ snd _ _ ≫ (ordinarySRows (acyclicStructure N)).map α := by
    rw [firstTailSSet_snd, ← Category.assoc, firstTailSSet_snd]
    exact (tailSRows N).naturality α
  have hsection : (fiberSRows N).app m ≫ (relativeSRows N).map α = (fiberSRows N).app n := by
    simpa using ((fiberSRows N).naturality α).symm
  have h := SplitRealizationFiber.transition_compactHELP_of_natural_split
    (firstTailSSet N m.unop) (firstTailSSet N n.unop)
    ((fiberSRows N).app m) ((fiberSRows N).app n)
    (tailZeroVertex N m.unop) (tailZeroVertex N n.unop)
    (fiber_firstTailSSet N m.unop) (fiber_firstTailSSet N n.unop)
    ((relativeSRows N).map α) ((ordinarySRows (acyclicStructure N)).map α)
    hsquare hsection
    (firstTailSSetRealizationHomotopyEquiv N m.unop)
    (firstTailSSetRealizationHomotopyEquiv_toFun N m.unop)
    (firstTailSSetRealizationHomotopyEquiv N n.unop)
    (firstTailSSetRealizationHomotopyEquiv_toFun N n.unop)
  have transport
      (p : C(|(relativeSRows N).obj m|, |(ordinarySRows (acyclicStructure N)).obj m|))
      (q : C(|(relativeSRows N).obj n|, |(ordinarySRows (acyclicStructure N)).obj n|))
      (hp : p = (SSet.toTop.map ((tailSRows N).app m)).hom)
      (hq : q = (SSet.toTop.map ((tailSRows N).app n)).hom)
      (w : q.comp (SSet.toTop.map ((relativeSRows N).map α)).hom =
        (SSet.toTop.map ((ordinarySRows (acyclicStructure N)).map α)).hom.comp p)
      (hw : CompactHomotopyExtensionLiftingProperty
        (HomotopyPullback.transitionFiber p q
          (SSet.toTop.map ((relativeSRows N).map α)).hom
          (SSet.toTop.map ((ordinarySRows (acyclicStructure N)).map α)).hom
          w (realizationPoint (tailZeroVertex N m.unop)))) :
      CompactHomotopyExtensionLiftingProperty (rowTransitionFiber N α) := by
    subst p
    subst q
    exact hw
  exact transport _ _ (rowFiberProjection_eq N m.unop)
    (rowFiberProjection_eq N n.unop) _ h

end Quillen.Waldhausen.Fibration.RelativeRows
