/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.DoubleMappingCylinder.LocalComparison
public import Quillen.Topology.HomotopyFiber.StrictWeakTransport
public import Quillen.Topology.HELP.TwoOfThree

/-! # Actual collar strict fibers compared with their homotopy fibers

An actual total-space homotopy equivalence to a genuine fibration transports
full compact HELP from its original strict-fiber map to the original
strict-fiber inclusion. The double-cylinder instances use the existing
literal collar comparison and unchanged endpoint pullback fibration.
No local or global HLP of the original collar is asserted.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
namespace Quillen.HomotopyFiber

/-- A genuine equivalent fibration model detects full compact HELP for the
canonical strict-fiber inclusion, without requiring the original map to lift. -/
theorem strictFiberInclusion_compactHELP_of_equiv
    {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
    (q : C(F, B)) (e : ContinuousMap.HomotopyEquiv E F)
    (hq : HomotopyLiftingProperty q) (b : B)
    (hf : CompactHomotopyExtensionLiftingProperty
      (strictMapOver (q.comp e.toFun) q e.toFun rfl b)) :
    CompactHomotopyExtensionLiftingProperty (strictFiberInclusion (q.comp e.toFun) b) := by
  have hg := compactHELP_of_homotopyEquiv (sourceEquiv q e b)
  have htarget := compactHELP_of_homotopyEquiv (strictFiberHomotopyEquivOfLifting q hq b)
  have hc := htarget.comp hf
  have hcomp : CompactHomotopyExtensionLiftingProperty
      ((sourceMap q e.toFun b).comp (strictFiberInclusion (q.comp e.toFun) b)) := by
    convert hc using 1
    rfl
  exact hcomp.cancel_second hg

end Quillen.HomotopyFiber
namespace Quillen.DoubleCylinder
variable {A B C D A' B' C' D' : TopCat.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {f' : A' ⟶ B'} {g' : A' ⟶ C'}
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  {l' : A' ⊗ TopCat.I ⟶ D'} {e' : TopCat.of (B' ⊕ C') ⟶ D'}
  (sq : IsPushout (TheoremA.intervalEndpoints A) (endMap f g) l e)
  (sq' : IsPushout (TheoremA.intervalEndpoints A') (endMap f' g') l' e')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g') (cut : unitInterval)

/-- The original strict-fiber map of the actual left collar comparison. -/
def leftCollarComparisonFiber (hcut : 0 < cut) (y : LeftCollar f' g' sq' cut) :=
  HomotopyFiber.strictMapOver (leftCollarMap sq sq' a b c wf wg cut).hom
    (HomotopyPullback.strictBaseProjection b.hom (leftCollarProjection f' g' sq' cut hcut).hom)
    (leftCollarComparison sq sq' a b c wf wg cut hcut).hom rfl y

/-- The original strict-fiber map of the actual right collar comparison. -/
def rightCollarComparisonFiber (hcut : cut < 1) (y : RightCollar f' g' sq' cut) :=
  HomotopyFiber.strictMapOver (rightCollarMap sq sq' a b c wf wg cut).hom
    (HomotopyPullback.strictBaseProjection c.hom (rightCollarProjection f' g' sq' cut hcut).hom)
    (rightCollarComparison sq sq' a b c wf wg cut hcut).hom rfl y

/-- Literal left collar transport; the hypothesis is on the displayed
comparison fiber, not on the desired strict-to-homotopy-fiber inclusion. -/
theorem leftCollar_strictFiberInclusion_compactHELP (hcut : 0 < cut)
    (hb : HomotopyLiftingProperty b.hom) (y : LeftCollar f' g' sq' cut)
    (hy : CompactHomotopyExtensionLiftingProperty
      (leftCollarComparisonFiber sq sq' a b c wf wg cut hcut y)) :
    CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictFiberInclusion (leftCollarMap sq sq' a b c wf wg cut).hom y) :=
  HomotopyFiber.strictFiberInclusion_compactHELP_of_equiv
    (HomotopyPullback.strictBaseProjection b.hom (leftCollarProjection f' g' sq' cut hcut).hom)
    (leftCollarComparisonHomotopyEquiv sq sq' a b c wf wg cut hcut)
    (HomotopyLiftingProperty.baseChange _ _ hb) y hy

/-- The corresponding literal right collar transport. -/
theorem rightCollar_strictFiberInclusion_compactHELP (hcut : cut < 1)
    (hc : HomotopyLiftingProperty c.hom) (y : RightCollar f' g' sq' cut)
    (hy : CompactHomotopyExtensionLiftingProperty
      (rightCollarComparisonFiber sq sq' a b c wf wg cut hcut y)) :
    CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictFiberInclusion (rightCollarMap sq sq' a b c wf wg cut).hom y) :=
  HomotopyFiber.strictFiberInclusion_compactHELP_of_equiv
    (HomotopyPullback.strictBaseProjection c.hom (rightCollarProjection f' g' sq' cut hcut).hom)
    (rightCollarComparisonHomotopyEquiv sq sq' a b c wf wg cut hcut)
    (HomotopyLiftingProperty.baseChange _ _ hc) y hy

end Quillen.DoubleCylinder
