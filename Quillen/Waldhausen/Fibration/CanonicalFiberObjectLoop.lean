/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Fibration.CanonicalFiberMap
public import Quillen.Topology.HomotopyGroups.Loop.DegreeShift
public import Quillen.Waldhausen.Fibration.WeakObjectTrack
public import Quillen.Waldhausen.GrothendieckComparison.ObjectNaturality
public import Quillen.Waldhausen.SConstruction.ObjectTransformationTrack

/-!
# Original acyclic object loops in the canonical fiber

The source coordinate is the original object loop. The fiber-path coordinate retains the
specified reversed zero-to-acyclic-inclusion homotopy. These are the actual representatives
needed for a localization boundary calculation; no unit-boundary identity is assumed here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Topology
universe u v
namespace Quillen.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V)

/-- The original acyclic object loop maps through the actual canonical homotopy-fiber map. -/
def canonicalFiberObjectLoop (X : AcyclicCategory N) :
    Path (HomotopyFiber.basepoint (changeWeakMap N) N.coarse.kBasepoint V.kBasepoint
      (changeWeakMap_basepoint N))
      (HomotopyFiber.basepoint (changeWeakMap N) N.coarse.kBasepoint V.kBasepoint
        (changeWeakMap_basepoint N)) :=
  basedLoopMap (canonicalFiberMap N) (canonicalFiberMap_basepoint N)
    ((acyclicStructure N).kZeroObjectLoop X)

/-- Its original source coordinate is the unchanged fine object loop. -/
theorem canonicalFiberObjectLoop_projection (X : AcyclicCategory N) (t : unitInterval) :
    (canonicalFiberObjectLoop N X t).val.1 = V.kZeroObjectLoop X.obj t := by
  exact congrArg (fun p : Path V.kBasepoint V.kBasepoint => p t)
    (deloopingMap_kZeroObjectLoop (acyclicInclusion_exact N) rfl X)

/-- Its independent fiber coordinate retains the full original reversed zero track. -/
theorem canonicalFiberObjectLoop_path (X : AcyclicCategory N) (t s : unitInterval) :
    (canonicalFiberObjectLoop N X t).val.2 s =
      acyclicNullhomotopy N (s, (acyclicStructure N).kZeroObjectLoop X t) := rfl

/-- The same coarse acyclic object has the specified actual weak zero-to-object track. -/
def acyclicObjectWeakTrack (X : AcyclicCategory N) :
    (N.coarse.kZeroObjectLoop N.coarse.zero).Homotopy (N.coarse.kZeroObjectLoop X.obj) :=
  N.coarse.weakObjectLoopTrack (N.coarse.isZero.to_ X.obj) X.property

/-- The original diagonal weak-arrow path is retained at the comparison midpoint. -/
theorem acyclicObjectWeakTrack_midpoint (X : AcyclicCategory N) (t : unitInterval) :
    acyclicObjectWeakTrack N X (⟨1 / 2, by norm_num, by norm_num⟩, t) =
      realizationEdgePath (N.coarse.weakObjectEdge (N.coarse.isZero.to_ X.obj) X.property) t :=
  N.coarse.weakObjectLoopTrack_midpoint _ _ t

/-- The original zero-to-acyclic exact-functor cylinder evaluated at the actual object loop. -/
def acyclicObjectTransformationTrack (X : AcyclicCategory N) :
    (N.coarse.kZeroObjectLoop N.coarse.zero).Homotopy (N.coarse.kZeroObjectLoop X.obj) :=
  objectTransformationTrack (acyclicStructure N) N.coarse
    (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact N)
    (zeroToAcyclicInclusion N) (zeroToAcyclicInclusion_weak N) rfl
    (by simpa only [acyclicInclusion_zero] using N.coarse_zero.symm) X

/-- The actual canonical fiber coordinate is exactly the original transformation track reversed.
-/
theorem canonicalFiberObjectLoop_path_transformation (X : AcyclicCategory N)
    (t s : unitInterval) :
    (canonicalFiberObjectLoop N X t).val.2 s =
      acyclicObjectTransformationTrack N X (unitInterval.symm s, t) := rfl

end Quillen.Waldhausen.Fibration
