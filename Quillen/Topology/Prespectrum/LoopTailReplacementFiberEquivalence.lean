/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.LoopTailReplacementFiber
public import Quillen.Topology.HomotopyFiber.Separation
public import Quillen.Topology.Prespectrum.LoopTailOmega
public import Quillen.Topology.Prespectrum.StableOmegaLevelDetection
public import Quillen.Topology.Prespectrum.FiberOmega

/-!
# Complete weak fiber preservation by the original loop-tail replacement

Under T1 separation of the original source and target levels, the constructed original comparison
from the replacement of the path-space fiber to the path-space fiber of the replacement map is a
stable equivalence. Its literal unit triangle and the existing all-integer fiber LES prove this.
Both original endpoints are then proved Omega using the actual fiber structure comparison, so
all-component Omega detection makes this same comparison completely weak at every level.

Fiber T1 separation is derived from the original source and target; no T1 assumption is imposed
on replacement levels. No cone-preservation or general stable-cofiber theorem is asserted.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory

universe u

namespace Quillen.LoopPrespectrum

variable {E F : LoopPrespectrum.{u}} (f : E ⟶ F)

/-- Separation of the unchanged path-space fiber levels follows from the two original levels. -/
instance homotopyFiber_t1Space (k : ℕ) [T1Space (E.space k)] [T1Space (F.space k)] :
    T1Space ((homotopyFiber f).space k) :=
  inferInstanceAs (T1Space (HomotopyFiber (f.map k) (F.point k)))

variable [∀ k, T1Space (E.space k)] [∀ k, T1Space (F.space k)]

/-- The actual unit-square map on path-space fibers is stable by the original all-integer LES. -/
theorem loopTailReplacementUnitSquare_fiber_isStableEquivalence :
    IsStableEquivalence (homotopyFiberMap (loopTailReplacementUnitSquare f)) :=
  homotopyFiberMap_isStableEquivalence (loopTailReplacementUnitSquare f)
    (loopTailReplacementInclusion_isStableEquivalence E)
    (loopTailReplacementInclusion_isStableEquivalence F)

/-- The comparison's actual stable map is the original unit-square fiber map after the inverse
of the original initial-inclusion stable isomorphism. -/
theorem loopTailReplacementFiberComparison_stableMap_eq (d : ℤ) :
    (stableHomotopyFunctor d).map (loopTailReplacementFiberComparison f) =
      (loopTailReplacementStableHomotopyIso (homotopyFiber f) d).inv ≫
        (stableHomotopyFunctor d).map (homotopyFiberMap (loopTailReplacementUnitSquare f)) := by
  apply (cancel_epi (loopTailReplacementStableHomotopyIso (homotopyFiber f) d).hom).mp
  rw [Iso.hom_inv_id_assoc, loopTailReplacementStableHomotopyIso_hom,
    ← Functor.map_comp, loopTailReplacementFiberComparison_initial]

/-- The constructed original comparison is a stable equivalence, by its literal unit triangle
and the actual fiber LES rather than a cone or abstract replacement assumption. -/
theorem loopTailReplacementFiberComparison_isStableEquivalence :
    IsStableEquivalence (loopTailReplacementFiberComparison f) := by
  intro d
  rw [loopTailReplacementFiberComparison_stableMap_eq]
  have := loopTailReplacementUnitSquare_fiber_isStableEquivalence f d
  infer_instance

/-- The same original comparison is completely weak at every level. Both endpoints are proved
Omega; target closure uses the original two-parameter fiber structure comparison. -/
theorem loopTailReplacementFiberComparison_isWeakHomotopyEquivalence (k : ℕ) :
    IsWeakHomotopyEquivalence ((loopTailReplacementFiberComparison f).map k) :=
  level_isWeakHomotopyEquivalence_of_isStableEquivalence
    (loopTailReplacement_isOmega (homotopyFiber f))
    (homotopyFiber_isOmega (loopTailReplacementMap f)
      (loopTailReplacement_isOmega E) (loopTailReplacement_isOmega F))
    (loopTailReplacementFiberComparison f)
    (loopTailReplacementFiberComparison_isStableEquivalence f) k

end Quillen.LoopPrespectrum
