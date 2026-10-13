/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Fibration.CanonicalFiberObjectLoop
public import Quillen.Waldhausen.SConstruction.ObjectTransformationSquareRealization

/-!
# The original reversed weak-square coordinate in the canonical fiber

The fiber coordinate is the actual zero-to-acyclic component square, with its nerve parameter
reversed and its object-loop parameter unchanged. This is an equality of the specified family.
A later Laurent application must match the original coordinate unit and its actual loop orientation;
the cofiber sign isomorphism alone does not establish that comparison.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Convexity
open scoped Topology
universe u v
namespace Quillen.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V)

/-- The full fiber path uses the original component square at the reversed nerve coordinate. -/
theorem canonicalFiberObjectLoop_path_square (X : AcyclicCategory N)
    (t s : unitInterval) :
    (canonicalFiberObjectLoop N X t).val.2 s =
      bisimplexRealization N.coarse
        (N.coarse.weakObjectSimplex ((zeroToAcyclicInclusion N).app X)
          (zeroToAcyclicInclusion_weak N X)).val
        ((isSimplex₂_diagonal_iff N.coarse.cof N.coarse.weq _).mpr
          (N.coarse.weakObjectSimplex ((zeroToAcyclicInclusion N).app X)
            (zeroToAcyclicInclusion_weak N X)).property)
        (StdSimplex.homeomorphI.symm t,
          StdSimplex.homeomorphI.symm (unitInterval.symm s)) := by
  rw [canonicalFiberObjectLoop_path_transformation]
  exact objectTransformationRealization_square (acyclicStructure N) N.coarse
    (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact N)
    (zeroToAcyclicInclusion N) (zeroToAcyclicInclusion_weak N) rfl
    (by simpa only [acyclicInclusion_zero] using N.coarse_zero.symm) X
    (unitInterval.symm s) t

end Quillen.Waldhausen.Fibration
