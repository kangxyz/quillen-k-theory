/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.StrictSquareSplitNull
public import Quillen.Topology.Prespectrum.SplitSquareSeed
public import Quillen.Topology.Prespectrum.NullLoopNaturality

/-!
# Original strict-to-split forward-seed evaluation

The unit square and the proved comparison of the two specified source nulls compare the
complete original null/unit/null seeds. The source uses the undelayed strict cone contraction;
the target uses its original positive split followed by its cone contraction. No reparameterized
source seed replaces the given one. Concrete applications must prove the displayed unit square.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum.StrictSquare.SplitEvaluation
variable {S : Arrow (Arrow LoopPrespectrum.{u})} {R : SplitSquare.{u}}
  (i : SplitEvaluation S R)
  (U : Homotopy (S.left.hom ≫ S.hom.right) (S.left.hom ≫ S.hom.right))
  (V : Homotopy R.l R.l)
  (JU : ((U.postcomp i.c).trans i.T).RelHomotopy
    (i.T.trans (Homotopy.precomp i.a V)))

/-- The original strict forward seed uses the full undelayed source-null cylinder. -/
def sourceSeed : S.left.left ⟶ strictSquareLoopedConeFunctor.obj S :=
  (U.postcomp (mappingConeInclusion (StrictSquare.comparison S))).nullLoopMap
    (StrictSquare.sourceNullHomotopy S)

namespace Seed

/-- The original strict unit evaluated into the split target cone. -/
def oldUnit := (U.postcomp i.c).postcomp (mappingConeInclusion R.comparison)

/-- Original source evaluation followed by the split target unit. -/
def newUnit := (Homotopy.precomp i.a V).postcomp (mappingConeInclusion R.comparison)

/-- The actual unit square retains its entire cone-image track. -/
def unitPasting :
    ((oldUnit i U).trans (Null.diagonalMovement i)).RelHomotopy
      ((Null.diagonalMovement i).trans (newUnit i V)) := by
  simpa only [Homotopy.postcomp_trans, oldUnit, newUnit, Null.diagonalMovement] using
    JU.postcomp (mappingConeInclusion R.comparison)

/-- The whole specified source-null and unit squares compare both complete based conjugates. -/
def conjugation :=
  Homotopy.RelHomotopy.conjugateNaturality (Null.diagonalMovement i)
    (oldUnit i U) (newUnit i V) (Null.originalOldNull i) (Null.originalNewNull i)
    (unitPasting i U V JU) (Null.originalNullComparison i)

/-- The first conjugate is the original strict seed followed by actual cone-loop evaluation. -/
theorem source_eq :
    (oldUnit i U).nullLoopMap (Null.originalOldNull i) = sourceSeed U ≫ map i := by
  have h := Homotopy.nullLoopMap_naturality (𝟙 S.left.left) (coneMap i)
    (U.postcomp (mappingConeInclusion (StrictSquare.comparison S))) (oldUnit i U)
    (StrictSquare.sourceNullHomotopy S) (Null.originalOldNull i)
    (by intro n; rfl) (by intro n; rfl)
  exact h.symm

/-- The second conjugate is original source evaluation followed by the split target seed. -/
theorem target_eq :
    (newUnit i V).nullLoopMap (Null.originalNewNull i) = i.a ≫ R.transition V := by
  exact Homotopy.nullLoopMap_naturality i.a (𝟙 (mappingCone R.comparison))
    (newUnit i V) (V.postcomp (mappingConeInclusion R.comparison))
    (Null.originalNewNull i) R.sourceNull (by intro n; rfl) (by intro n; rfl)

end Seed

/-- Actual evaluation intertwines the two original specified forward seeds. -/
def seedHomotopy : Homotopy (sourceSeed U ≫ map i) (i.a ≫ R.transition V) :=
  (Seed.conjugation i U V JU).zeroLoopMapHomotopy.cast
    (Seed.source_eq i U) (Seed.target_eq i V)

/-- The comparison and output-loop coordinates retain the entire original conjugation. -/
theorem seedHomotopy_apply (n : ℕ) (r s : unitInterval) (x : S.left.left.space n) :
    Path.toContinuousMap ((seedHomotopy i U V JU).level n (r, x)) s =
      (Seed.conjugation i U V JU).level n (r, (s, x)) := rfl

end Quillen.LoopPrespectrum.StrictSquare.SplitEvaluation
