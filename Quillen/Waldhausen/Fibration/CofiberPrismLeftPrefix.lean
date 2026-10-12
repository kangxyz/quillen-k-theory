/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.Fibration.CofiberPrismFiber
public import Quillen.Topology.HomotopyFiber.Loop
public import Quillen.Topology.HomotopyGroups.Loop.LeftComponentTranslation

/-!
# The original canonical-fiber loop and its exact source prefix

The existing loop/fiber homeomorphism transposes the two original coordinates. Left translation
then gives exactly the source prefix in the cofiber prism, retaining the original reversed
canonical-fiber path. The component equivalence uses the prescribed suffix-removal path; no
arbitrary path between components or Laurent boundary identity is introduced.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits unitInterval
open scoped Topology
universe u v
namespace Quillen.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)

/-- Transpose the original canonical-fiber object loop using the existing exact homeomorphism. -/
def canonicalFiberObjectLoopTranspose (X : AcyclicCategory N) :
    HomotopyFiber (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
      (Path.refl N.coarse.kBasepoint) :=
  (HomotopyFiber.loopFiberHomeomorph (changeWeakMap N) (changeWeakMap_basepoint N)).symm
    (canonicalFiberObjectLoop N X)

/-- The original fine object loop is unchanged by this prescribed coordinate transpose. -/
theorem canonicalFiberObjectLoopTranspose_source (X : AcyclicCategory N) :
    (canonicalFiberObjectLoopTranspose N X).val.1 = V.kZeroObjectLoop X.obj := by
  ext t
  exact canonicalFiberObjectLoop_projection N X t

/-- The stored path retains both original loop and reversed canonical-fiber coordinates. -/
theorem canonicalFiberObjectLoopTranspose_path (X : AcyclicCategory N) (s t : unitInterval) :
    (canonicalFiberObjectLoopTranspose N X).val.2 s t =
      (canonicalFiberObjectLoop N X t).val.2 s := rfl

/-- The transposed target is exactly the actual constant loop. -/
theorem canonicalFiberObjectLoopTranspose_one (X : AcyclicCategory N) :
    (canonicalFiberObjectLoopTranspose N X).val.2 1 = Path.refl N.coarse.kBasepoint :=
  (canonicalFiberObjectLoopTranspose N X).property.2

section Cofiber
variable [HasZeroMorphisms C] {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)
  (hi : N.coarse.cof i) (hwi : N.coarse.weq i)
  (hQ : IsPushout i (0 : A ⟶ N.coarse.zero) q (0 : N.coarse.zero ⟶ Q))

/-- Left translation of the actual transposed fiber path is the literal cofiber-prism prefix. -/
theorem cofiberPrismCompositionCube_zero_leftPrefix (s t : unitInterval) :
    loopLeftTranslationEquiv (N.coarse.kZeroObjectLoop A)
        ((canonicalFiberObjectLoopTranspose N
          (cofiberPrismAcyclicQuotient N i q hi hwi hQ)).val.2 s)
        t =
      N.coarse.cofiberPrismCompositionCube i q hi hwi hQ (0, unitInterval.symm s, t) := by
  rw [loopLeftTranslationEquiv_apply, Path.trans_apply,
    cofiberPrismCompositionCube_zero_fiber N i q hi hwi hQ]
  split_ifs <;> rfl

end Cofiber
end Quillen.Waldhausen.Fibration
