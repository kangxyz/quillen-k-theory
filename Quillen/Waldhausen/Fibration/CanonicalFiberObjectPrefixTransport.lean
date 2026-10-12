/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.Fibration.CofiberPrismLeftPrefix
public import Quillen.Waldhausen.Fibration.IdentityCofiberComponent

/-!
# The original canonical-fiber point under its prescribed prefix and suffix

The original loop/fiber transpose is prefixed by the displayed object loop, then transported
along the actual identity-cofiber triangle. The whole stored fiber path is retained. In
particular, its first part still has the reversed original canonical-fiber coordinate. This
is the concrete input to the existing iterated-fiber loop formula; no boundary sign is assigned.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval
universe u v
namespace Quillen.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C]
  {V : Structure C} (N : NestedWeakEquivalences V) (A : C) (X : AcyclicCategory N)

/-- Prefix the actual transposed canonical-fiber point by the original source object loop. -/
def canonicalFiberObjectPrefixed :
    HomotopyFiber (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
      ((N.coarse.kZeroObjectLoop A).trans (Path.refl N.coarse.kBasepoint)) := by
  refine ⟨((V.kZeroObjectLoop A).trans (V.kZeroObjectLoop X.obj),
    (loopLeftTranslationEquiv (N.coarse.kZeroObjectLoop A)).toFun.comp
      (canonicalFiberObjectLoopTranspose N X).val.2), ?_, ?_⟩
  · change loopLeftTranslationEquiv (N.coarse.kZeroObjectLoop A)
      ((canonicalFiberObjectLoopTranspose N X).val.2 0) = _
    rw [(canonicalFiberObjectLoopTranspose N X).property.1,
      canonicalFiberObjectLoopTranspose_source, loopLeftTranslationEquiv_apply,
      basedLoopMap_trans]
    have hA : basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N)
        (V.kZeroObjectLoop A) = N.coarse.kZeroObjectLoop A :=
      deloopingMap_kZeroObjectLoop (changeWeak_exact N) N.zero_eq.symm A
    rw [hA]
  · change loopLeftTranslationEquiv (N.coarse.kZeroObjectLoop A)
      ((canonicalFiberObjectLoopTranspose N X).val.2 1) = _
    rw [canonicalFiberObjectLoopTranspose_one, loopLeftTranslationEquiv_apply]

/-- The prescribed prefix leaves the fine object coordinate as literal concatenation. -/
theorem canonicalFiberObjectPrefixed_source :
    (canonicalFiberObjectPrefixed N A X).val.1 =
      (V.kZeroObjectLoop A).trans (V.kZeroObjectLoop X.obj) := rfl

/-- The original reversed fiber coordinate remains inside the literal left prefix. -/
theorem canonicalFiberObjectPrefixed_path (s t : unitInterval) :
    (canonicalFiberObjectPrefixed N A X).val.2 s t =
      if h : (t : ℝ) ≤ 1 / 2 then
        N.coarse.kZeroObjectLoop A
          ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩
      else
        (canonicalFiberObjectLoop N X
          ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 h).le, t.2.2⟩⟩).val.2 s := by
  change loopLeftTranslationEquiv (N.coarse.kZeroObjectLoop A)
    ((canonicalFiberObjectLoopTranspose N X).val.2 s) t = _
  rw [loopLeftTranslationEquiv_apply, Path.trans_apply]
  split_ifs <;> rfl

variable [HasZeroMorphisms C]

/-- Transport uses exactly the original identity-cofiber suffix path. -/
def canonicalFiberObjectPrefixTransport :
    HomotopyFiber (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
      (N.coarse.kZeroObjectLoop A) :=
  HomotopyFiber.basepointTransportEquiv
    (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
    (N.coarse.identityCofiberSuffixPath A) (canonicalFiberObjectPrefixed N A X)

/-- Original suffix transport does not alter the prescribed fine source loop. -/
theorem canonicalFiberObjectPrefixTransport_source :
    (canonicalFiberObjectPrefixTransport N A X).val.1 =
      (V.kZeroObjectLoop A).trans (V.kZeroObjectLoop X.obj) := rfl

/-- The whole transported fiber path is the original prefixed path followed by the triangle. -/
theorem canonicalFiberObjectPrefixTransport_path :
    (canonicalFiberObjectPrefixTransport N A X).val.2 =
      ((HomotopyFiber.toPath
        (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
        ((N.coarse.kZeroObjectLoop A).trans (Path.refl N.coarse.kBasepoint))
        (canonicalFiberObjectPrefixed N A X)).trans
          (N.coarse.identityCofiberSuffixPath A)).toContinuousMap :=
  HomotopyFiber.basepointTransportEquiv_path _ _ _

end Quillen.Waldhausen.Fibration
