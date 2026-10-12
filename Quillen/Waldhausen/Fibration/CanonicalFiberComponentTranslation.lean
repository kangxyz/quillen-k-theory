/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.Fibration.CanonicalFiberObjectPrefixTransport
public import Quillen.Topology.HomotopyFiber.SquareEquivalence
public import Quillen.Topology.HomotopyFiber.PointComparison

/-!
# The prescribed canonical-fiber component translation

The original strict left-concatenation square consists of genuine homotopy equivalences.
Its existing fiber equivalence followed by the actual identity-cofiber suffix therefore
supplies a genuine equivalence with the previously constructed canonical-fiber translation
as its literal value. Both the original source loop and entire reversed fiber path survive.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v
namespace Quillen.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (A : C)

/-- The original object-loop prefixes commute with the unchanged localization loop map. -/
theorem canonicalFiberPrefix_square :
    (loopLeftTranslationEquiv (N.coarse.kZeroObjectLoop A)).toFun.comp
        (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N)) =
      (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N)).comp
        (loopLeftTranslationEquiv (V.kZeroObjectLoop A)).toFun := by
  have hA : basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N)
      (V.kZeroObjectLoop A) = N.coarse.kZeroObjectLoop A :=
    deloopingMap_kZeroObjectLoop (changeWeak_exact N) N.zero_eq.symm A
  have hs := loopLeftTranslationEquiv_naturality
    (changeWeakMap N) (changeWeakMap_basepoint N) (V.kZeroObjectLoop A)
  rw [hA] at hs
  exact hs.symm

/-- The actual prefix map is a genuine equivalence on the original localization loop fibers. -/
def canonicalFiberPrefixEquiv :
    ContinuousMap.HomotopyEquiv
      (HomotopyFiber (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
        (Path.refl N.coarse.kBasepoint))
      (HomotopyFiber (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
        ((N.coarse.kZeroObjectLoop A).trans (Path.refl N.coarse.kBasepoint))) :=
  (HomotopyFiber.mapHomotopyEquivOfEquivalences
    (loopLeftTranslationEquiv (V.kZeroObjectLoop A))
    (loopLeftTranslationEquiv (N.coarse.kZeroObjectLoop A))
    (canonicalFiberPrefix_square N A) (Path.refl N.coarse.kBasepoint)).trans
      (HomotopyFiber.basepointEqHomeomorph
        (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
        (loopLeftTranslationEquiv_apply (N.coarse.kZeroObjectLoop A)
          (Path.refl N.coarse.kBasepoint))).toHomotopyEquiv

/-- Its forward map on the original transposed object loop is exactly the previously defined point.
-/
theorem canonicalFiberPrefixEquiv_object (X : AcyclicCategory N) :
    canonicalFiberPrefixEquiv N A (canonicalFiberObjectLoopTranspose N X) =
      canonicalFiberObjectPrefixed N A X := by
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · change loopLeftTranslationEquiv (V.kZeroObjectLoop A)
      (canonicalFiberObjectLoopTranspose N X).val.1 = _
    rw [canonicalFiberObjectLoopTranspose_source, loopLeftTranslationEquiv_apply]
    rfl
  · rfl

variable [HasZeroMorphisms C]

/-- The entire prescribed prefix and identity-triangle transport is a genuine fiber equivalence. -/
def canonicalFiberComponentEquiv :
    ContinuousMap.HomotopyEquiv
      (HomotopyFiber (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
        (Path.refl N.coarse.kBasepoint))
      (HomotopyFiber (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
        (N.coarse.kZeroObjectLoop A)) :=
  (canonicalFiberPrefixEquiv N A).trans
    (HomotopyFiber.basepointTransportEquiv
      (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
      (N.coarse.identityCofiberSuffixPath A))

/-- The original canonical-fiber point retains its exact prescribed full translation. -/
theorem canonicalFiberComponentEquiv_object (X : AcyclicCategory N) :
    canonicalFiberComponentEquiv N A (canonicalFiberObjectLoopTranspose N X) =
      canonicalFiberObjectPrefixTransport N A X := by
  change HomotopyFiber.basepointTransportEquiv _ _
    (canonicalFiberPrefixEquiv N A (canonicalFiberObjectLoopTranspose N X)) = _
  rw [canonicalFiberPrefixEquiv_object]
  rfl

end Quillen.Waldhausen.Fibration
