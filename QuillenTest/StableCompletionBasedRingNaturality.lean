/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Plus.StableCompletionBasedRingNaturality
public import Mathlib.Data.ZMod.Basic

/-!
# Consumers for the original based stable change-of-rings square

These examples retain the prescribed inverse and completion-unit tracks in all
finite degrees, the exact fundamental-group homomorphisms, and an actual map to
the zero ring. The cross-universe vertex-track theorem is tested independently.
-/

@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.FiniteProjectiveModule
open Quillen.FiniteProjectiveModule.StableCompletion
universe u v u' v'
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal rightBaseChangeMonoidal

example {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F G : C ⥤ D} (α : F ⟶ G) (c : C) (t : unitInterval) :
    classifyingSpaceUniversalHomotopy α (t, classifyingSpacePoint c) =
      classifyingSpacePath (α.app c) t :=
  classifyingSpaceUniversalHomotopy_vertex_track α c t

example {R S : Type u} [Ring R] [Ring S] (f : R →+* S) (n : ℕ)
    (a : HomotopyGroup.Pi n (ClassifyingSpace (SingleObj (StableGeneralLinear.Group R)))
      (stableBase R)) :
    pathTransport (zeroCompletionBaseChangeBasepointPath f) n
      (homotopyGroupMap (zeroCompletionBaseChangeMap f) rfl
        (pathTransport (basepointPath R) n (homotopyGroupMap (stableZeroMap R) rfl a))) =
      pathTransport (basepointPath S) n
        (homotopyGroupMap (stableZeroMap S) rfl
          (homotopyGroupMap (classifyingSpaceMap (StableGeneralLinear.map f).toFunctor).hom
            (stableRingMap_point f) a)) :=
  stableZeroMap_homotopyGroupMap_ringMap f n a

example {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    ((pathTransportMulEquiv (zeroCompletionBaseChangeBasepointPath f) 0).toMonoidHom.comp
      (piMap 0 (zeroCompletionBaseChangeMap f) (x := zeroBase R) rfl)).comp
        (stablePiOneMap R) =
      (stablePiOneMap S).comp
        (piMap 0 (classifyingSpaceMap (StableGeneralLinear.map f).toFunctor).hom
          (stableRingMap_point f)) :=
  stablePiOneMap_ringMap f

example (n : ℕ)
    (a : HomotopyGroup.Pi n (ClassifyingSpace (SingleObj (StableGeneralLinear.Group ℤ)))
      (stableBase ℤ)) :
    pathTransport (zeroCompletionBaseChangeBasepointPath (Int.castRingHom (ZMod 1))) n
      (homotopyGroupMap (zeroCompletionBaseChangeMap (Int.castRingHom (ZMod 1))) rfl
        (pathTransport (basepointPath ℤ) n (homotopyGroupMap (stableZeroMap ℤ) rfl a))) =
      pathTransport (basepointPath (ZMod 1)) n
        (homotopyGroupMap (stableZeroMap (ZMod 1)) rfl
          (homotopyGroupMap (classifyingSpaceMap
            (StableGeneralLinear.map (Int.castRingHom (ZMod 1))).toFunctor).hom
              (stableRingMap_point _) a)) :=
  stableZeroMap_homotopyGroupMap_ringMap _ n a

example {R : Type u} [Ring R] (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n) (originalTelescopeProjection R)
      (originalTelescopeProjection_point R)) :=
  originalTelescopeProjection_homotopyGroupMap_bijective R n

example {R S : Type u} [Ring R] [Ring S] (f : R →+* S) (t : unitInterval) :
    telescopeZeroBaseChangeHomotopy f (t, classifyingSpacePoint (telescopeBase R)) =
      zeroCompletionBaseChangeBasepointPath f t :=
  telescopeZeroBaseChangeHomotopy_track f t
