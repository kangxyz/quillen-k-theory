/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.Prespectrum.ParameterLooping
public import Quillen.Topology.Prespectrum.MappingCone

/-!
Original coherent homotopy reversal, concatenation and conjugation produce actual loop-valued maps
and cone transitions.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum
variable {E F G : LoopPrespectrum.{u}}

/-- Reverse the actual homotopy time, preserving the original structure coordinate. -/
def Homotopy.symm {f g : E ⟶ F} (H : Homotopy f g) : Homotopy g f where
  level n := (H.levelHomotopy n).symm.toContinuousMap
  at_zero n x := (H.levelHomotopy n).symm.apply_zero x
  at_one n x := (H.levelHomotopy n).symm.apply_one x
  at_point n s := H.at_point n (unitInterval.symm s)
  comm n s x t := H.comm n (unitInterval.symm s) x t

/-- Concatenate whole structure-compatible homotopies using the actual interval halves. -/
def Homotopy.trans {f g h : E ⟶ F} (H : Homotopy f g) (K : Homotopy g h) : Homotopy f h where
  level n := ((H.levelHomotopy n).trans (K.levelHomotopy n)).toContinuousMap
  at_zero n x := ((H.levelHomotopy n).trans (K.levelHomotopy n)).apply_zero x
  at_one n x := ((H.levelHomotopy n).trans (K.levelHomotopy n)).apply_one x
  at_point n s := by
    change ((H.levelHomotopy n).trans (K.levelHomotopy n)) (s,E.point n) = _
    rw [ContinuousMap.HomotopyRel.trans_apply]
    split
    · exact H.at_point _ _
    · exact K.at_point _ _
  comm n s x t := by
    change ((H.levelHomotopy (n+1)).trans (K.levelHomotopy (n+1))) (s,E.structureMap n x t) =
      F.structureMap n (((H.levelHomotopy n).trans (K.levelHomotopy n)) (s,x)) t
    rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
    split
    · exact H.comm _ _ _ _
    · exact K.comm _ _ _ _

/-- Conjugate a genuine self-homotopy by the supplied original nullhomotopy. -/
def Homotopy.conjugateToZero {f : E ⟶ F} (H : Homotopy f f)
    (N : Homotopy f (zeroHom E F)) : Homotopy (zeroHom E F) (zeroHom E F) :=
  N.symm.trans (H.trans N)

/-- The actual loop map at the zero point, with the necessary parameter interchange explicit. -/
def Homotopy.nullLoopMap {f : E ⟶ F} (H : Homotopy f f)
    (N : Homotopy f (zeroHom E F)) : E ⟶ parameterLooping F :=
  (H.conjugateToZero N).zeroLoopMap

/-- The cone nullhomotopy transports a self-homotopy of the original comparison to a based loop. -/
def mappingConeLoopTransition (f : E ⟶ F) (H : Homotopy f f) : E ⟶ parameterLooping (mappingCone f)
  :=
  (H.postcomp (mappingConeInclusion f)).nullLoopMap (mappingConeHomotopy f)

/-- The entire original loop remains the explicitly concatenated homotopy. -/
theorem mappingConeLoopTransition_apply (f : E ⟶ F) (H : Homotopy f f)
    (n : ℕ) (x : E.space n) (s : unitInterval) :
    Path.toContinuousMap ((mappingConeLoopTransition f H).map n x) s =
      ((H.postcomp (mappingConeInclusion f)).conjugateToZero (mappingConeHomotopy f)).level n (s,x)
        := rfl

/--
A self-homotopy along a specified original source leg yields the concrete cone-loop transition.
-/
def mappingConeLoopTransitionAlong (f : E ⟶ F) (a : G ⟶ E)
    (H : Homotopy (a ≫ f) (a ≫ f)) : G ⟶ parameterLooping (mappingCone f) :=
  (H.postcomp (mappingConeInclusion f)).nullLoopMap
    (Homotopy.precomp a (mappingConeHomotopy f))

end Quillen.LoopPrespectrum
