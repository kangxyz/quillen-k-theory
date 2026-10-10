/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.MappingCone
public import Quillen.Topology.Prespectrum.HomotopyPushout
public import Quillen.Topology.Prespectrum.Looping

/-! Concrete desuspended mapping-cone step for an actual homotopy-commuting square.
The geometric polynomial/Laurent square and unit action are not supplied by this owner;
there is no assumption or assertion of a fundamental theorem or negative K identification. -/
@[expose] public section

noncomputable section
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum
variable {A B C D : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C)
  (b : B ⟶ D) (c : C ⟶ D) (H : Homotopy (f ≫ b) (g ≫ c))

/-- The actual desuspended cone of the original double-cylinder comparison. -/
def desuspendedSquareCone : LoopPrespectrum.{u} :=
  looping (mappingCone (HomotopyPushout.desc f g b c H))

/-- The genuine looped boundary map on the original fourth corner. -/
def squareConeBoundary : looping D ⟶ desuspendedSquareCone f g b c H :=
  loopingMap (mappingConeInclusion (HomotopyPushout.desc f g b c H))

/-- Compose an actual displayed degree-raising arrow with the actual boundary.
In the Bass application the former must be constructed from the Laurent-unit action. -/
def squareConeTransition (u : A ⟶ looping D) : A ⟶ desuspendedSquareCone f g b c H :=
  u ≫ squareConeBoundary f g b c H

@[simp] theorem squareConeTransition_apply (u : A ⟶ looping D) (n : ℕ) (x : A.space n)
    (t : unitInterval) :
    Path.toContinuousMap ((squareConeTransition f g b c H u).map n x) t =
      ReducedMappingCone.inr
        ((HomotopyPushout.prespectrum f g).point n) (D.point n)
        ((HomotopyPushout.desc f g b c H).map n) (Path.toContinuousMap (u.map n x) t) := rfl

/-- The comparison-to-cone nullhomotopy is a full coherent prespectrum homotopy. -/
def squareConeNullHomotopy :
    Homotopy (HomotopyPushout.desc f g b c H ≫ mappingConeInclusion (HomotopyPushout.desc f g b
      c H))
      (zeroHom (HomotopyPushout.prespectrum f g) (mappingCone (HomotopyPushout.desc f g b c H))) :=
  mappingConeHomotopy (HomotopyPushout.desc f g b c H)

end Quillen.LoopPrespectrum
