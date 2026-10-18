/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Automorphism.Naturality
public import Quillen.Topology.HomotopyGroups.CoordinateTransposition

/-!
# The two literal coordinates of the capped Q automorphism cube

Transposing the Q-path coordinate and the automorphism/cap coordinate gives
an actual cube representing the inverse Q automorphism class. Exact-functor
naturality retains the original K-map. This is the literal general cube used
by R5 at revision `1b7c3945394bcc27a94d1ebf86df702b0291ee18`.
No equality with the native stable-completion comparison is claimed.
-/
@[expose] public section
open CategoryTheory.ExactCategory (ExactFunctor ExactStructure)

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Quillen
open Quillen.Automorphism
open Quillen.Automorphism.Cap
open scoped Topology unitInterval

namespace Quillen.Automorphism.Cube

variable {C : Type u} [SmallCategory C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (A : C) (g : Aut A)

/-- The literal cube already used by the current class, with Q path first. -/
def qPathFirstCube : GenLoop (Fin 2) (ClassifyingSpace E.QCategory) E.kBasepoint :=
  loopUncurry ((genLoopEquivOfUnique (Fin 1)).symm
    (cappedLoop (coreLoopMap E (classifyingSpacePoint (Core.mk A)))
      (automorphismCylinder E g)))

theorem qPathFirstCube_class :
    (Quotient.mk' (qPathFirstCube E A g) : E.K 1) = automorphismClass E A g := by
  exact (componentToPiTwo_eq_cube
    (coreLoopMap E (classifyingSpacePoint (Core.mk A)))
    (automorphismCylinder E g)).symm

/-- The same capped cube with automorphism/cap time before Q-path time. -/
def automorphismFirstCube :
    GenLoop (Fin 2) (ClassifyingSpace E.QCategory) E.kBasepoint :=
  transposeGenLoop (0 : Fin 2) 1 Fin.zero_ne_one (qPathFirstCube E A g)

theorem automorphismFirstCube_class :
    (Quotient.mk' (automorphismFirstCube E A g) : E.K 1) =
      (automorphismClass E A g)⁻¹ := by
  rw [automorphismFirstCube, transposeGenLoop_class, qPathFirstCube_class]

/-- This is an actual coordinate swap, not a renamed inverse group element. -/
theorem automorphismFirstCube_apply (z : Fin 2 → unitInterval) :
    automorphismFirstCube E A g z =
      cappedLoop (coreLoopMap E (classifyingSpacePoint (Core.mk A)))
        (automorphismCylinder E g) (z 0) (z 1) := by
  change cappedLoop (coreLoopMap E (classifyingSpacePoint (Core.mk A)))
      (automorphismCylinder E g)
      ((cubeCoordinateSwap (0 : Fin 2) 1 z) 1)
      ((cubeCoordinateSwap (0 : Fin 2) 1 z) 0) = _
  simp [cubeCoordinateSwap]

end Quillen.Automorphism.Cube

namespace Quillen.Automorphism.Cube
open Quillen.Automorphism.Functoriality

/-- The concrete transposed representative is natural for the same actual
exact-functor K maps; no new field comparison is chosen. -/
theorem transposedCube_KMap
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    [Preadditive C] [HasFiniteBiproducts C]
    [Preadditive D] [HasFiniteBiproducts D]
    {EC : ExactStructure C} {ED : ExactStructure D}
    (F : ExactFunctor EC ED) (A : C) (g : Aut A) :
    F.KMap 1 (Quotient.mk' (automorphismFirstCube EC A g)) =
      Quotient.mk' (automorphismFirstCube ED (F.toFunctor.obj A)
        (F.toFunctor.mapIso g)) := by
  rw [automorphismFirstCube_class, map_inv, automorphismClass_natural]
  exact (automorphismFirstCube_class _ _ _).symm

end Quillen.Automorphism.Cube
