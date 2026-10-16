/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Limits.Shapes.SequentialSystem.SignCorrection
public import Quillen.Topology.Prespectrum.SelfTrackSuccessorSign
public import Quillen.Topology.Prespectrum.StableShift

/-!
# The integer-graded stable operation of an original self-track

The actual finite homomorphisms, in input degree at least two, have the proved
anti-commuting successor squares. Their alternating signs therefore descend
to the original sequential colimits. The target is identified with degree
one higher by the existing exact level/degree reindexing and final-tail map.
No Omega-spectrum or eventual-stability premise is used.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum
variable {E F : LoopPrespectrum.{u}} {f : E ⟶ F}

/-- The original finite operation at the unchanged actual stable stage. -/
def Homotopy.stableStageOperation (H : Homotopy f f) (d : ℤ) (n : ℕ) :
    (stableSystem E d).obj n ⟶ (shiftedStableSystem F d).obj n :=
  AddCommGrpCat.ofHom
    (H.homotopyClassOperationHom ((-d).toNat + n + 2) (d.toNat + n)).toAdditive

/-- The actual original stage operations anti-commute with the actual successor maps. -/
theorem Homotopy.stableStageOperation_anticomm (H : Homotopy f f) (d : ℤ) (n : ℕ) :
    (stableSystem E d).map (homOfLE (Nat.le_succ n)) ≫
        H.stableStageOperation d (n + 1) =
      -(H.stableStageOperation d n ≫
        (shiftedStableSystem F d).map (homOfLE (Nat.le_succ n))) := by
  simp only [stableSystem, shiftedStableSystem, Functor.comp_map,
    Functor.ofSequence_map_homOfLE_succ]
  apply AddCommGrpCat.ext
  intro a
  exact congrArg Additive.ofMul
    (H.homotopyClassOperation_structure_sign ((-d).toNat + n + 2) (d.toNat + n)
      (Additive.toMul a))

/-- Alternating the original stage operations gives a genuine natural transformation. -/
def Homotopy.stableShiftedSystemOperation (H : Homotopy f f) (d : ℤ) :
    stableSystem E d ⟶ shiftedStableSystem F d :=
  CategoryTheory.Limits.SequentialSystem.signCorrectionHom (H.stableStageOperation d)
    (H.stableStageOperation_anticomm d)

/-- The actual operation descends to the colimit of the unchanged shifted target diagram. -/
def Homotopy.stableShiftedOperation (H : Homotopy f f) (d : ℤ) :
    stableHomotopyGroup E d ⟶ colimit (shiftedStableSystem F d) :=
  colimMap (H.stableShiftedSystemOperation d)

/-- The integer-graded operation uses the proved original degree/level and tail identifications. -/
def Homotopy.stableOperation (H : Homotopy f f) (d : ℤ) :
    stableHomotopyGroup E d ⟶ stableHomotopyGroup F (d + 1) :=
  H.stableShiftedOperation d ≫
    (HasColimit.isoOfNatIso (shiftedStableSystemIso F d)).hom ≫
      (CategoryTheory.Limits.SequentialSystem.tailColimitIso (stableSystem F (d + 1))
        (parameterStableOffset d)).hom

/-- Before reindexing, the colimit map retains its exact alternating original stage map. -/
@[reassoc] theorem Homotopy.stableShiftedOperation_ι (H : Homotopy f f) (d : ℤ) (n : ℕ) :
    stableHomotopyι E d n ≫ H.stableShiftedOperation d =
      ((-1 : ℤ) ^ n • H.stableStageOperation d n) ≫
        colimit.ι (shiftedStableSystem F d) n := by
  exact ι_colimMap (H.stableShiftedSystemOperation d) n

/-- The final operation retains the exact original stage leg, sign, and integer tail offset. -/
@[reassoc] theorem Homotopy.stableOperation_ι (H : Homotopy f f) (d : ℤ) (n : ℕ) :
    stableHomotopyι E d n ≫ H.stableOperation d =
      ((-1 : ℤ) ^ n • H.stableStageOperation d n) ≫
        (shiftedStableReindexIso F d n).hom ≫
          stableHomotopyι F (d + 1) (parameterStableOffset d + n) := by
  simp [Homotopy.stableOperation, Homotopy.stableShiftedOperation, stableHomotopyι,
    Homotopy.stableShiftedSystemOperation, shiftedStableSystemIso]

end Quillen.LoopPrespectrum
