/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyFiber.GenLoopNormalizedReturn

/-! Whole original return, null, normalization and coordinate-zero consumers. -/
@[expose] public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open scoped Topology unitInterval
open Quillen Quillen.HomotopyFiber
universe u v
namespace QuillenTest.GenLoopNormalizedReturn
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) (y : Y) (x : X) (h : f x = y) (n : ℕ)
  {a d : GenLoop (Fin (n + 1)) X x} (R : Path a d)
  (lambda : Path (genLoopPostcomp f h d) (genLoopPostcomp f h a))
local notation "F" => genLoopPostcompContinuousMap (N := Fin (n + 1)) f h

/-- The actual fine return contains R.symm and the complete original cancellation. -/
theorem original_fine_return :
    genLoopPrefixReturn n R =
      (R.symm.map (GenLoopPrefix.inversePrefix n a).continuous).trans
        (GenLoopPrefix.cancellation n a) := rfl

/-- The actual source cast has the new fine image equal to the old coarse prefix. -/
theorem original_null_source_cast :
    genLoopPrefixNull f y x h n lambda =
      ((lambda.map (GenLoopPrefix.inversePrefix n (F a)).continuous).trans
        (GenLoopPrefix.cancellation n (F a))).cast
          (GenLoopPrefix.inversePrefix_map n f h a d) rfl := rfl

/-- The returned loop keeps the actual two-by-two concatenation word. -/
theorem original_returned_word :
    genLoopReturnedLoop f y x h n (GenLoopPrefix.inversePrefix n a d)
        (genLoopPrefixNull f y x h n lambda) (genLoopPrefixReturn n R) =
      ((GenLoopPrefix.cancellation n (F a)).symm.trans
        ((R.map (F).continuous).map
          (GenLoopPrefix.inversePrefix n (F a)).continuous)).trans
        ((lambda.map (GenLoopPrefix.inversePrefix n (F a)).continuous).trans
          (GenLoopPrefix.cancellation n (F a))) :=
  genLoopReturnedLoop_prefix f y x h n R lambda

/-- Both actual whole paths are connected by the displayed constructive associators. -/
def original_normalized_return_homotopy :
    (genLoopNormalizedSelfTrackPath n (F a) ((R.map (F).continuous).trans lambda)).Homotopy
      (genLoopReturnedLoop f y x h n (GenLoopPrefix.inversePrefix n a d)
        (genLoopPrefixNull f y x h n lambda) (genLoopPrefixReturn n R)) :=
  genLoopNormalizedReturnHomotopy f y x h n R lambda

/-- Every original normalized path time is retained on the initial face. -/
theorem original_initial_path (t : unitInterval) :
    genLoopNormalizedReturnHomotopy f y x h n R lambda (0, t) =
      genLoopNormalizedSelfTrackPath n (F a) ((R.map (F).continuous).trans lambda) t :=
  (genLoopNormalizedReturnHomotopy f y x h n R lambda).apply_zero t

/-- Every original returned-loop time is retained on the final face. -/
theorem original_final_path (t : unitInterval) :
    genLoopNormalizedReturnHomotopy f y x h n R lambda (1, t) =
      genLoopReturnedLoop f y x h n (GenLoopPrefix.inversePrefix n a d)
        (genLoopPrefixNull f y x h n lambda) (genLoopPrefixReturn n R) t :=
  (genLoopNormalizedReturnHomotopy f y x h n R lambda).apply_one t

/-- Both independent homotopy times keep the complete spatial boundary. -/
theorem original_whole_boundary (s t : unitInterval) (z : Fin (n + 1) → unitInterval)
    (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    genLoopNormalizedReturnHomotopy f y x h n R lambda (s, t) z = y :=
  genLoopNormalizedReturnHomotopy_boundary f y x h n R lambda s t z hz

/-- Coordinate-zero currying gives the same original whole relative fiber-loop comparison. -/
def original_curried_cube_homotopy :
    (loopCurry (genLoopNormalizedSelfTrackCube n (F a)
      ((R.map (F).continuous).trans lambda))).val.HomotopyRel
      (genLoopOfBasedPath (genLoopReturnedLoop f y x h n (GenLoopPrefix.inversePrefix n a d)
        (genLoopPrefixNull f y x h n lambda) (genLoopPrefixReturn n R))).val
      (Cube.boundary (Fin (n + 1))) :=
  (genLoopOfBasedPathHomotopy (genLoopNormalizedReturnHomotopy f y x h n R lambda)).cast
    (congrArg Subtype.val (loopCurry_genLoopNormalizedSelfTrackCube n (F a)
      ((R.map (F).continuous).trans lambda))).symm rfl

/-- Input degree one uses the same actual null and the same source return. -/
def original_degree_zero_homotopy {a0 d0 : GenLoop (Fin 1) X x} (R0 : Path a0 d0)
    (lambda0 : Path (genLoopPostcomp f h d0) (genLoopPostcomp f h a0)) :
    (genLoopNormalizedSelfTrackPath 0 (genLoopPostcomp f h a0)
      ((R0.map (genLoopPostcompContinuousMap f h).continuous).trans lambda0)).Homotopy
      (genLoopReturnedLoop f y x h 0 (GenLoopPrefix.inversePrefix 0 a0 d0)
        (genLoopPrefixNull f y x h 0 lambda0) (genLoopPrefixReturn 0 R0)) :=
  genLoopNormalizedReturnHomotopy f y x h 0 R0 lambda0

/-- The degree-zero input still fixes its entire boundary at both independent times. -/
theorem original_degree_zero_boundary {a0 d0 : GenLoop (Fin 1) X x} (R0 : Path a0 d0)
    (lambda0 : Path (genLoopPostcomp f h d0) (genLoopPostcomp f h a0))
    (s t : unitInterval) (z : Fin 1 → unitInterval) (hz : z ∈ Cube.boundary (Fin 1)) :
    genLoopNormalizedReturnHomotopy f y x h 0 R0 lambda0 (s, t) z = y :=
  genLoopNormalizedReturnHomotopy_boundary f y x h 0 R0 lambda0 s t z hz

end QuillenTest.GenLoopNormalizedReturn
