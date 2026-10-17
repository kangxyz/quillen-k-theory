/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetConeReference
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeConeEvaluation
public import Quillen.Topology.Path.ScalarRectangleConcatenation

/-! The original two-half target action on the same unreduced ordinary cone and its original tip. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.TargetCone
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier FourEdgeTree
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
local notation "U" => normalizedMap (coefficientMap P f)
local notation "Ja" => normalizedMap (polynomialProjection P a)
local notation "Jb" => normalizedMap (polynomialProjection P b)
local notation "Eb" => E ≫ U
local notation "Fb" => WholeReference.reference P b Eb
local notation "βb" => beta P b Eb
local notation "T" => scalarCone P b Eb

/-- The original Laurent coefficient action followed by the target cone inclusion. -/
def laurentMap : C(|parameterSSet (WholeReference.reference P a E)|, T) :=
  (laurentInclusion Eb Jb Fb βb).comp (laurent P f E)

/-- The source cone tip maps to the one original target cone tip. -/
def tipMap : C(|tipSSet.{u + 1}|, T) := ContinuousMap.const _ (tip Eb Jb Fb βb)

/-- The exact common midpoint is the target attachment of the actual target span map. -/
def midpoint : C(FourEdgeTree.space E Ja, T) :=
  ⟨fun z ↦ laurentInclusion Eb Jb Fb βb
    (SSet.toTop.map βb (TargetSpan.treeMap P f E z)), by fun_prop⟩

/-- The first original half retains the entire H0 surface, including every full reference. -/
def firstHomotopy :
    ((laurentMap P f E).comp (SSet.toTop.map (beta P a E)).hom).Homotopy
      (midpoint P f E) where
  toContinuousMap := ⟨fun z ↦ laurentInclusion Eb Jb Fb βb (surface P f E (z.2, z.1)),
    by fun_prop⟩
  map_zero_left z := by
    change laurentInclusion Eb Jb Fb βb (surface P f E (z, 0)) = _
    rw [surface_zero]; rfl
  map_one_left z := by
    change laurentInclusion Eb Jb Fb βb (surface P f E (z, 1)) = _
    rw [surface_one]; rfl

/-- The second original half uses the actual target tree input at the unchanged cone height. -/
def secondHomotopy : (midpoint P f E).Homotopy
    ((tipMap P f E).comp (SSet.toTop.map
      (SSet.stdSimplex.isTerminalObj₀.from (FourEdgeTree.simplicial E Ja))).hom) where
  toContinuousMap := ⟨fun z ↦ cylinder Eb Jb Fb βb (TargetSpan.treeMap P f E z.2, z.1),
    by fun_prop⟩
  map_zero_left z := cone_cylinder_zero Eb Jb Fb βb _
  map_one_left z := cone_cylinder_one Eb Jb Fb βb _

/-- Literal first-half/second-half concatenation; there is no extra cone or extra tip. -/
def cylinderHomotopy := (firstHomotopy P f E).trans (secondHomotopy P f E)

/-- Descent through the original unreduced cone retains its entire Laurent baseline. -/
def coneMap : C(scalarCone P a E, T) :=
  DoubleCylinder.homotopyDesc _ _
    (DoubleCylinder.realized_isPushout (beta P a E) (SSet.stdSimplex.isTerminalObj₀.from _))
    (laurentMap P f E) (tipMap P f E) (cylinderHomotopy P f E)

/-- The whole Laurent inclusion carries the exact source coefficient action. -/
theorem coneMap_laurent (y : |parameterSSet (WholeReference.reference P a E)|) :
    coneMap P f E (laurentInclusion E Ja (WholeReference.reference P a E) (beta P a E) y) =
      laurentMap P f E y := by
  change coneMap P f E (SSet.toTop.map (FourEdgeTree.left _ _) y) = _
  rw [FourEdgeTree.left, SetDescent.eval_realized_left]
  exact congrArg (fun k ↦ k y)
    (DoubleCylinder.homotopyDesc_left _ _
      (DoubleCylinder.realized_isPushout (beta P a E) (SSet.stdSimplex.isTerminalObj₀.from _))
      (laurentMap P f E) (tipMap P f E) (cylinderHomotopy P f E))

/-- The original source tip maps to the original target tip. -/
theorem coneMap_tip :
    coneMap P f E (tip E Ja (WholeReference.reference P a E) (beta P a E)) =
      tip Eb Jb Fb βb := by
  change coneMap P f E (SSet.toTop.map (FourEdgeTree.right _ _) _) = _
  rw [FourEdgeTree.right, SetDescent.eval_realized_right]
  exact congrArg (fun k ↦ k (default : |tipSSet.{u + 1}|))
    (DoubleCylinder.homotopyDesc_right _ _
      (DoubleCylinder.realized_isPushout (beta P a E) (SSet.stdSimplex.isTerminalObj₀.from _))
      (laurentMap P f E) (tipMap P f E) (cylinderHomotopy P f E))

/-- The complete cone cylinder keeps the literal nested original concatenation. -/
theorem coneMap_cylinder (z : FourEdgeTree.space E Ja) (t : I) :
    coneMap P f E (cylinder E Ja (WholeReference.reference P a E) (beta P a E) (z, t)) =
      cylinderHomotopy P f E (t, z) :=
  DoubleCylinder.homotopyDesc_apply_cylinder _ _
    (DoubleCylinder.realized_isPushout (beta P a E) (SSet.stdSimplex.isTerminalObj₀.from _))
    (laurentMap P f E) (tipMap P f E) (cylinderHomotopy P f E) t z

/-- The first half has the original H0 surface at twice the source height. -/
theorem coneMap_lower (z : FourEdgeTree.space E Ja) (t : I) :
    coneMap P f E
      (cylinder E Ja (WholeReference.reference P a E) (beta P a E) (z, lower t)) =
    laurentInclusion Eb Jb Fb βb (surface P f E (z, t)) := by
  rw [coneMap_cylinder]
  exact ScalarRectangle.homotopy_lower (firstHomotopy P f E) (secondHomotopy P f E) t z

/-- The second half retains the original target cylinder at its unchanged rescaled height. -/
theorem coneMap_upper (z : FourEdgeTree.space E Ja) (t : I) :
    coneMap P f E
      (cylinder E Ja (WholeReference.reference P a E) (beta P a E) (z, upper t)) =
    cylinder Eb Jb Fb βb (TargetSpan.treeMap P f E z, t) := by
  rw [coneMap_cylinder]
  exact ScalarRectangle.homotopy_upper (firstHomotopy P f E) (secondHomotopy P f E) t z

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.TargetCone
