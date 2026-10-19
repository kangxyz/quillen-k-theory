/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.SuspensionLoopCounitStable

/-!
# The actual suspension-loop unit and its evaluation triangle

The original cone cylinder is used in its forward zero-to-zero orientation. It supplies the
actual unit into parameter loops, naturally in every spectrum. The unit at parameter loops
followed by the parameter-looped evaluation counit is strictly the identity at every time.
Consequently stability of the counit proves stability of this particular unit, with no general
Freudenthal assertion or replacement of the spectrum by an Omega spectrum.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum

/-- The original forward cone contraction, with both endpoints the actual zero map. -/
def suspensionCylinderHomotopy (E : LoopPrespectrum.{u}) :
    Homotopy (zeroHom E (suspensionCone E)) (zeroHom E (suspensionCone E)) :=
  mappingConeHomotopy (zeroHom E pointPrespectrum)

/-- The suspension-loop unit retains the original cone time in its forward order. -/
def suspensionLoopUnit (E : LoopPrespectrum.{u}) : E ⟶ parameterLooping (suspensionCone E) :=
  (suspensionCylinderHomotopy E).zeroLoopMap

/-- Every value of the actual unit is the original cone-cylinder point. -/
theorem suspensionLoopUnit_apply (E : LoopPrespectrum.{u}) (n : ℕ)
    (x : E.space n) (s : unitInterval) :
    Path.toContinuousMap ((suspensionLoopUnit E).map n x) s =
      ReducedMappingCone.cylinder (E.point n) (pointPrespectrum.point n)
        ((zeroHom E pointPrespectrum).map n) (s, x) := rfl

/-- The entire actual unit commutes with genuine prespectrum maps. -/
theorem suspensionLoopUnit_naturality {E F : LoopPrespectrum.{u}} (f : E ⟶ F) :
    f ≫ suspensionLoopUnit F =
      suspensionLoopUnit E ≫ parameterLoopingMap (suspensionConeMap f) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext s
  rfl

/-- The triangle evaluates at the same original loop time, without reversal or transpose. -/
theorem suspensionLoopUnit_counit (E : LoopPrespectrum.{u}) :
    suspensionLoopUnit (parameterLooping E) ≫
      parameterLoopingMap (suspensionLoopCounit E) = 𝟙 (parameterLooping E) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro γ
  apply Path.ext
  funext s
  rfl

/-- Stability of the actual counit implies stability of the unit at parameter loops. -/
theorem suspensionLoopUnit_parameterLooping_isStableEquivalence
    (E : LoopPrespectrum.{u}) (hE : IsStableEquivalence (suspensionLoopCounit E)) :
    IsStableEquivalence (suspensionLoopUnit (parameterLooping E)) := by
  intro d
  let :=  parameterLooping_suspensionLoopCounit_isStableEquivalence E hE d
  have h := congrArg ((stableHomotopyFunctor d).map) (suspensionLoopUnit_counit E)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at h
  rw [IsIso.eq_inv_of_inv_hom_id h]
  infer_instance

end Quillen.LoopPrespectrum
