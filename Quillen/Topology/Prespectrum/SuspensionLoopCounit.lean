/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.Point
public import Quillen.Topology.Prespectrum.MappingCone
public import Quillen.Topology.Prespectrum.FiberSequence

/-!
# The actual suspension-cone counit for parameter loops

The reduced suspension carrier is the original cone of the map to the literal point spectrum.
Evaluation of a parameter loop gives an entire coherent zero homotopy and hence a genuine map
from the suspension of parameter loops to the original spectrum. Its fiber lift is the literal
point-to-spectrum fiber isomorphism. The loop and structure coordinates remain independent.
This module makes no claim that the counit is stable for an arbitrary spectrum.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum

/-- The actual reduced suspension carrier, using the original point and mapping cone. -/
def suspensionCone (E : LoopPrespectrum.{u}) : LoopPrespectrum.{u} :=
  mappingCone (zeroHom E pointPrespectrum)

/-- An actual map induces the original strict map of reduced suspension cones. -/
def suspensionConeMap {E F : LoopPrespectrum.{u}} (f : E ⟶ F) :
    suspensionCone E ⟶ suspensionCone F :=
  mappingConeMap (A := Arrow.mk (zeroHom E pointPrespectrum))
    (B := Arrow.mk (zeroHom F pointPrespectrum))
    (Arrow.homMk f (𝟙 pointPrespectrum) (by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    rfl))

/-- Evaluation of a based parameter loop is a coherent zero homotopy, including structure time. -/
def loopEvaluationHomotopy (E : LoopPrespectrum.{u}) :
    Homotopy (zeroHom (parameterLooping E) pointPrespectrum ≫ zeroHom pointPrespectrum E)
      (zeroHom (parameterLooping E) E) where
  level n := ⟨fun z ↦ Path.toContinuousMap z.2 z.1, by fun_prop⟩
  at_zero _n γ := γ.source
  at_one _n γ := γ.target
  at_point _n _s := rfl
  comm _n _s _γ _t := rfl

/-- The actual counit evaluates the original suspension cylinder on the original loop. -/
def suspensionLoopCounit (E : LoopPrespectrum.{u}) :
    suspensionCone (parameterLooping E) ⟶ E :=
  mappingConeDesc (zeroHom (parameterLooping E) pointPrespectrum)
    (zeroHom pointPrespectrum E) (loopEvaluationHomotopy E)

/-- No reparameterization is inserted in the independent suspension and loop coordinates. -/
theorem suspensionLoopCounit_cylinder (E : LoopPrespectrum.{u}) (n : ℕ)
    (s : unitInterval) (γ : (parameterLooping E).space n) :
    (suspensionLoopCounit E).map n
      (ReducedMappingCone.cylinder ((parameterLooping E).point n) (pointPrespectrum.point n)
        ((zeroHom (parameterLooping E) pointPrespectrum).map n) (s, γ)) =
        Path.toContinuousMap γ s := rfl

/-- The point summand maps to the original chosen point. -/
theorem suspensionLoopCounit_point (E : LoopPrespectrum.{u}) (n : ℕ)
    (x : pointPrespectrum.{u}.space n) :
    (suspensionLoopCounit E).map n
      (ReducedMappingCone.inr ((parameterLooping E).point n) (pointPrespectrum.point n)
        ((zeroHom (parameterLooping E) pointPrespectrum).map n) x) = E.point n := rfl

/-- The actual counit commutes with every genuine spectrum map. -/
theorem suspensionLoopCounit_naturality {E F : LoopPrespectrum.{u}} (f : E ⟶ F) :
    suspensionConeMap (parameterLoopingMap f) ≫ suspensionLoopCounit F =
      suspensionLoopCounit E ≫ f := by
  apply Hom.ext
  funext n
  apply ReducedMappingCone.hom_ext
  · intro x
    exact (f.map_point n).symm
  · intro z
    rfl

/-- Retain the whole fiber path of the literal point-to-spectrum map as a based loop. -/
def pointFiberInverse (E : LoopPrespectrum.{u}) :
    homotopyFiber (zeroHom pointPrespectrum E) ⟶ parameterLooping E where
  map n := {
    toFun z := {
      toFun := z.1.2
      continuous_toFun := z.1.2.continuous
      source' := z.2.1
      target' := z.2.2 }
    continuous_toFun := by
      apply Path.continuous_uncurry_iff.mp
      change Continuous (fun z :
        (homotopyFiber (zeroHom pointPrespectrum E)).space n × unitInterval ↦ z.1.1.2 z.2)
      fun_prop }
  map_point _n := by apply Path.ext; funext s; rfl
  comm _n _γ := by apply Path.ext; funext t; apply Path.ext; funext s; rfl

/-- The original loop-to-fiber inclusion is an isomorphism for the actual point source. -/
def pointFiberIso (E : LoopPrespectrum.{u}) :
    parameterLooping E ≅ homotopyFiber (zeroHom pointPrespectrum E) where
  hom := homotopyFiberLoopInclusion (zeroHom pointPrespectrum E)
  inv := pointFiberInverse E
  hom_inv_id := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro γ
    apply Path.ext
    funext s
    rfl
  inv_hom_id := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    apply Prod.ext
    · change (PUnit.unit : PUnit.{u+1}) = _
      exact Subsingleton.elim _ _
    · apply ContinuousMap.ext
      intro s
      rfl

/-- The specified counit's whole-null fiber lift is exactly the original point-fiber map. -/
theorem loopEvaluationHomotopy_fiberLift (E : LoopPrespectrum.{u}) :
    homotopyFiberLift (zeroHom pointPrespectrum E) (zeroHom (parameterLooping E) pointPrespectrum)
      (loopEvaluationHomotopy E) = (pointFiberIso E).hom := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro γ
  apply Subtype.ext
  rfl

end Quillen.LoopPrespectrum
