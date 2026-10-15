/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyCofiber.UnreducedFirstObstruction
public import Quillen.Topology.HomotopyCofiber.UnreducedConeHomology
public import Quillen.Topology.LocalCoefficients.FirstObstruction
public import Quillen.Topology.HomotopyGroups.Connectivity.FiberObstructionStep

/-!
# The actual relative first obstruction detected by integral cone homology

The cone's lower homotopy groups vanish by the proved finite excision bridge.
Absolute first-obstruction detection then kills its next group; the literal
path-retaining cone comparison kills the corresponding original fiber group.
A constant-integral-chain quasi-isomorphism supplies the required cone homology
vanishing through the actual collar Mayer--Vietoris theorem.

The genuine frozen FirstObstruction theorem is applied directly; no
homology-to-homotopy certificate is introduced.
-/

@[expose] public section

open Quillen.LocalCoefficients

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits
universe u

namespace Quillen.ReducedMappingCone
open LocalCoefficients
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
variable [SimplyConnectedSpace X] [SimplyConnectedSpace Y]
variable (f : C(X, Y))

/-- Zero actual integral cone homology kills the first possible original
relative obstruction, including the fiber fundamental group at m=0. -/
theorem subsingleton_firstObstruction_of_cone_homology
    (x : X) (m : ℕ) (hf : IsHomotopyConnectedMap f (m + 1))
    (hH : IsZero (homology (constant (UnreducedSpace f) integralCoefficientModule.{u})
      (m + 2))) :
    Subsingleton (HomotopyGroup.Pi (m + 1) (HomotopyFiber f (f x))
      (HomotopyFiber.basepoint f (f x) x rfl)) := by
  let : PathConnectedSpace (UnreducedSpace f) :=
    DoubleCylinder.pathConnectedSpace (TopCat.ofHom f)
      (TopCat.ofHom (ContinuousMap.const X (PUnit.unit : PUnit.{u + 1})))
      (unreducedSquare f) x
  have hcone : Subsingleton (HomotopyGroup.Pi (m + 2)
      (UnreducedSpace f) (unreducedVertex f)) :=
    subsingleton_pi_of_homology_isZero m (unreducedVertex f)
      (fun z k _ hk ↦ unreducedCone_subsingleton_below_first f x m hf z k hk) hH
  exact subsingleton_firstObstruction_of_cone f x m hf hcone

/-- An actual constant-integral-chain quasi-isomorphism kills the next fiber
obstruction by its actual cone, not by an assumed relative Hurewicz map. -/
theorem subsingleton_firstObstruction_of_integral_quasiIso
    (x : X) (m : ℕ) (hf : IsHomotopyConnectedMap f (m + 1))
    (hH : QuasiIso (pushforwardChainMap f (constant Y integralCoefficientModule.{u}))) :
    Subsingleton (HomotopyGroup.Pi (m + 1) (HomotopyFiber f (f x))
      (HomotopyFiber.basepoint f (f x) x rfl)) :=
  subsingleton_firstObstruction_of_cone_homology f x m hf
    (unreducedCone_positive_homology_isZero_of_quasiIso f integralCoefficientModule.{u}
      hH (m + 1))

/-- The first-obstruction argument raises the connectivity of the original
map, retaining its actual fibers and all of their basepoints. -/
theorem isHomotopyConnectedMap_succ_of_integral_quasiIso
    (m : ℕ) (hf : IsHomotopyConnectedMap f (m + 1))
    (hH : QuasiIso (pushforwardChainMap f (constant Y integralCoefficientModule.{u}))) :
    IsHomotopyConnectedMap f (m + 2) :=
  hf.succ_of_canonical (fun x ↦
    subsingleton_firstObstruction_of_integral_quasiIso f x m hf hH)

end Quillen.ReducedMappingCone
