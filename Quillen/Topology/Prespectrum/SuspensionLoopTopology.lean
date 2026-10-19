/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.SuspensionLoopUnit
public import Quillen.Topology.Prespectrum.ConeLoopSeparation
public import Quillen.Topology.HomotopyCofiber.ReducedMappingConeCollapse
public import Quillen.Topology.HomotopyCofiber.ReducedMappingConeVanishing

/-!
# Original point topology and growth of the suspension-loop carrier

The suspension is the original cone to the point. Its chosen point inherits HEP and its
all-point linear vanishing offset is unchanged. Parameter looping then raises the offset by
one, using the original loop vanishing theorem at every component. These are point-set and
all-point statements, not consequences of a stable equivalence.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum

/-- The original suspension quotient retains T1 separation at every original level. -/
instance suspensionConeSpaceT1Space (E : LoopPrespectrum.{u}) (n : ℕ)
    [T1Space (E.space n)] : T1Space ((suspensionCone E).space n) := by
  let : T1Space (pointPrespectrum.{u}.space n) := inferInstanceAs (T1Space PUnit.{u + 1})
  change T1Space ((mappingCone (zeroHom E pointPrespectrum)).space n)
  infer_instance

/-- The actual suspension point has HEP from the original input point. -/
theorem suspensionCone_point_homotopyExtensionProperty (E : LoopPrespectrum.{u}) (n : ℕ)
    (hE : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (E.point n)))) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom
      (ContinuousMap.const PUnit.{u + 1} ((suspensionCone E).point n))) :=
  ReducedMappingCone.point_homotopyExtensionProperty (E.point n) (pointPrespectrum.point n)
    ((zeroHom E pointPrespectrum).map n) ((zeroHom E pointPrespectrum).map_point n)
    hE (pointPrespectrum_point_homotopyExtensionProperty n)

/-- Suspension preserves the full original linear vanishing offset above cutoff two. -/
theorem suspensionCone_homotopyGroup_subsingleton (E : LoopPrespectrum.{u}) (c : ℕ)
    (hE : ∀ n, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (E.point n))))
    (hπ : ∀ n x k, k < n + 2 →
      Subsingleton (HomotopyGroup.Pi k (E.space (n + c + 2)) x))
    (n : ℕ) (x : (suspensionCone E).space (n + c + 2)) (k : ℕ) (hk : k < n + 2) :
    Subsingleton (HomotopyGroup.Pi k ((suspensionCone E).space (n + c + 2)) x) :=
  ReducedMappingCone.homotopyGroup_subsingleton (E.point _) (pointPrespectrum.point _)
    ((zeroHom E pointPrespectrum).map _) ((zeroHom E pointPrespectrum).map_point _)
    (hE _) (pointPrespectrum_point_homotopyExtensionProperty _) n
    (hπ n) (fun y j _ ↦ Quillen.subsingleton_pi_of_contractible j PUnit.{u + 1} y) x k hk

/-- The actual parameter-looped suspension retains its original chosen-point HEP. -/
theorem suspensionLoop_point_homotopyExtensionProperty (E : LoopPrespectrum.{u}) (n : ℕ)
    [T1Space (E.space n)]
    (hE : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (E.point n)))) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1}
      ((parameterLooping (suspensionCone E)).point n))) :=
  parameterLooping_point_homotopyExtensionProperty _ n isClosed_singleton
    (suspensionCone_point_homotopyExtensionProperty E n hE)

/-- The actual looped suspension loses exactly one degree, at every original loop component. -/
theorem suspensionLoop_homotopyGroup_subsingleton (E : LoopPrespectrum.{u}) (c : ℕ)
    (hE : ∀ n, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (E.point n))))
    (hπ : ∀ n x k, k < n + 2 →
      Subsingleton (HomotopyGroup.Pi k (E.space (n + c + 2)) x))
    (n : ℕ) (x : (parameterLooping (suspensionCone E)).space (n + (c + 1) + 2))
    (k : ℕ) (hk : k < n + 2) :
    Subsingleton (HomotopyGroup.Pi k
      ((parameterLooping (suspensionCone E)).space (n + (c + 1) + 2)) x) := by
  have he : n + (c + 1) + 2 = (n + 1) + c + 2 := by omega
  revert x
  rw [he]
  intro x
  exact Quillen.subsingleton_pi_loop_of_succ ((suspensionCone E).point _) k
    (suspensionCone_homotopyGroup_subsingleton E c hE hπ (n + 1)
      ((suspensionCone E).point _) (k + 1) (by omega)) x

end Quillen.LoopPrespectrum
