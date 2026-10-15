/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyFiber.ConnectingLoopTranspose
public import Quillen.Topology.Prespectrum.ParameterLooping
public import Quillen.AlgebraicGeometry.PerfectComplexes.GlobalLocalization

/-!
# Original connecting-map normalization consumers

These consumers retain the actual relative-open and qcqs connecting homomorphisms. They
check the literal coordinate swap and its proved sign on arbitrary double-loop classes.
They do not identify the normalized class of the original Laurent unit.
-/
@[expose] public section

open Quillen.PerfectComplexes

noncomputable section
open scoped Topology unitInterval
open AlgebraicGeometry
open Quillen.Waldhausen.Fibration
universe u v
namespace QuillenTest.ScalarConnectingNormalization

open Quillen

/-- The unchanged fiber-loop composite retains independent loop and fiber coordinates. -/
theorem original_coordinates {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    {x : X} {y : Y} (h : f x = y)
    (γ : Path (Path.refl y) (Path.refl y)) (t s : unitInterval) :
    (HomotopyFiber.loopConnectingMap f h γ t).val.1 = x ∧
      (HomotopyFiber.loopConnectingMap f h γ t).val.2 s = γ s t :=
  ⟨HomotopyFiber.loopConnectingMap_source f h γ t,
    HomotopyFiber.loopConnectingMap_path f h γ t s⟩

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
local notation "f" => changeWeakMap (perfectOpenNested j)
local notation "h" => changeWeakMap_basepoint (perfectOpenNested j)
local notation "y" => Quillen.Waldhausen.Structure.kBasepoint (perfectOpenWeakWaldhausen j)

/-- The original relative boundary agrees with the transposed fiber-loop inclusion on every class.
-/
theorem original_relative_boundary
    (a : HomotopyGroup.Pi 0 (Path (Path.refl y) (Path.refl y))
      (Path.refl (Path.refl y))) :
    perfectSupportedFiberKMap j 0
        (perfectOpenConnectingHom j 0
          (((loopShiftEquiv (x := y) 1).symm
            ((loopShiftEquiv (x := Path.refl y) 0).symm a))⁻¹)) =
      (loopShiftEquiv 0).symm
        (homotopyGroupMap (HomotopyFiber.loopConnectingMap f h)
          (HomotopyFiber.loopConnectingMap_refl f h) a) := by
  rw [perfectSupportedFiberKMap_connecting]
  exact (HomotopyFiber.connectingHom_loopConnectingMap_sign f h
    (doubleLoopTranspose y) (doubleLoopTranspose_refl y)
    (fun γ s t ↦ doubleLoopTranspose_apply y γ s t) a).symm

/-- The actual qcqs boundary retains the original relative restriction and the same normalization.
-/
theorem original_qcqs_boundary [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (a : HomotopyGroup.Pi 0 (Path (Path.refl y) (Path.refl y))
      (Path.refl (Path.refl y))) :
    perfectSupportedFiberKMap j 0
        (qcqsPerfectConnectingHom j 0
          (perfectOpenKRestrict j 1
            (((loopShiftEquiv (x := y) 1).symm
              ((loopShiftEquiv (x := Path.refl y) 0).symm a))⁻¹))) =
      (loopShiftEquiv 0).symm
        (homotopyGroupMap (HomotopyFiber.loopConnectingMap f h)
          (HomotopyFiber.loopConnectingMap_refl f h) a) := by
  have hc := DFunLike.congr_fun (qcqsPerfectConnectingHom_comp_relative j 0)
    (((loopShiftEquiv (x := y) 1).symm
      ((loopShiftEquiv (x := Path.refl y) 0).symm a))⁻¹)
  exact (congrArg (perfectSupportedFiberKMap j 0) hc).trans (original_relative_boundary j a)

end QuillenTest.ScalarConnectingNormalization
