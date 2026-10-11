/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassStepSeparation
public import Mathlib.Data.ZMod.Basic

/-! # Original cone, double-cylinder and affine Bass separation consumers -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.Tests.ConePushoutSeparation

/-- The actual constant cone map collapses every bottom endpoint, including nonbase sources. -/
theorem original_constant_cone_fiber {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (s : unitInterval) (x : X) :
    Quillen.ReducedMappingCone.cylinder x₀ y₀ (ContinuousMap.const X y₀) (s, x) =
      Quillen.ReducedMappingCone.point x₀ y₀ (ContinuousMap.const X y₀) ↔
        x = x₀ ∨ s = 1 ∨ s = 0 := by
  simpa only [ContinuousMap.const_apply, and_true] using
    Quillen.ReducedMappingCone.cylinder_eq_point_iff x₀ y₀ (ContinuousMap.const X y₀) rfl (s, x)

/-- Both endpoint fibers of the actual zero-map double cylinder collapse, without injectivity. -/
theorem original_zero_pushout_fiber (A B C : Quillen.LoopPrespectrum.{u})
    (n : ℕ) (s : unitInterval) (x : A.space n) :
    HomotopyPushout.cylinder (zeroHom A B) (zeroHom A C) n (s, x) =
      HomotopyPushout.point (zeroHom A B) (zeroHom A C) n ↔
        x = A.point n ∨ s = 0 ∨ s = 1 := by
  simpa only [zeroHom, ContinuousMap.const_apply, and_true] using
    HomotopyPushout.cylinder_eq_point_iff (zeroHom A B) (zeroHom A C) n (s, x)

/-- Nonbase endpoint preimages are kept literally for arbitrary, possibly noninjective maps. -/
theorem original_nonbase_fibers {A B C : Quillen.LoopPrespectrum.{u}}
    (f : A ⟶ B) (g : A ⟶ C) (n : ℕ) (z : unitInterval × A.space n)
    (y : B.space n) (v : C.space n) (hy : y ≠ B.point n) (hv : v ≠ C.point n) :
    (HomotopyPushout.cylinder f g n z = HomotopyPushout.left f g n y ↔
      z.1 = 0 ∧ f.map n z.2 = y) ∧
    (HomotopyPushout.cylinder f g n z = HomotopyPushout.right f g n v ↔
      z.1 = 1 ∧ g.map n z.2 = v) :=
  ⟨HomotopyPushout.cylinder_eq_left_iff f g n z y hy,
    HomotopyPushout.cylinder_eq_right_iff f g n z v hv⟩

/-- A singleton is closed in the original affine Bass step, with no replacement of its topology. -/
theorem original_bass_singleton (R : CommRingCat.{u}) (n : ℕ)
    (x : (Quillen.PerfectComplexes.affineBassStep R).space n) :
    IsClosed ({x} : Set ((Quillen.PerfectComplexes.affineBassStep R).space n)) :=
  isClosed_singleton

/-- Separation of the original Bass step includes a nonreduced base. -/
theorem nonreduced_bass (n : ℕ) :
    T1Space ((Quillen.PerfectComplexes.affineBassStep (.of (ZMod 4))).space n) := inferInstance

/-- Separation also includes the zero-ring original Bass diagram. -/
theorem zero_ring_bass (n : ℕ) :
    T1Space ((Quillen.PerfectComplexes.affineBassStep (.of (ZMod 1))).space n) := inferInstance

end Quillen.Tests.ConePushoutSeparation
