/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.HomotopyFiber.LES
public import Quillen.Topology.HomotopyFiber.Components
public import Quillen.Topology.HomotopyEquiv.Based

/-!
# The pointed-set tail of the homotopy-fiber long exact sequence

The cubical constructions also work in degree zero, where no group structure
is assumed. The connecting function `π₁ Y → π₀ HF(f)` and the remaining tail
are exact as pointed sets: image equals preimage of the distinguished class.
-/
@[expose] public section


noncomputable section
universe w u v
namespace Quillen.HomotopyFiber
variable {N : Type w} {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]
variable (f : C(X, Y)) (y : Y) (x : X) (h : f x = y)

/-- Package the already constructed explicit based inverse homotopies. -/
def iteratedFiberBasedEquivLoops :
    BasedHomotopyEquiv (iteratedBasepoint f y x h) (Path.refl y) where
  toMap := iteratedToLoops f y x h
  invMap := loopsToIterated f y x h
  map_point := iteratedToLoops_basepoint f y x h
  inv_point := loopsToIterated_refl f y x h
  leftHomotopy := (iteratedLeftInverseHomotopy f y x h).toHomotopy
  rightHomotopy := loopsRightInverseHomotopy f y x h
  left_fixed := iteratedLeftInverseHomotopy_based f y x h
  right_fixed := loopsRightInverseHomotopy_based f y x h

/-- Identification of the loop inclusion on arbitrary homotopy sets. -/
theorem homotopyGroupMap_loopInclusion_apply (a : HomotopyGroup N (Path y y) (Path.refl y)) :
    homotopyGroupMap (loopInclusion f y x h) (loopInclusion_refl f y x h) a =
      homotopyGroupMap (projection (projection f y) x)
        (projection_basepoint (projection f y) x (basepoint f y x h) rfl)
        (homotopyGroupMap (loopsToIterated f y x h) (loopsToIterated_refl f y x h) a) :=
  homotopyGroupMap_comp (loopsToIterated f y x h) (loopsToIterated_refl f y x h)
    (projection (projection f y) x)
    (projection_basepoint (projection f y) x (basepoint f y x h) rfl) a

/-- Pointed-set exactness at the homotopy fiber in every degree. -/
theorem mem_range_loopInclusion_iff_constant
    (a : HomotopyGroup N (HomotopyFiber f y) (basepoint f y x h)) :
    a ∈ Set.range (homotopyGroupMap (loopInclusion f y x h) (loopInclusion_refl f y x h)) ↔
      homotopyGroupMap (projection f y) (projection_basepoint f y x h) a =
        (Quotient.mk' GenLoop.const : HomotopyGroup N X x) := by
  rw [← mem_range_projection_iff_constant (projection f y) x (basepoint f y x h) rfl a]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨_, (homotopyGroupMap_loopInclusion_apply f y x h b).symm⟩
  · rintro ⟨b, rfl⟩
    let e := (iteratedFiberBasedEquivLoops f y x h).homotopySetEquiv N
    refine ⟨e b, ?_⟩
    exact (homotopyGroupMap_loopInclusion_apply f y x h (e b)).trans
      (congrArg (homotopyGroupMap (projection (projection f y) x)
        (projection_basepoint (projection f y) x (basepoint f y x h) rfl))
          (e.symm_apply_apply b))

/-- Pointed-set exactness at the target loop space in every degree. -/
theorem mem_range_loopMap_iff_constant
    (a : HomotopyGroup N (Path y y) (Path.refl y)) :
    a ∈ Set.range (homotopyGroupMap (basedLoopMap f h) (basedLoopMap_refl f h)) ↔
      homotopyGroupMap (loopInclusion f y x h) (loopInclusion_refl f y x h) a =
        (Quotient.mk' GenLoop.const : HomotopyGroup N (HomotopyFiber f y) (basepoint f y x h)) := by
  constructor
  · rintro ⟨b, rfl⟩
    rw [← homotopyGroupMap_comp]
    have hh := homotopyGroupMap_eq_of_based_homotopy (N := N)
      (f := (loopInclusion f y x h).comp (basedLoopMap f h))
      (g := ContinuousMap.const (Path x x) (basepoint f y x h))
      (x := Path.refl x) (y := basepoint f y x h)
      ((congrArg (loopInclusion f y x h) (basedLoopMap_refl f h)).trans
        (loopInclusion_refl f y x h)) rfl
      (loopMapInclusionNullhomotopy f y x h) (loopMapInclusionNullhomotopy_based f y x h)
    exact (congrFun hh b).trans (homotopyGroupMap_const_apply (basepoint f y x h) _ b)
  · refine Quotient.inductionOn a (fun p hp => ?_)
    change Quotient.mk' (genLoopPostcomp (loopInclusion f y x h)
      (loopInclusion_refl f y x h) p) = Quotient.mk' GenLoop.const at hp
    obtain ⟨H⟩ := Quotient.exact hp
    refine ⟨Quotient.mk' (sourceLoopsOfNullhomotopy f y x h p H), ?_⟩
    exact Quotient.sound ⟨(squareLoopHomotopy f y x h p H).symm⟩

/-- The connecting function on homotopy sets, including `π₁Y → π₀HF(f)`. -/
def connectingMap (n : ℕ) :
    HomotopyGroup.Pi (n + 1) Y y →
      HomotopyGroup.Pi n (HomotopyFiber f y) (basepoint f y x h) :=
  fun a => homotopyGroupMap (loopInclusion f y x h) (loopInclusion_refl f y x h)
    (loopShiftEquiv n a)

/-- Exactness at the fiber, with the degree-shifted connecting function. -/
theorem mem_range_connectingMap_iff_constant (n : ℕ)
    (a : HomotopyGroup.Pi n (HomotopyFiber f y) (basepoint f y x h)) :
    a ∈ Set.range (connectingMap f y x h n) ↔
      homotopyGroupMap (projection f y) (projection_basepoint f y x h) a =
        (Quotient.mk' GenLoop.const : HomotopyGroup.Pi n X x) := by
  rw [← mem_range_loopInclusion_iff_constant f y x h a]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨b, rfl⟩
    refine ⟨(loopShiftEquiv n).symm b, ?_⟩
    exact congrArg (homotopyGroupMap (loopInclusion f y x h) (loopInclusion_refl f y x h))
      ((loopShiftEquiv n).apply_symm_apply b)

/-- Exactness at the target, with no group assumption on the next term. -/
theorem mem_range_piMap_iff_connectingMap_constant (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) Y y) :
    a ∈ Set.range (homotopyGroupMap (N := Fin (n + 1)) f h) ↔
      connectingMap f y x h n a =
        (Quotient.mk' GenLoop.const : HomotopyGroup.Pi n (HomotopyFiber f y) (basepoint f y x
          h)) := by
  change _ ↔ homotopyGroupMap (loopInclusion f y x h) (loopInclusion_refl f y x h)
    (loopShiftEquiv n a) = _
  rw [← mem_range_loopMap_iff_constant f y x h (loopShiftEquiv n a)]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨loopShiftEquiv n b, (loopShiftEquiv_natural n f h b).symm⟩
  · rintro ⟨b, hb⟩
    refine ⟨(loopShiftEquiv n).symm b, ?_⟩
    apply (loopShiftEquiv n).injective
    exact (loopShiftEquiv_natural n f h ((loopShiftEquiv n).symm b)).trans
      ((congrArg (homotopyGroupMap (basedLoopMap f h) (basedLoopMap_refl f h))
        ((loopShiftEquiv n).apply_symm_apply b)).trans hb)

/-- The connecting set-map agrees with the connecting homomorphism wherever
the latter's target has its ordinary homotopy-group structure. -/
theorem connectingMap_succ (n : ℕ) :
    connectingMap f y x h (n + 1) = connectingHom f y x h n := rfl

/-- The full low-degree tail is exact as pointed sets at `π₁Y`, `π₀HF`, and `π₀X`. -/
theorem lowDegreeExactSequence :
    Set.range (homotopyGroupMap (N := Fin 1) f h) =
      {a | connectingMap f y x h 0 a =
        (Quotient.mk' GenLoop.const : HomotopyGroup.Pi 0 (HomotopyFiber f y) (basepoint f y x h))} ∧
    Set.range (connectingMap f y x h 0) =
      {a | homotopyGroupMap (projection f y) (projection_basepoint f y x h) a =
        (Quotient.mk' GenLoop.const : HomotopyGroup.Pi 0 X x)} ∧
    Set.range (homotopyGroupMap (N := Fin 0) (projection f y) (projection_basepoint f y x h)) =
      {a | homotopyGroupMap f h a = (Quotient.mk' GenLoop.const : HomotopyGroup.Pi 0 Y y)} := by
  refine ⟨?_, ?_, piZero_exact f y x h⟩
  · ext a
    exact mem_range_piMap_iff_connectingMap_constant f y x h 0 a
  · ext a
    exact mem_range_connectingMap_iff_constant f y x h 0 a

end Quillen.HomotopyFiber
