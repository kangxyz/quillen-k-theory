/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.Prespectrum.FiberSequence

/-! Actual coordinate, connecting-map and negative-degree fiber-sequence consumers. -/
@[expose] public section

open CategoryTheory.Limits.SequentialSystem

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open Quillen Quillen.LoopPrespectrum
universe u
namespace QuillenTest.StableFiberSequence

open Quillen
variable {A E F : LoopPrespectrum.{u}} (f : E ⟶ F)

/-- The full fiber path and structure parameter remain independent. -/
theorem independent_coordinates (n : ℕ) (z : (homotopyFiber f).space n)
    (s t : unitInterval) :
    ((homotopyFiber f).structureMap n z t).1.2 s = F.structureMap n (z.1.2 s) t := rfl

/-- The connecting inclusion retains the literal original loop. -/
theorem original_loop_inclusion (n : ℕ) (γ : Path (F.point n) (F.point n)) (s : unitInterval) :
    ((homotopyFiberLoopInclusion f).map n γ).1.2 s = γ s := rfl

/-- The coherent nullhomotopy keeps the original path, rather than replacing its class. -/
theorem original_nullhomotopy (n : ℕ) (z : (homotopyFiber f).space n) (s : unitInterval) :
    (homotopyFiberNullHomotopy f).level n (s,z) = z.1.2 s := rfl

/-- Specified lifts preserve every value of their supplied nullhomotopy. -/
theorem specified_lift (g : A ⟶ E) (H : LoopPrespectrum.Homotopy (g ≫ f) (zeroHom A F))
    (n : ℕ) (x : A.space n) (s : unitInterval) :
    ((homotopyFiberLift f g H).map n x).1.2 s = H.level n (s,x) := rfl

/-- The degree-zero to degree-minus-one boundary is the actual signed comparison. -/
theorem negative_connecting_formula :
    stableFiberConnecting f (-1) = (parameterStableHomotopyIso F (-1)).inv ≫
      (stableHomotopyFunctor (-1)).map (homotopyFiberLoopInclusion f) := rfl

/-- The exact negative boundary uses the original degree-zero stable map.
The arithmetic index is kept unreduced to avoid unfolding the stable colimit. -/
theorem zero_to_negative_exact :
    Function.Exact ((stableHomotopyFunctor ((-1 : ℤ) + 1)).map f)
      (stableFiberConnecting f (-1)) := stableFiberConnecting_exact_target f (-1)

/-- No Omega hypothesis is required for exactness at the original fiber. -/
theorem arbitrary_fiber_exact (d : ℤ) :
    Function.Exact (stableFiberConnecting f d)
      ((stableHomotopyFunctor d).map (homotopyFiberProjection f)) :=
  stableFiberConnecting_exact_fiber f d

/-- No connectivity premise is required for the original source position. -/
theorem arbitrary_source_exact (d : ℤ) :
    Function.Exact ((stableHomotopyFunctor d).map (homotopyFiberProjection f))
      ((stableHomotopyFunctor d).map f) := stableHomotopyFiber_exact_source f d

/-- The displayed coherent nullhomotopy kills the actual stable composite. -/
theorem original_stable_composite_zero (d : ℤ) :
    (stableHomotopyFunctor d).map (homotopyFiberProjection f) ≫
      (stableHomotopyFunctor d).map f = 0 := by
  rw [← Functor.map_comp]
  exact ((homotopyFiberNullHomotopy f).stableHomotopyMap_eq d).trans
    (stableHomotopyMap_zero (homotopyFiber f) F d)

/-- The boundary on genuine colimit inclusions retains both the alternating sign
and actual negative-degree tail, before applying the original level map. -/
theorem original_connecting_stage (d : ℤ) (n : ℕ) :
    (alternatingIso n (parameterStableStageIso F d n)).hom ≫
      (shiftedStableReindexIso F d n).hom ≫
        stableHomotopyι F (d+1) (parameterStableOffset d+n) ≫ stableFiberConnecting f d =
      (stableSystemMap (homotopyFiberLoopInclusion f) d).app n ≫
        stableHomotopyι (homotopyFiber f) d n := by
  rw [stableFiberConnecting, parameterStableHomotopyIso_ι_inv_assoc, stableHomotopyι_naturality]

end QuillenTest.StableFiberSequence
