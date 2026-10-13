/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.Fibration.Prespectrum
public import Quillen.Topology.Prespectrum.FiberOmega

/-! Actual fiber paths, loop transposition, complete Omega fibers and original
acyclic spectrum nullhomotopies with independent category universes. -/
@[expose] public section


noncomputable section
open CategoryTheory
open Quillen Quillen.LoopPrespectrum Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open Quillen.Waldhausen.Fibration
universe u v
namespace QuillenTest.CoherentAcyclicSpectrum

open Quillen

/-- The loop-fiber inverse keeps the original source loop pointwise. -/
theorem inverse_source {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X,Y)) {x : X} {y : Y} (h : f x = y)
    (γ : Path (HomotopyFiber.basepoint f y x h) (HomotopyFiber.basepoint f y x h))
    (t : unitInterval) :
    ((HomotopyFiber.loopFiberHomeomorph f h).symm γ).1.1 t = (γ t).1.1 := rfl

/-- Both distinct path variables survive transposition in the inverse. -/
theorem inverse_whole_path {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X,Y)) {x : X} {y : Y} (h : f x = y)
    (γ : Path (HomotopyFiber.basepoint f y x h) (HomotopyFiber.basepoint f y x h))
    (s t : unitInterval) :
    ((HomotopyFiber.loopFiberHomeomorph f h).symm γ).1.2 s t = (γ t).1.2 s := rfl

/-- The original structure square controls all components as well as higher groups. -/
theorem original_fiber_omega {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (hE : E.IsOmega) (hF : F.IsOmega) (n : ℕ) :
    IsWeakHomotopyEquivalence ((homotopyFiber f).structureMap n) :=
  homotopyFiber_isOmega f hE hF n

variable {C : Type u} [Category.{v} C] (V : Structure C)

/-- The original zero functor remains pointwise zero at every stage. -/
theorem literal_zero_stage (n : ℕ) (x : (originalPrespectrum V).space n) :
    (originalPrespectrumMap V V (zeroFunctor_isExact V V) rfl).map n x =
      (originalPrespectrum V).point n := by
  rw [originalPrespectrumMap_zeroFunctor]
  rfl

/-- Canonical zero normalization retains an explicit fixed-basepoint whole homotopy. -/
theorem normalized_zero_track (n : ℕ) (s : unitInterval) :
    (exactOriginalPrespectrumMapZeroFunctorHomotopy V V).level n
      (s, (originalPrespectrum V).point n) = (originalPrespectrum V).point n :=
  (exactOriginalPrespectrumMapZeroFunctorHomotopy V V).at_point n s

variable (N : NestedWeakEquivalences V)

/-- The actual fiber lift has the original acyclic inclusion as its source. -/
theorem actual_acyclic_source (n : ℕ)
    (x : (originalPrespectrum (acyclicStructure N)).space n) :
    ((canonicalFiberPrespectrumMap N).map n x).1.1 =
      (acyclicInclusionPrespectrumMap N).map n x := rfl

/-- The entire specified nullhomotopy is the actual stored fiber path. -/
theorem actual_acyclic_path (n : ℕ)
    (x : (originalPrespectrum (acyclicStructure N)).space n) (s : unitInterval) :
    ((canonicalFiberPrespectrumMap N).map n x).1.2 s =
      (acyclicPrespectrumNullhomotopy N).level n (s,x) := rfl

/-- The coherent acyclic track respects the original structure maps at every time. -/
theorem actual_acyclic_structure (n : ℕ)
    (x : (originalPrespectrum (acyclicStructure N)).space n) (s t : unitInterval) :
    (originalPrespectrum N.coarse).structureMap n
      ((acyclicPrespectrumNullhomotopy N).level n (s,x)) t =
      (acyclicPrespectrumNullhomotopy N).level (n+1)
        (s, (originalPrespectrum (acyclicStructure N)).structureMap n x t) :=
  ((acyclicPrespectrumNullhomotopy N).comm n s x t).symm

/-- No cylinder or extension assumption is needed for the actual fiber Omega property. -/
theorem actual_acyclic_target_omega :
    (homotopyFiber (changeWeakPrespectrumMap N)).IsOmega :=
  homotopyFiber_isOmega _ (originalPrespectrum_isOmega V)
    (originalPrespectrum_isOmega N.coarse)

end QuillenTest.CoherentAcyclicSpectrum
