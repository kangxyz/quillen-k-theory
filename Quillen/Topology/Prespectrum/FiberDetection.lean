/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.Prespectrum.FiberSequence
public import Quillen.Topology.Prespectrum.StableEquivalence

/-!
Vanishing of every actual stable fiber group detects a stable equivalence. The negative fiber degree
is retained when proving degree-zero surjectivity. No cofiber comparison or Omega hypothesis is
assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum
variable {E F : LoopPrespectrum.{u}} (f : E ⟶ F)

/-- The actual stable fiber groups vanish for every stable equivalence. -/
theorem stableFiber_subsingleton_of_isStableEquivalence
    (hf : IsStableEquivalence f) (d : ℤ) :
    Subsingleton (stableHomotopyGroup (homotopyFiber f) d) := by
  have hinj := ((ConcreteCategory.isIso_iff_bijective _).mp (hf d)).injective
  have hsurj := ((ConcreteCategory.isIso_iff_bijective _).mp (hf (d+1))).surjective
  have hz (a : stableHomotopyGroup (homotopyFiber f) d) : a = 0 := by
    have hp : (stableHomotopyFunctor d).map (homotopyFiberProjection f) a = 0 := by
      apply hinj
      simpa only [map_zero] using (stableHomotopyFiber_exact_source f d _).mpr ⟨a,rfl⟩
    obtain ⟨b,hb⟩ := (stableFiberConnecting_exact_fiber f d a).mp hp
    obtain ⟨x,hx⟩ := hsurj b
    have hδ := (stableFiberConnecting_exact_target f d b).mpr ⟨x,hx⟩
    exact hb.symm.trans hδ
  exact ⟨fun a b ↦ (hz a).trans (hz b).symm⟩

/-- Conversely, vanishing of the original stable fiber in every degree detects
isomorphisms on the original integer-graded stable groups. -/
theorem isStableEquivalence_of_stableFiber_subsingleton
    (h : ∀ d : ℤ, Subsingleton (stableHomotopyGroup (homotopyFiber f) d)) :
    IsStableEquivalence f := by
  have hinj (d : ℤ) : Function.Injective ((stableHomotopyFunctor d).map f) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    obtain ⟨a,ha⟩ := (stableHomotopyFiber_exact_source f d x).mp hx
    have hzero : a = 0 := (h d).elim _ _
    simpa only [hzero, map_zero] using ha.symm
  have hsurj (d : ℤ) : Function.Surjective ((stableHomotopyFunctor (d+1)).map f) := by
    intro y
    exact (stableFiberConnecting_exact_target f d y).mp ((h d).elim _ _)
  intro d
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨hinj d, ?_⟩
  have hs := hsurj (d-1)
  have he : d-1+1 = d := by omega
  rw [he] at hs
  exact hs

theorem isStableEquivalence_iff_stableFiber_subsingleton :
    IsStableEquivalence f ↔
      ∀ d : ℤ, Subsingleton (stableHomotopyGroup (homotopyFiber f) d) :=
  ⟨fun h d ↦ stableFiber_subsingleton_of_isStableEquivalence f h d,
    isStableEquivalence_of_stableFiber_subsingleton f⟩

end Quillen.LoopPrespectrum
