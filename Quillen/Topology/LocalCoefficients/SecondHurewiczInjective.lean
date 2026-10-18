/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.LocalCoefficients.SecondHurewicz
public import Quillen.Topology.LocalCoefficients.FiniteCapDescent
public import Quillen.Topology.LocalCoefficients.RelativeFiniteBoundary
public import Quillen.Topology.HomotopyFiber.ContractibleSource

/-!
# Injectivity of the original marked second Hurewicz map

In a simply connected target, a vanishing marked spherical cycle is an
actual finite integral boundary. Finite-cap descent at the actual map from
ULift PUnit kills its original connecting class after abelianization. The
original contractible-source connecting bijection has abelian source Pi two,
so its inverse descends through that abelianization and detects the original
class. This proves injectivity without any H-two surjectivity premise.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Limits Convexity
open scoped Simplicial Topology unitInterval

namespace Quillen.LocalCoefficients.SecondHurewicz
variable {Y : Type u} [TopologicalSpace Y] [SimplyConnectedSpace Y] {y : Y}

/-- A literal marked spherical boundary forces its original stick Pi-two class to be one. -/
theorem sphericalClass_zero_imp_class_one (a : SphericalSimplex Y y 2)
    (ha : sphericalClass a = 0) : a.homotopyClassStick = 1 := by
  let j : C(ULift.{u} PUnit, Y) := ContinuousMap.const _ y
  let x : ULift.{u} PUnit := ⟨PUnit.unit⟩
  have hj : Function.Injective j := fun _ _ _ => Subsingleton.elim _ _
  obtain ⟨bC, hbC⟩ := chainCycle_boundary_of_homology_eq_zero (Chains Y) 2
    (sphericalTwoCycle a) ha
  obtain ⟨b, w, hb⟩ := chain_exists_finite_sum
    (constant Y integralCoefficientModule.{u}) ⦋3⦌ bC
  have heq : (Chains Y).d 3 2
      (∑ τ ∈ b, chainInclusion (constant Y integralCoefficientModule.{u}) τ (w τ)) =
    sphericalTwoChain a -
      (pushforwardChainMap j (constant Y integralCoefficientModule.{u})).f 2
        (∑ τ ∈ (∅ : Finset (SingularSimplex (ULift.{u} PUnit) ⦋2⦌)),
          chainInclusion (constant (ULift.{u} PUnit) integralCoefficientModule.{u}) τ 0) := by
    rw [← hb, hbC, iCycles_sphericalTwoCycle]
    simp only [Finset.sum_empty, map_zero, sub_zero]
  have hc := connectingAbelianization_zero_of_finite_chain_equation j hj x a ∅
    (fun _ => 0) b w (by simp) heq
  let d := HomotopyFiber.connectingHom j y x rfl 0
  have hd : Function.Bijective d :=
    (HomotopyFiber.loopInclusion_bijective_of_contractibleSource j y x rfl 1).comp
      (loopShiftMulEquiv (x := y) 0).bijective
  let e := MulEquiv.ofBijective d hd
  change Abelianization.of (d a.homotopyClassStick) = 1 at hc
  have hv := congrArg (Abelianization.lift e.symm.toMonoidHom) hc
  have hz : e.symm (e a.homotopyClassStick) = 1 :=
    (Abelianization.lift_apply_of e.symm.toMonoidHom (d a.homotopyClassStick)).symm.trans
      (hv.trans (map_one (Abelianization.lift e.symm.toMonoidHom)))
  exact (e.symm_apply_apply a.homotopyClassStick).symm.trans hz

/-- In a simply connected target, the original marked second Hurewicz homomorphism is injective. -/
theorem hom_injective (y : Y) : Function.Injective (hom y) := by
  apply (injective_iff_map_eq_one (hom y)).mpr
  intro a ha
  obtain ⟨a, rfl⟩ := SphericalSimplex.homotopyClassStick_surjective a
  apply sphericalClass_zero_imp_class_one a
  rw [hom_spherical] at ha
  exact congrArg Multiplicative.toAdd ha

end Quillen.LocalCoefficients.SecondHurewicz
