/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.HELP.FiberwiseRealizationLifting
public import Quillen.Topology.HELP.CompactHomotopyEquivalence

/-! # Actual equivalence of realization totals from genuine fiber HELP

When both total spaces are actual simplicial realizations, the proved
realized-inclusion lifting constructs a global inverse and both homotopies.
This does not presume a realization model for an arbitrary homotopy pullback.
-/
@[expose] public section

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen
open TheoremA

/-- The original map of genuine fibrations between actual realizations is a
homotopy equivalence if its actual strict-fiber maps have compact HELP. -/
def homotopyEquivOfRealizationFiberHELP {X Y : SSet.{u}}
    {B : Type u} [TopologicalSpace B]
    (pBase : C(|X|, B)) (qBase : C(|Y|, B)) (f : C(|X|, |Y|)) (wBase : qBase.comp f = pBase)
    (hpBase : HomotopyLiftingProperty pBase) (hqBase : HomotopyLiftingProperty qBase)
    (hf : ∀ b : B, CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictMapOver pBase qBase f wBase b)) :
    ContinuousMap.HomotopyEquiv |X| |Y| := by
  let i := (⊥ : Y.Subcomplex).ι
  let a : |((⊥ : Y.Subcomplex) : SSet.{u})| ⟶ TopCat.of (MappingPath f) :=
    TopCat.ofHom ⟨isEmptyElim, continuous_of_discreteTopology⟩
  let p := TopCat.ofHom (MappingPath.endpoint f)
  letI : HasLiftingProperty (SSet.toTop.map i) p :=
    MappingPath.endpoint_realization_mono_of_fiberHELP pBase qBase f wBase hpBase hqBase hf i
  have sq : CommSq a (SSet.toTop.map i) p (𝟙 |Y|) := ⟨by ext x; exact isEmptyElim x⟩
  let s := sq.lift
  have hs : s ≫ p = 𝟙 |Y| := sq.fac_right
  let g : C(|Y|, |X|) := (MappingPath.source f).comp s.hom
  let K : (f.comp g).Homotopy (ContinuousMap.id |Y|) := {
    toFun z := (s z.2).1.2 z.1
    continuous_toFun := by fun_prop
    map_zero_left x := (s x).2
    map_one_left x := ConcreteCategory.congr_hom hs x }
  let a₀ : |X| ⟶ TopCat.of (MappingPath f) := TopCat.ofHom f ≫ s
  let a₁ : |X| ⟶ TopCat.of (MappingPath f) := TopCat.ofHom (MappingPath.inclusion f)
  have h₀ : a₀ ≫ p = TopCat.ofHom f := by rw [Category.assoc, hs, Category.comp_id]
  have h₁ : a₁ ≫ p = TopCat.ofHom f := rfl
  let H := homotopyOfRealizedEndpointLifting p X
    (MappingPath.endpoint_realization_mono_of_fiberHELP pBase qBase f wBase hpBase hqBase hf
      (simplicialCylinderEndpoints X))
    a₀ a₁ (TopCat.ofHom f) h₀ h₁
  exact {
    toFun := f
    invFun := g
    left_inv := ⟨((ContinuousMap.Homotopy.refl (MappingPath.source f)).comp H).cast rfl rfl⟩
    right_inv := ⟨K⟩ }

@[simp] theorem homotopyEquivOfRealizationFiberHELP_toFun {X Y : SSet.{u}}
    {B : Type u} [TopologicalSpace B]
    (pBase : C(|X|, B)) (qBase : C(|Y|, B)) (f : C(|X|, |Y|)) (wBase : qBase.comp f = pBase)
    (hpBase : HomotopyLiftingProperty pBase) (hqBase : HomotopyLiftingProperty qBase)
    (hf : ∀ b : B, CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictMapOver pBase qBase f wBase b)) :
    (homotopyEquivOfRealizationFiberHELP pBase qBase f wBase hpBase hqBase hf).toFun = f := rfl

end Quillen
