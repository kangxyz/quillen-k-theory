/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Realization.CubicalLifting
public import Quillen.Topology.HELP.WeakFinite
public import Quillen.Topology.HELP.CompactHomotopyEquivalence

/-!
# Whitehead's theorem for actual simplicial realizations

A weak homotopy equivalence between the realizations of two simplicial sets is
promoted to an actual continuous homotopy equivalence with the original forward
map. Literal cube-boundary lifting for its mapping-path endpoint transports to
realized simplex boundaries and then to all realized simplicial monomorphisms.
The empty inclusion supplies a global inverse, and the actual simplicial
cylinder endpoint inclusion supplies the second inverse homotopy.

No compact HELP, external CW-type certificate, or chosen based inverse data is
assumed. The theorem concerns actual simplicial realizations.
-/

@[expose] public section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen.Realization

/-- A weak homotopy equivalence between actual simplicial realizations has an
actual continuous homotopy inverse. The forward continuous map is unchanged. -/
def homotopyEquivOfWeakHomotopyEquivalence {X Y : SSet.{u}} (f : C(|X|, |Y|))
    (hf : IsWeakHomotopyEquivalence f) :
    ContinuousMap.HomotopyEquiv |X| |Y| := by
  let i := (⊥ : Y.Subcomplex).ι
  let a : |((⊥ : Y.Subcomplex) : SSet.{u})| ⟶ TopCat.of (MappingPath f) :=
    TopCat.ofHom ⟨isEmptyElim, continuous_of_discreteTopology⟩
  let p := TopCat.ofHom (MappingPath.endpoint f)
  letI : HasLiftingProperty (SSet.toTop.map i) p :=
    hf.mappingPath_endpoint_boundaryLifting.hasLiftingProperty_realization_mono i
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
    (hf.mappingPath_endpoint_boundaryLifting.hasLiftingProperty_realization_mono
      (simplicialCylinderEndpoints X))
    a₀ a₁ (TopCat.ofHom f) h₀ h₁
  exact {
    toFun := f
    invFun := g
    left_inv := ⟨((ContinuousMap.Homotopy.refl (MappingPath.source f)).comp H).cast rfl rfl⟩
    right_inv := ⟨K⟩ }

@[simp]
theorem homotopyEquivOfWeakHomotopyEquivalence_toFun {X Y : SSet.{u}} (f : C(|X|, |Y|))
    (hf : IsWeakHomotopyEquivalence f) :
    (homotopyEquivOfWeakHomotopyEquivalence f hf).toFun = f := rfl

end Quillen.Realization
