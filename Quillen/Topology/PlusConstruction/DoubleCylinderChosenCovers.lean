/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Topology.LocalCoefficients.DoubleCylinderTwistedHomology
public import Quillen.Topology.DoubleMappingCylinder.PiOneLegs
public import Quillen.Topology.LocalCoefficients.TwistedWhiteheadChosenCovers
/-!
The original double-cylinder legs are weak equivalences from the two original
plus certificates and supplied geometric covers. Their maps are constructed.
The Pi-one and arbitrary-local-system hypotheses are derived from the actual cylinder. No comparison
map, leg equivalence or desired homology certificate is assumed.
-/
@[expose] public section

open Topology

open Quillen.DoubleCylinder
open Quillen.LocalCoefficients

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory
open scoped Topology unitInterval
universe u
namespace Quillen.IsPlusConstruction
open LocalCoefficients DoubleCylinder
variable {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
variable {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
variable (sq : IsPushout (intervalEndpoints A) (endMap f g) l e)
include sq
/-- The actual left leg is a weak equivalence from two original plus certificates
and supplied geometric covers, with their commuting lift genuinely constructed. -/
theorem doubleCylinder_leftLeg_isWeakHomotopyEquivalence_chosenCovers
    [LocallyPathConnectedSpace B]
    (a : A) (b : B) (c : C) (γ : Path (f a) b) (δ : Path (g a) c)
    (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    (hg : IsPlusConstruction.{u, u, u} g.hom δ N)
    {E F : Type u} [TopologicalSpace E] [TopologicalSpace F]
    [SimplyConnectedSpace E] [SimplyConnectedSpace F]
    {p : E → B} {q : F → D} (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (hqsurj : Function.Surjective q) (e₀ : E) :
    IsWeakHomotopyEquivalence (gapLeftEndpoint e) := by
  let := hf.targetPathConnected
  let := hg.targetPathConnected
  let := DoubleCylinder.pathConnectedSpace f g sq a
  have hπ := (plus_legs_piOne_bijective f g sq a b c γ δ N hf hg).1
  apply isWeakHomotopyEquivalence_of_twisted_quasiIso_chosenCovers hp hq hqsurj
    (gapLeftEndpoint e) e₀
    (homotopyGroupMap_bijective_at_all_points (gapLeftEndpoint e) (f a) 1 hπ (p e₀))
  intro V
  exact doubleCylinder_leftEnd_universeLift_quasiIso f g sq 0 1
    (bandMidpoint 0 1 zero_lt_one) hg.localCoefficients V
/-- The right original leg has the symmetric genuine chosen-cover conclusion. -/
theorem doubleCylinder_rightLeg_isWeakHomotopyEquivalence_chosenCovers
    [LocallyPathConnectedSpace C]
    (a : A) (b : B) (c : C) (γ : Path (f a) b) (δ : Path (g a) c)
    (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    (hg : IsPlusConstruction.{u, u, u} g.hom δ N)
    {E F : Type u} [TopologicalSpace E] [TopologicalSpace F]
    [SimplyConnectedSpace E] [SimplyConnectedSpace F]
    {p : E → C} {q : F → D} (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (hqsurj : Function.Surjective q) (e₀ : E) :
    IsWeakHomotopyEquivalence (gapRightEndpoint e) := by
  let := hf.targetPathConnected
  let := hg.targetPathConnected
  let := DoubleCylinder.pathConnectedSpace f g sq a
  have hπ := (plus_legs_piOne_bijective f g sq a b c γ δ N hf hg).2
  apply isWeakHomotopyEquivalence_of_twisted_quasiIso_chosenCovers hp hq hqsurj
    (gapRightEndpoint e) e₀
    (homotopyGroupMap_bijective_at_all_points (gapRightEndpoint e) (g a) 1 hπ (p e₀))
  intro V
  exact doubleCylinder_rightEnd_universeLift_quasiIso f g sq 0 1
    (bandMidpoint 0 1 zero_lt_one) hf.localCoefficients V
end Quillen.IsPlusConstruction
