/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassPushoutExcision
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassConeExcision
public import Quillen.Topology.Prespectrum.PushoutStableEquivalence

/-!
# Original reduced-pushout stable preservation for actual finite Bass-stage corners

The actual chosen-point and growing finite-excision proofs discharge every generic input.
An unchanged strict span map between independently indexed finite Bass-stage corners is stable
as soon as its THREE ORIGINAL corner maps are stable. No complete-weakness, levelwise inverse,
Omega, connectivity-growth, point HEP or row-excision premise is left to the caller.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable (i j k i' j' k' : ℕ) (R S T R' S' T' : CommRingCat.{u})
  (f : (boundedFlatAffineSectionBassDiagram i).obj R ⟶
    (boundedFlatAffineSectionBassDiagram j).obj S)
  (g : (boundedFlatAffineSectionBassDiagram i).obj R ⟶
    (boundedFlatAffineSectionBassDiagram k).obj T)
  (f' : (boundedFlatAffineSectionBassDiagram i').obj R' ⟶
    (boundedFlatAffineSectionBassDiagram j').obj S')
  (g' : (boundedFlatAffineSectionBassDiagram i').obj R' ⟶
    (boundedFlatAffineSectionBassDiagram k').obj T')
  (a : (boundedFlatAffineSectionBassDiagram i).obj R ⟶
    (boundedFlatAffineSectionBassDiagram i').obj R')
  (b : (boundedFlatAffineSectionBassDiagram j).obj S ⟶
    (boundedFlatAffineSectionBassDiagram j').obj S')
  (c : (boundedFlatAffineSectionBassDiagram k).obj T ⟶
    (boundedFlatAffineSectionBassDiagram k').obj T')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')

/-- Original stable corner maps preserve the unchanged reduced pushout at actual finite stages. -/
theorem boundedFlatAffineSectionBass_pushoutMap_isStableEquivalence
    (ha : IsStableEquivalence a) (hb : IsStableEquivalence b) (hc : IsStableEquivalence c) :
    IsStableEquivalence (HomotopyPushout.map f g f' g' a b c wf wg) :=
  HomotopyPushout.map_isStableEquivalence_of_excision f g f' g' a b c wf wg
    (fun n ↦ boundedFlatAffineSectionBassDiagram_point_homotopyExtensionProperty i R (n + 1))
    (fun n ↦ boundedFlatAffineSectionBassDiagram_point_homotopyExtensionProperty j S (n + 1))
    (fun n ↦ boundedFlatAffineSectionBassDiagram_point_homotopyExtensionProperty k T (n + 1))
    (fun n ↦ boundedFlatAffineSectionBassDiagram_point_homotopyExtensionProperty i' R' (n + 1))
    (fun n ↦ boundedFlatAffineSectionBassDiagram_point_homotopyExtensionProperty j' S' (n + 1))
    (fun n ↦ boundedFlatAffineSectionBassDiagram_point_homotopyExtensionProperty k' T' (n + 1))
    (boundedFlatAffineSectionBass_map_coneFiber_isStableEquivalence i j R S f)
    (boundedFlatAffineSectionBass_map_coneFiber_isStableEquivalence i' j' R' S' f')
    (boundedFlatAffineSectionBass_pushoutInr_coneFiber_isStableEquivalence i j k R S T f g)
    (boundedFlatAffineSectionBass_pushoutInr_coneFiber_isStableEquivalence i' j' k' R' S' T' f' g')
    ha hb hc

end Quillen.PerfectComplexes
