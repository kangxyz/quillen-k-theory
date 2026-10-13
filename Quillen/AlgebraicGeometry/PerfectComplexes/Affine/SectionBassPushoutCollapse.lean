/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassTopology
public import Quillen.Topology.Prespectrum.PushoutConeCollapse

/-!
# Original pushout-cone collapse at every actual finite Bass stage

The literal points of every actual finite section Bass stage already have HEP. Consequently
the original cone(C→HPO(f,g))→cone(f) collapse is a complete weak equivalence at EVERY level,
and a stable equivalence in every signed degree. This discharges its point-set hypotheses
without any connectivity-growth or stable-excision assumption.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable (i j k : ℕ) (R S T : CommRingCat.{u})
  (f : (boundedFlatAffineSectionBassDiagram i).obj R ⟶
    (boundedFlatAffineSectionBassDiagram j).obj S)
  (g : (boundedFlatAffineSectionBassDiagram i).obj R ⟶
    (boundedFlatAffineSectionBassDiagram k).obj T)

/-- The actual finite-stage span's original right-cone collapse is weak at every original level. -/
theorem boundedFlatAffineSectionBass_rightConeCollapse_level_isWeakHomotopyEquivalence (n : ℕ) :
    IsWeakHomotopyEquivalence ((HomotopyPushout.rightConeCollapse f g).map n) :=
  HomotopyPushout.rightConeCollapse_level_isWeakHomotopyEquivalence f g n
    (boundedFlatAffineSectionBassDiagram_point_homotopyExtensionProperty i R n)
    (boundedFlatAffineSectionBassDiagram_point_homotopyExtensionProperty j S n)
    (boundedFlatAffineSectionBassDiagram_point_homotopyExtensionProperty k T n)

/-- The unchanged finite-stage span collapse is a stable equivalence in all signed degrees. -/
theorem boundedFlatAffineSectionBass_rightConeCollapse_isStableEquivalence :
    IsStableEquivalence (HomotopyPushout.rightConeCollapse f g) :=
  isStableEquivalence_of_levelwise _
    (boundedFlatAffineSectionBass_rightConeCollapse_level_isWeakHomotopyEquivalence i j k R S T f g)

end Quillen.PerfectComplexes
