/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassConeExcision
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassPushoutExcision
public import Quillen.Topology.Prespectrum.StableVanishing
public import Quillen.Topology.Prespectrum.PushoutStableGeneration
public import Quillen.Topology.Prespectrum.PositiveLevelEquivalence

/-!
# The actual finite Bass-stage stable lower bound

At stage i the unchanged strict Bass diagram has zero signed groups below -i. Its original
polynomial span is generated in bottom degree -i by the two actual inclusions. Accepted
all-point finite growth and literal point HEP discharge every excision and collapse input;
no assertion about later transition stabilization or the telescope is used.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
universe u
namespace Quillen.PerfectComplexes

/-- Every original finite-stage signed group below the actual offset vanishes. -/
theorem boundedFlatAffineSectionBassDiagram_stable_subsingleton_of_lt
    (i : ℕ) (R : CommRingCat.{u}) (d : ℤ) (hd : d < -(i : ℤ)) :
    Subsingleton (stableHomotopyGroup ((boundedFlatAffineSectionBassDiagram i).obj R) d) := by
  apply stableHomotopyGroup_subsingleton_of_stages _ d
  intro n
  let := boundedFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_of_le
    i R ((-d).toNat + n + 2) (by omega) (d.toNat + n + 2) (by omega)
      (((boundedFlatAffineSectionBassDiagram i).obj R).point ((-d).toNat + n + 2))
  exact inferInstanceAs (Subsingleton (Additive (HomotopyGroup.Pi (d.toNat + n + 2)
    (((boundedFlatAffineSectionBassDiagram i).obj R).space ((-d).toNat + n + 2))
      (((boundedFlatAffineSectionBassDiagram i).obj R).point ((-d).toNat + n + 2)))))

/-- The unchanged right-cone collapse of every actual finite-stage span is stable. -/
theorem boundedFlatAffineSectionBass_rightConeCollapse_isStableEquivalence
    (i j k : ℕ) (R S T : CommRingCat.{u})
    (f : (boundedFlatAffineSectionBassDiagram i).obj R ⟶
      (boundedFlatAffineSectionBassDiagram j).obj S)
    (g : (boundedFlatAffineSectionBassDiagram i).obj R ⟶
      (boundedFlatAffineSectionBassDiagram k).obj T) :
    IsStableEquivalence (HomotopyPushout.rightConeCollapse f g) :=
  isStableEquivalence_of_positiveLevel _ (fun n =>
    HomotopyPushout.rightConeCollapse_level_isWeakHomotopyEquivalence f g (n + 1)
      (boundedFlatAffineSectionBassDiagram_point_homotopyExtensionProperty i R (n + 1))
      (boundedFlatAffineSectionBassDiagram_point_homotopyExtensionProperty j S (n + 1))
      (boundedFlatAffineSectionBassDiagram_point_homotopyExtensionProperty k T (n + 1)))

/-- At the stage-i bottom degree, the original two polynomial inclusions generate the span. -/
theorem boundedFlatAffineSectionBassSpan_bottom_generate
    (i : ℕ) (R : CommRingCat.{u})
    (z : stableHomotopyGroup (HomotopyPushout.prespectrum
      ((boundedFlatAffineSectionBassDiagram i).map (coefficient R))
      ((boundedFlatAffineSectionBassDiagram i).map (coefficient R))) (-(i : ℤ))) :
    ∃ x : stableHomotopyGroup
      ((boundedFlatAffineSectionBassDiagram i).obj (.of (Polynomial R))) (-(i : ℤ)),
    ∃ y : stableHomotopyGroup
      ((boundedFlatAffineSectionBassDiagram i).obj (.of (Polynomial R))) (-(i : ℤ)),
      (stableHomotopyFunctor (-(i : ℤ))).map (HomotopyPushout.inl
        ((boundedFlatAffineSectionBassDiagram i).map (coefficient R))
        ((boundedFlatAffineSectionBassDiagram i).map (coefficient R))) x +
      (stableHomotopyFunctor (-(i : ℤ))).map (HomotopyPushout.inr
        ((boundedFlatAffineSectionBassDiagram i).map (coefficient R))
        ((boundedFlatAffineSectionBassDiagram i).map (coefficient R))) y = z :=
  HomotopyPushout.stable_inclusions_generate
    ((boundedFlatAffineSectionBassDiagram i).map (coefficient R))
    ((boundedFlatAffineSectionBassDiagram i).map (coefficient R))
    (boundedFlatAffineSectionBass_coefficient_coneFiber_isStableEquivalence i (coefficient R))
    (boundedFlatAffineSectionBass_pushoutInr_coneFiber_isStableEquivalence
      i i i R (.of (Polynomial R)) (.of (Polynomial R)) _ _)
    (boundedFlatAffineSectionBass_rightConeCollapse_isStableEquivalence
      i i i R (.of (Polynomial R)) (.of (Polynomial R)) _ _)
    (-(i : ℤ))
    (boundedFlatAffineSectionBassDiagram_stable_subsingleton_of_lt
      i R (-(i : ℤ) - 1) (by omega)) z

/-- The actual polynomial span at stage i also has zero stable groups below -i. -/
theorem boundedFlatAffineSectionBassSpan_stable_subsingleton_of_lt
    (i : ℕ) (R : CommRingCat.{u}) (d : ℤ) (hd : d < -(i : ℤ)) :
    Subsingleton (stableHomotopyGroup (HomotopyPushout.prespectrum
      ((boundedFlatAffineSectionBassDiagram i).map (coefficient R))
      ((boundedFlatAffineSectionBassDiagram i).map (coefficient R))) d) :=
  HomotopyPushout.stableHomotopyGroup_subsingleton_of_corner_groups
    ((boundedFlatAffineSectionBassDiagram i).map (coefficient R))
    ((boundedFlatAffineSectionBassDiagram i).map (coefficient R))
    (boundedFlatAffineSectionBass_coefficient_coneFiber_isStableEquivalence i (coefficient R))
    (boundedFlatAffineSectionBass_pushoutInr_coneFiber_isStableEquivalence
      i i i R (.of (Polynomial R)) (.of (Polynomial R)) _ _)
    (boundedFlatAffineSectionBass_rightConeCollapse_isStableEquivalence
      i i i R (.of (Polynomial R)) (.of (Polynomial R)) _ _) d
    (boundedFlatAffineSectionBassDiagram_stable_subsingleton_of_lt i R (d - 1) (by omega))
    (boundedFlatAffineSectionBassDiagram_stable_subsingleton_of_lt i (.of (Polynomial R)) d hd)
    (boundedFlatAffineSectionBassDiagram_stable_subsingleton_of_lt i (.of (Polynomial R)) d hd)

end Quillen.PerfectComplexes
