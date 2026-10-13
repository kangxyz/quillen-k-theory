/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassPushoutExcision
public import Quillen.Topology.Prespectrum.StrictSquareCone

/-!
# Original Bass square comparison excision at every finite geometric stage

For any actual coefficient square, all four original finite-stage corners and the actual reduced
span have all-point vanishing below n+2 at level n+i+2. Their literal chosen points have HEP.
Consequently the original span-to-final-corner comparison has genuine cone-to-fiber connectivity
2*n+2 and stable excision. No growth, point-set or excision premise remains.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable (i : ℕ) (Q : Arrow (Arrow CommRingCat.{u}))

/-- The actual square comparison has the genuine doubled finite cone-to-fiber range. -/
theorem boundedFlatAffineSectionBass_square_coneFiber_isHomotopyConnectedMap (n : ℕ) :
    IsHomotopyConnectedMap
      ((mappingConeFiberComparison (StrictSquare.comparison
        ((boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow.obj Q))).map (n + i + 2))
      (2 * n + 2) := by
  let S := (boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow.obj Q
  have hP (t : ℕ) (ht : t < n + 2) :
      ∀ z : (StrictSquare.span S).space (n + i + 2),
        Subsingleton (HomotopyGroup.Pi t ((StrictSquare.span S).space (n + i + 2)) z) := by
    have h := boundedFlatAffineSectionBass_pushout_homotopyGroup_subsingleton
      i i i Q.left.left Q.left.right Q.right.left S.left.hom S.hom.left n t ht
    rw [Nat.max_self, Nat.max_self] at h
    exact h
  have hD (x : S.right.right.space (n + i + 2)) (t : ℕ) (ht : t < n + 2) :
      Subsingleton (HomotopyGroup.Pi t (S.right.right.space (n + i + 2)) x) :=
    boundedFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_at
      i Q.right.right n t ht x
  let := pathConnectedSpace_of_subsingleton_pi_zero
    (S.right.right.point (n + i + 2)) (hD _ 0 (by omega))
  apply mappingConeFiberComparison_level_isHomotopyConnectedMap (StrictSquare.comparison S)
    (n + i + 2)
    (HomotopyPushout.point_homotopyExtensionProperty S.left.hom S.hom.left _
      (boundedFlatAffineSectionBassDiagram_point_homotopyExtensionProperty i Q.left.left _)
      (boundedFlatAffineSectionBassDiagram_point_homotopyExtensionProperty i Q.left.right _)
      (boundedFlatAffineSectionBassDiagram_point_homotopyExtensionProperty i Q.right.left _))
    (boundedFlatAffineSectionBassDiagram_point_homotopyExtensionProperty i Q.right.right _)
    (n + 1) (n + 2) (2 * n + 2) (by omega)
  · exact isHomotopyConnectedMap_of_vanishing ((StrictSquare.comparison S).map _)
      ((StrictSquare.span S).point _) (n + 1)
      (fun x t ht ↦ hP t (by omega) x) (fun x t ht ↦ hD x t (by omega))
  · exact isHomotopyConnectedMap_const_of_vanishing
      ((StrictSquare.span S).point _) (n + 2) (fun x t ht ↦ hP t ht x)

/-- Original finite-stage square comparisons satisfy stable cone-to-fiber excision. -/
theorem boundedFlatAffineSectionBass_square_coneFiber_isStableEquivalence :
    IsStableEquivalence (mappingConeFiberComparison (StrictSquare.comparison
      ((boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow.obj Q))) := by
  apply isStableEquivalence_of_eventually_linearConnectivity _ (i + 1) (2 * i)
  intro n hn
  have h := boundedFlatAffineSectionBass_square_coneFiber_isHomotopyConnectedMap
    i Q (n - (i + 1))
  rw [show n - (i + 1) + i + 2 = n + 1 by omega,
    show 2 * (n - (i + 1)) + 2 = 2 * n - 2 * i by omega] at h
  exact h

end Quillen.PerfectComplexes
