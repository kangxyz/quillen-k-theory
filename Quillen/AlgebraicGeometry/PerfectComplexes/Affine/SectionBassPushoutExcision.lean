/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassConnectivity
public import Quillen.Topology.Prespectrum.PushoutVanishing
public import Quillen.Topology.Prespectrum.ConeFiberConnectivity
public import Quillen.Topology.Prespectrum.StableConnectivity

/-!
# Genuine right-inclusion cone excision for actual finite-stage Bass spans

Original all-point growth of the three independently indexed finite stages passes to their
actual reduced pushout. Together with original point HEP, this gives finite and then stable
cone-to-fiber excision for the unchanged C inclusion. The explicit cutoff is the largest
corner index plus two; no low-level connectivity or row-excision assumption remains.
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

/-- The actual span pushout inherits genuine all-point finite growth at its explicit cutoff. -/
theorem boundedFlatAffineSectionBass_pushout_homotopyGroup_subsingleton
    (n r : ℕ) (hr : r < n + 2)
    (z : (HomotopyPushout.prespectrum f g).space (n + max i (max j k) + 2)) :
    Subsingleton (HomotopyGroup.Pi r
      ((HomotopyPushout.prespectrum f g).space (n + max i (max j k) + 2)) z) :=
  HomotopyPushout.homotopyGroup_subsingleton f g (n + max i (max j k) + 2) n
    (boundedFlatAffineSectionBassDiagram_point_homotopyExtensionProperty i R _)
    (boundedFlatAffineSectionBassDiagram_point_homotopyExtensionProperty j S _)
    (boundedFlatAffineSectionBassDiagram_point_homotopyExtensionProperty k T _)
    (fun x t ht ↦ boundedFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_of_le
      i R _ (by omega) t (by omega) x)
    (fun y t ht ↦ boundedFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_of_le
      j S _ (by omega) t (by omega) y)
    (fun z t ht ↦ boundedFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_of_le
      k T _ (by omega) t (by omega) z) z r hr

/-- The unchanged right inclusion's original cone-fiber comparison has the genuine doubled range. -/
theorem boundedFlatAffineSectionBass_pushoutInr_coneFiber_isHomotopyConnectedMap (n : ℕ) :
    IsHomotopyConnectedMap
      ((mappingConeFiberComparison (HomotopyPushout.inr f g)).map (n + max i (max j k) + 2))
      (2 * n + 2) := by
  have hC (x : ((boundedFlatAffineSectionBassDiagram k).obj T).space
      (n + max i (max j k) + 2)) (t : ℕ) (ht : t < n + 2) :
      Subsingleton (HomotopyGroup.Pi t
        (((boundedFlatAffineSectionBassDiagram k).obj T).space (n + max i (max j k) + 2)) x) :=
    boundedFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_of_le
      k T _ (by omega) t (by omega) x
  have hP (z) (t : ℕ) (ht : t < n + 2) :=
    boundedFlatAffineSectionBass_pushout_homotopyGroup_subsingleton i j k R S T f g n t ht z
  let := pathConnectedSpace_of_subsingleton_pi_zero
    ((HomotopyPushout.prespectrum f g).point (n + max i (max j k) + 2)) (hP _ 0 (by omega))
  apply mappingConeFiberComparison_level_isHomotopyConnectedMap (HomotopyPushout.inr f g)
    (n + max i (max j k) + 2)
    (boundedFlatAffineSectionBassDiagram_point_homotopyExtensionProperty k T _)
    (HomotopyPushout.point_homotopyExtensionProperty f g _
      (boundedFlatAffineSectionBassDiagram_point_homotopyExtensionProperty i R _)
      (boundedFlatAffineSectionBassDiagram_point_homotopyExtensionProperty j S _)
      (boundedFlatAffineSectionBassDiagram_point_homotopyExtensionProperty k T _))
    (n + 1) (n + 2) (2 * n + 2) (by omega)
  · exact isHomotopyConnectedMap_of_vanishing ((HomotopyPushout.inr f g).map _)
      (((boundedFlatAffineSectionBassDiagram k).obj T).point _) (n + 1)
      (fun x t ht ↦ hC x t (by omega)) (fun z t ht ↦ hP z t (by omega))
  · exact isHomotopyConnectedMap_const_of_vanishing
      (((boundedFlatAffineSectionBassDiagram k).obj T).point _) (n + 2) hC

/-- Actual finite-stage span right inclusions have stable original cone-to-fiber excision. -/
theorem boundedFlatAffineSectionBass_pushoutInr_coneFiber_isStableEquivalence :
    IsStableEquivalence (mappingConeFiberComparison (HomotopyPushout.inr f g)) := by
  apply isStableEquivalence_of_eventually_linearConnectivity
    (mappingConeFiberComparison (HomotopyPushout.inr f g))
      (max i (max j k) + 1) (2 * max i (max j k))
  intro n hn
  have h := boundedFlatAffineSectionBass_pushoutInr_coneFiber_isHomotopyConnectedMap
    i j k R S T f g (n - (max i (max j k) + 1))
  rw [show n - (max i (max j k) + 1) + max i (max j k) + 2 = n + 1 by omega,
    show 2 * (n - (max i (max j k) + 1)) + 2 = 2 * n - 2 * max i (max j k) by omega] at h
  exact h

end Quillen.PerfectComplexes
