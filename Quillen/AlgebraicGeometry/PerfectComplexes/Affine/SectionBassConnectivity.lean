/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassTopology
public import Quillen.KTheory.Bass.StrictDiagramVanishing
public import Quillen.Waldhausen.SConstruction.Iterated.FiniteConnectivity

/-!
# Actual finite connectivity growth at every section Bass iterate

The proved original S-level growth and literal point HEP discharge the seed assumptions.
The actual reduced pushout, cone and parameter-loop proofs give offset i at Bass stage i:
at original level n+i+2 all homotopy sets below n+2 vanish at every point. Point maps have
connectivity n+2 and original maps between such stages have connectivity n+1. The cutoff
is explicit; no low-level component assertion or eventual-growth premise is introduced.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

/-- Every actual finite Bass iterate has the proved one-degree-per-step growth offset. -/
theorem boundedFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_at
    (i : ℕ) (R : CommRingCat.{u}) (n k : ℕ) (hk : k < n + 2)
    (x : ((boundedFlatAffineSectionBassDiagram i).obj R).space (n + i + 2)) :
    Subsingleton (HomotopyGroup.Pi k
      (((boundedFlatAffineSectionBassDiagram i).obj R).space (n + i + 2)) x) := by
  have hπ := KTheory.Bass.strictDiagramIterate_homotopyGroup_subsingleton
    PolynomialBaseChange.laurentSquareFunctor i boundedFlatAffineSectionPrespectrumFunctor
    boundedFlatAffineSectionPrespectrum_point_homotopyExtensionProperty 0
    (fun S m j hj y ↦ Waldhausen.IteratedS.prespectrum_positiveLevel_homotopyGroup_subsingleton_at
      (boundedFlatAffineSectionModel S) (m + 1) j (by omega) y) R n k hk
  rw [Nat.zero_add] at hπ
  exact hπ x

/-- The same genuine bound in an arbitrary original level above the explicit stage cutoff. -/
theorem boundedFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_of_le
    (i : ℕ) (R : CommRingCat.{u}) (m : ℕ) (hm : i + 2 ≤ m)
    (k : ℕ) (hk : k + i < m)
    (x : ((boundedFlatAffineSectionBassDiagram i).obj R).space m) :
    Subsingleton (HomotopyGroup.Pi k
      (((boundedFlatAffineSectionBassDiagram i).obj R).space m) x) := by
  let n := m - (i + 2)
  have he : n + i + 2 = m := by dsimp [n]; omega
  have hπ := boundedFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_at i R n k
    (by dsimp [n]; omega)
  rw [he] at hπ
  exact hπ x

/-- The original stage-to-point map has the sharper finite bound above its explicit cutoff. -/
theorem boundedFlatAffineSectionBassDiagram_toPoint_isHomotopyConnectedMap
    (i : ℕ) (R : CommRingCat.{u}) (n : ℕ) :
    IsHomotopyConnectedMap (ContinuousMap.const
      (((boundedFlatAffineSectionBassDiagram i).obj R).space (n + i + 2))
      (PUnit.unit : PUnit.{u + 2})) (n + 2) :=
  isHomotopyConnectedMap_const_of_vanishing
    (((boundedFlatAffineSectionBassDiagram i).obj R).point (n + i + 2)) (n + 2)
    (fun x k hk ↦ boundedFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_at
      i R n k hk x)

/-- Any original map between stage-i models has a proved finite bound at the unchanged level. -/
theorem boundedFlatAffineSectionBassDiagram_map_isHomotopyConnectedMap
    (i : ℕ) (R S : CommRingCat.{u})
    (f : (boundedFlatAffineSectionBassDiagram i).obj R ⟶
      (boundedFlatAffineSectionBassDiagram i).obj S) (n : ℕ) :
    IsHomotopyConnectedMap (f.map (n + i + 2)) (n + 1) := by
  let := pathConnectedSpace_of_subsingleton_pi_zero
    (((boundedFlatAffineSectionBassDiagram i).obj S).point (n + i + 2))
    (boundedFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_at i S n 0 (by omega) _)
  exact isHomotopyConnectedMap_of_vanishing (f.map (n + i + 2))
    (((boundedFlatAffineSectionBassDiagram i).obj R).point (n + i + 2)) (n + 1)
    (fun x k hk ↦ boundedFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_at
      i R n k (by omega) x)
    (fun y k hk ↦ boundedFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_at
      i S n k (by omega) y)

/-- The original iterated seed transition itself has increasing finite connectivity; source
and successor target bounds are both discharged at the displayed higher cutoff. -/
theorem boundedFlatAffineSectionBassTransition_isHomotopyConnectedMap
    (i : ℕ) (R : CommRingCat.{u}) (n : ℕ) :
    IsHomotopyConnectedMap
      (((boundedFlatAffineSectionBassTransition i).app R).map (n + i + 3)) (n + 1) := by
  let := pathConnectedSpace_of_subsingleton_pi_zero
    (((boundedFlatAffineSectionBassDiagram (i + 1)).obj R).point (n + i + 3))
    (boundedFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_of_le
      (i + 1) R (n + i + 3) (by omega) 0 (by omega) _)
  exact isHomotopyConnectedMap_of_vanishing
    (((boundedFlatAffineSectionBassTransition i).app R).map (n + i + 3))
    (((boundedFlatAffineSectionBassDiagram i).obj R).point (n + i + 3)) (n + 1)
    (fun x k hk ↦ boundedFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_of_le
      i R (n + i + 3) (by omega) k (by omega) x)
    (fun y k hk ↦ boundedFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_of_le
      (i + 1) R (n + i + 3) (by omega) k (by omega) y)

end Quillen.PerfectComplexes
