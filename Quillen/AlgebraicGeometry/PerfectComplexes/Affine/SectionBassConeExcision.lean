/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassConnectivity
public import Quillen.Topology.Prespectrum.ConeFiberConnectivity
public import Quillen.Topology.Prespectrum.StableConnectivity

/-!
# Genuine cone excision for all actual finite section Bass iterates

For an unchanged arrow from stage i over R to stage j over S, the proved all-point connectivity
bounds and original point HEP give finite cone excision at level n+max(i,j)+2 with range 2*n+2.
The genuine eventual signed-colimit criterion then proves stable excision, including arbitrary
negative degrees. The source and the complete original cone-cylinder path remain unchanged.
No growth or excision assumption remains, and low levels below the cutoff are not constrained.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable (i j : ℕ) (R S : CommRingCat.{u})
  (f : (boundedFlatAffineSectionBassDiagram i).obj R ⟶
    (boundedFlatAffineSectionBassDiagram j).obj S)

/-- Original maps between any two actual finite stages have genuine finite cone excision. -/
theorem boundedFlatAffineSectionBass_map_coneFiber_isHomotopyConnectedMap (n : ℕ) :
    IsHomotopyConnectedMap ((mappingConeFiberComparison f).map (n + max i j + 2))
      (2 * n + 2) := by
  have hX (x : ((boundedFlatAffineSectionBassDiagram i).obj R).space (n + max i j + 2))
      (k : ℕ) (hk : k < n + 2) : Subsingleton (HomotopyGroup.Pi k
        (((boundedFlatAffineSectionBassDiagram i).obj R).space (n + max i j + 2)) x) :=
    boundedFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_of_le
      i R (n + max i j + 2) (by omega) k (by omega) x
  have hY (y : ((boundedFlatAffineSectionBassDiagram j).obj S).space (n + max i j + 2))
      (k : ℕ) (hk : k < n + 2) : Subsingleton (HomotopyGroup.Pi k
        (((boundedFlatAffineSectionBassDiagram j).obj S).space (n + max i j + 2)) y) :=
    boundedFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_of_le
      j S (n + max i j + 2) (by omega) k (by omega) y
  let := pathConnectedSpace_of_subsingleton_pi_zero
    (((boundedFlatAffineSectionBassDiagram j).obj S).point (n + max i j + 2))
    (hY _ 0 (by omega))
  apply mappingConeFiberComparison_level_isHomotopyConnectedMap f (n + max i j + 2)
    (boundedFlatAffineSectionBassDiagram_point_homotopyExtensionProperty i R _)
    (boundedFlatAffineSectionBassDiagram_point_homotopyExtensionProperty j S _)
    (n + 1) (n + 2) (2 * n + 2) (by omega)
  · exact isHomotopyConnectedMap_of_vanishing (f.map (n + max i j + 2))
      (((boundedFlatAffineSectionBassDiagram i).obj R).point (n + max i j + 2)) (n + 1)
      (fun x k hk ↦ hX x k (by omega)) (fun y k hk ↦ hY y k (by omega))
  · exact isHomotopyConnectedMap_const_of_vanishing
      (((boundedFlatAffineSectionBassDiagram i).obj R).point (n + max i j + 2)) (n + 2) hX

/-- Every original arrow between actual finite Bass stages has stable cone-to-fiber excision. -/
theorem boundedFlatAffineSectionBass_map_coneFiber_isStableEquivalence :
    IsStableEquivalence (mappingConeFiberComparison f) := by
  apply isStableEquivalence_of_eventually_linearConnectivity (mappingConeFiberComparison f)
    (max i j + 1) (2 * max i j)
  intro n hn
  have h := boundedFlatAffineSectionBass_map_coneFiber_isHomotopyConnectedMap
    i j R S f (n - (max i j + 1))
  rw [show n - (max i j + 1) + max i j + 2 = n + 1 by omega,
    show 2 * (n - (max i j + 1)) + 2 = 2 * n - 2 * max i j by omega] at h
  exact h

/-- Every unchanged coefficient arrow at each actual finite Bass stage has stable cone excision.
-/
theorem boundedFlatAffineSectionBass_coefficient_coneFiber_isStableEquivalence
    (i : ℕ) {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsStableEquivalence
      (mappingConeFiberComparison ((boundedFlatAffineSectionBassDiagram i).map f)) :=
  boundedFlatAffineSectionBass_map_coneFiber_isStableEquivalence
    i i R S ((boundedFlatAffineSectionBassDiagram i).map f)

/-- The actual iterated Laurent seed between consecutive stages also has genuine stable excision.
-/
theorem boundedFlatAffineSectionBass_transition_coneFiber_isStableEquivalence
    (i : ℕ) (R : CommRingCat.{u}) :
    IsStableEquivalence
      (mappingConeFiberComparison ((boundedFlatAffineSectionBassTransition i).app R)) :=
  boundedFlatAffineSectionBass_map_coneFiber_isStableEquivalence
    i (i + 1) R R ((boundedFlatAffineSectionBassTransition i).app R)

end Quillen.PerfectComplexes
