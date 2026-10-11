/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.ConeFiberComparison
public import Quillen.Topology.HomotopyCofiber.ReducedMappingConeFiniteConnectivity

/-!
# Finite excision for the original prespectrum cone-to-fiber map

The actual prespectrum comparison is literally the reduced cone's original cylinder map.
Consequently finite double-cylinder excision and genuine original point HEP give its levelwise
finite bound. All endpoints and the complete path coordinate are retained.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum
variable {E F : LoopPrespectrum.{u}} (f : E ⟶ F)

/-- The original prespectrum comparison is the literal reduced cylinder, level by level. -/
theorem mappingConeFiberComparison_map_eq (n : ℕ) :
    (mappingConeFiberComparison f).map n =
      ReducedMappingCone.fiberComparison (E.point n) (F.point n) (f.map n) := rfl

/-- The finite original gap range transfers to the actual prespectrum cone fiber comparison. -/
theorem mappingConeFiberComparison_level_isHomotopyConnectedMap (n : ℕ)
    (hE : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (E.point n))))
    (hF : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (F.point n))))
    (p q r : ℕ) (hr : r + 1 ≤ p + q) (hf : IsHomotopyConnectedMap (f.map n) p)
    (hEq : IsHomotopyConnectedMap
      (ContinuousMap.const (E.space n) (PUnit.unit : PUnit.{u + 1})) q) :
    IsHomotopyConnectedMap ((mappingConeFiberComparison f).map n) r := by
  rw [mappingConeFiberComparison_map_eq]
  exact ReducedMappingCone.fiberComparison_isHomotopyConnectedMap (f.map n)
    (E.point n) (F.point n) (f.map_point n) hE hF p q r hr hf hEq

end Quillen.LoopPrespectrum
