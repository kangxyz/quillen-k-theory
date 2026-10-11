/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.ConeFiberConnectivity
public import Quillen.Topology.Prespectrum.StableConnectivity
public import Quillen.Waldhausen.SConstruction.Iterated.FiniteConnectivity
public import Quillen.Waldhausen.SConstruction.Iterated.PointHEP

/-!
# Genuine stable cone-to-fiber excision for original iterated-S maps

Every original map between actual S-models has an unchanged mapping-cone-to-fiber comparison
which is a stable equivalence. The finite bound is `2*n` at level `n+1`: actual connected Omega
S-model growth supplies the two attaching-map bounds, literal vertex/loop-point HEP supplies
reduced collapse, and the actual signed stable colimits supply stabilization. No connectivity,
well-basedness or stable-excision premise remains for these original models.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum
universe u v
namespace Quillen.Waldhausen.IteratedS

/-- The original cone gap between actual S-models has the unconditional doubled finite range. -/
theorem prespectrum_mappingConeFiberComparison_isHomotopyConnectedMap {W V : Model.{u}}
    (f : prespectrum W ⟶ prespectrum V) (n : ℕ) :
    IsHomotopyConnectedMap ((mappingConeFiberComparison f).map (n + 1)) (2 * n) :=
  mappingConeFiberComparison_level_isHomotopyConnectedMap f (n + 1)
    (prespectrum_point_homotopyExtensionProperty W (n + 1))
    (prespectrum_point_homotopyExtensionProperty V (n + 1)) n (n + 1) (2 * n) (by omega)
    (prespectrum_positiveLevel_isHomotopyConnectedMap f n)
    (prespectrum_positiveLevel_toPoint_isHomotopyConnectedMap W n)

/-- Genuine stable excision for the unchanged cone-to-fiber comparison of original S-models. -/
theorem prespectrum_mappingConeFiberComparison_isStableEquivalence {W V : Model.{u}}
    (f : prespectrum W ⟶ prespectrum V) : IsStableEquivalence (mappingConeFiberComparison f) :=
  isStableEquivalence_of_linearConnectivity (mappingConeFiberComparison f) 0
    (prespectrum_mappingConeFiberComparison_isHomotopyConnectedMap f)

/-- The literal original small-model map satisfies finite excision in its exact universe. -/
theorem originalPrespectrum_mappingConeFiberComparison_isHomotopyConnectedMap
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (W : Structure C) (V : Structure D) (f : originalPrespectrum W ⟶ originalPrespectrum V)
    (n : ℕ) :
    IsHomotopyConnectedMap ((mappingConeFiberComparison f).map (n + 1)) (2 * n) :=
  prespectrum_mappingConeFiberComparison_isHomotopyConnectedMap f n

/-- Stable excision retains the original arrow and all signed stable degrees without assumptions. -/
theorem originalPrespectrum_mappingConeFiberComparison_isStableEquivalence
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (W : Structure C) (V : Structure D) (f : originalPrespectrum W ⟶ originalPrespectrum V) :
    IsStableEquivalence (mappingConeFiberComparison f) :=
  prespectrum_mappingConeFiberComparison_isStableEquivalence f

end Quillen.Waldhausen.IteratedS
