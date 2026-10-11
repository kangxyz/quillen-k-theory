/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassTelescopeExcision
public import Quillen.Topology.Prespectrum.ConeStableNaturality

/-!
# Original Bass telescope cone boundaries on coefficient squares

Every original commuting coefficient square induces the unchanged strict cone map and preserves
its signed boundary. Genuine telescope excision has already been discharged for both rows.
Stable equivalences on the two original sides consequently induce a stable cone equivalence.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {A B : Arrow CommRingCat.{u}} (sq : A ⟶ B)

/-- The original coefficient square on the actual strict Bass telescopes. -/
def boundedFlatAffineSectionBassTelescopeSquare :
    Arrow.mk (boundedFlatAffineSectionBassTelescopeMap A.hom) ⟶
      Arrow.mk (boundedFlatAffineSectionBassTelescopeMap B.hom) :=
  boundedFlatAffineSectionBassTelescopeFunctor.mapArrow.map sq

/-- The unchanged cone map induced by the original telescope coefficient square. -/
def boundedFlatAffineSectionBassTelescopeConeMap :
    mappingCone (boundedFlatAffineSectionBassTelescopeMap A.hom) ⟶
      mappingCone (boundedFlatAffineSectionBassTelescopeMap B.hom) :=
  mappingConeMap (boundedFlatAffineSectionBassTelescopeSquare sq)

/-- The actual signed telescope boundary is natural for every original coefficient square. -/
@[reassoc] theorem boundedFlatAffineSectionBassTelescopeConeConnecting_naturality (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map
        (boundedFlatAffineSectionBassTelescopeConeMap sq) ≫
      boundedFlatAffineSectionBassTelescopeConeConnecting B.hom d =
        boundedFlatAffineSectionBassTelescopeConeConnecting A.hom d ≫
          (stableHomotopyFunctor d).map (boundedFlatAffineSectionBassTelescopeMap sq.left) :=
  stableMappingConeConnecting_naturality (boundedFlatAffineSectionBassTelescopeSquare sq)
    (boundedFlatAffineSectionBassTelescope_coneFiber_isStableEquivalence A.hom)
    (boundedFlatAffineSectionBassTelescope_coneFiber_isStableEquivalence B.hom) d

/-- Stable original telescope side maps induce a stable unchanged cone map. -/
theorem boundedFlatAffineSectionBassTelescopeConeMap_isStableEquivalence
    (hl : IsStableEquivalence (boundedFlatAffineSectionBassTelescopeMap sq.left))
    (hr : IsStableEquivalence (boundedFlatAffineSectionBassTelescopeMap sq.right)) :
    IsStableEquivalence (boundedFlatAffineSectionBassTelescopeConeMap sq) :=
  mappingConeMap_isStableEquivalence_of_excision
    (boundedFlatAffineSectionBassTelescopeSquare sq)
    (boundedFlatAffineSectionBassTelescope_coneFiber_isStableEquivalence A.hom)
    (boundedFlatAffineSectionBassTelescope_coneFiber_isStableEquivalence B.hom) hl hr

end Quillen.PerfectComplexes
