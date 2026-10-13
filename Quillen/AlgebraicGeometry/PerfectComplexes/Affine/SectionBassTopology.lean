/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassTelescope
public import Quillen.KTheory.Bass.StrictDiagramTopology
public import Quillen.Waldhausen.SConstruction.Iterated.PointHEP
public import Quillen.Topology.Prespectrum.TelescopeSeparation

/-!
# Separation and well-basedness of every actual section Bass stage

Every original section S-prespectrum level is T1 and has HEP at its literal chosen point,
including the degree-zero loop space. The actual strict Bass iteration propagates both
properties without extra premises at later stages. The actual reduced telescope is T1.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes

/-- All original section S-levels, including zero, are T1. -/
instance boundedFlatAffineSectionPrespectrumSpaceT1Space (R : CommRingCat.{u}) (k : ℕ) :
    T1Space ((boundedFlatAffineSectionPrespectrumFunctor.obj R).space k) :=
  Waldhausen.IteratedS.prespectrumSpaceT1Space (boundedFlatAffineSectionModel R) k

/-- Every original section S-point has genuine HEP, including its literal zero-level loop. -/
theorem boundedFlatAffineSectionPrespectrum_point_homotopyExtensionProperty
    (R : CommRingCat.{u}) (k : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      ((boundedFlatAffineSectionPrespectrumFunctor.obj R).point k))) :=
  Waldhausen.IteratedS.prespectrum_point_homotopyExtensionProperty
    (boundedFlatAffineSectionModel R) k

/-- Every actual Bass stage and every original level has T1 separation, with no extra premise. -/
instance boundedFlatAffineSectionBassDiagramSpaceT1Space (i : ℕ) (R : CommRingCat.{u})
    (k : ℕ) : T1Space (((boundedFlatAffineSectionBassDiagram i).obj R).space k) :=
  KTheory.Bass.strictDiagramIterateSpaceT1Space PolynomialBaseChange.laurentSquareFunctor i
    boundedFlatAffineSectionPrespectrumFunctor R k

/-- Every chosen point at every iterated stage remains genuinely well-based. -/
theorem boundedFlatAffineSectionBassDiagram_point_homotopyExtensionProperty
    (i : ℕ) (R : CommRingCat.{u}) (k : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      (((boundedFlatAffineSectionBassDiagram i).obj R).point k))) :=
  KTheory.Bass.strictDiagramIterate_point_homotopyExtensionProperty
    PolynomialBaseChange.laurentSquareFunctor i boundedFlatAffineSectionPrespectrumFunctor
    boundedFlatAffineSectionPrespectrum_point_homotopyExtensionProperty R k

/-- The unchanged reduced Bass telescope is T1 at every original level. -/
instance boundedFlatAffineSectionBassTelescopeSpaceT1Space (R : CommRingCat.{u}) (k : ℕ) :
    T1Space ((boundedFlatAffineSectionBassTelescope R).space k) :=
  Telescope.spaceT1Space (fun i ↦ (boundedFlatAffineSectionBassDiagram i).obj R)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).app R) k

end Quillen.PerfectComplexes
