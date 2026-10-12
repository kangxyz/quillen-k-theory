/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionOpenDiagram

/-!
# Consumers of original relative-open coefficient maps

The specified coefficient and open-side maps, original section functor, inherited zero,
cofibrations, relative weak maps, pushouts and structure time all remain explicit.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.Scheme.AffineOpenPair
universe u
namespace Quillen.Tests.SectionOpenCoefficient
open PerfectComplexes
variable {R S : CommRingCat.{u}} {U V : Scheme.{u}}
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f)

/-- The constructed Model arrow uses the unchanged original coefficient section functor. -/
theorem originalFunctor :
    (boundedFlatAffineSectionOpenReindexModelMap j j' f l h).functor =
      boundedFlatAffineSectionsMap f := rfl

include l h in
/-- The same actual reindexing retains the original chosen section zeros literally. -/
theorem originalZero :
    (boundedFlatAffineSectionsMap f).obj (boundedFlatAffineSectionOpenWaldhausen j).zero =
      (boundedFlatAffineSectionOpenWaldhausen j').zero :=
  (boundedFlatAffineSectionOpenReindexModelMap j j' f l h).zero

include l h in
/-- The original coefficient image of a specified actual cofibration is still a cofibration. -/
theorem originalCofibration {A B : BoundedFlatAffineSections R} (i : A ⟶ B)
    (hi : (boundedFlatAffineSectionOpenWaldhausen j).cof i) :
    (boundedFlatAffineSectionOpenWaldhausen j').cof ((boundedFlatAffineSectionsMap f).map i) :=
  (boundedFlatAffineSectionsMap_open_exact j j' f l h).cofibration i hi

include l h in
/-- Actual relative-open weakness is preserved under the original arbitrary open-pair square. -/
theorem originalWeakMap {A B : BoundedFlatAffineSections R} (i : A ⟶ B)
    (hi : (boundedFlatAffineSectionOpenWaldhausen j).weq i) :
    (boundedFlatAffineSectionOpenWaldhausen j').weq ((boundedFlatAffineSectionsMap f).map i) :=
  (boundedFlatAffineSectionsMap_open_exact j j' f l h).weak i hi

include l h in
/-- The original four coefficient images preserve the specified cofibration pushout square. -/
theorem originalPushout {A B D P : BoundedFlatAffineSections R}
    (i : A ⟶ B) (k : A ⟶ D) (g : B ⟶ P) (q : D ⟶ P)
    (hi : (boundedFlatAffineSectionOpenWaldhausen j).cof i) (hp : IsPushout i k g q) :
    IsPushout ((boundedFlatAffineSectionsMap f).map i) ((boundedFlatAffineSectionsMap f).map k)
      ((boundedFlatAffineSectionsMap f).map g) ((boundedFlatAffineSectionsMap f).map q) :=
  (boundedFlatAffineSectionsMap_open_exact j j' f l h).pushout hi hp

/-- The original structure-time coordinate survives the actual coarse coefficient map. -/
theorem originalStructureTime (n : ℕ) (t : unitInterval)
    (x : (prespectrum (boundedFlatAffineSectionOpenModel j)).space n) :
    (boundedFlatAffineSectionOpenReindexPrespectrumMap j j' f l h).map (n + 1)
        ((prespectrum (boundedFlatAffineSectionOpenModel j)).structureMap n x t) =
      (prespectrum (boundedFlatAffineSectionOpenModel j')).structureMap n
        ((boundedFlatAffineSectionOpenReindexPrespectrumMap j j' f l h).map n x) t :=
  congrArg (fun γ => γ t)
    ((boundedFlatAffineSectionOpenReindexPrespectrumMap j j' f l h).comm n x)

/-- Each fixed-pullback component of the natural arrow is the original change of weaknesses. -/
theorem originalDiagramComponent (a : Under R) :
    (boundedFlatAffineSectionOpenPrespectrumTransformation j).app a =
      boundedFlatAffineSectionOpenPrespectrumMap (inclusion j a) :=
  boundedFlatAffineSectionOpenPrespectrumTransformation_app j a

end Quillen.Tests.SectionOpenCoefficient
