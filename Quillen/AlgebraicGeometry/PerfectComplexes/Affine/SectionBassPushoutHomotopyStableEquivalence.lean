/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Bass.ModelPushoutHomotopyStableEquivalence
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassDiagram

/-!
# Whole-track reduced-pushout stable preservation for actual affine Bass stages

The genuine original section model diagram specializes the general model-stage proof to the
literal polynomial/Laurent Bass iterates. Both supplied square tracks and the exact existing
mapOfHomotopies are retained. All point-set, growth and intermediate row-excision assumptions
are discharged; only the three original stable corner maps remain as mathematical premises.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable (i j : ℕ) (R S T R' S' T' : CommRingCat.{u})
  (f : (boundedFlatAffineSectionBassDiagram i).obj R ⟶
    (boundedFlatAffineSectionBassDiagram i).obj S)
  (g : (boundedFlatAffineSectionBassDiagram i).obj R ⟶
    (boundedFlatAffineSectionBassDiagram i).obj T)
  (f' : (boundedFlatAffineSectionBassDiagram j).obj R' ⟶
    (boundedFlatAffineSectionBassDiagram j).obj S')
  (g' : (boundedFlatAffineSectionBassDiagram j).obj R' ⟶
    (boundedFlatAffineSectionBassDiagram j).obj T')
  (a : (boundedFlatAffineSectionBassDiagram i).obj R ⟶
    (boundedFlatAffineSectionBassDiagram j).obj R')
  (b : (boundedFlatAffineSectionBassDiagram i).obj S ⟶
    (boundedFlatAffineSectionBassDiagram j).obj S')
  (c : (boundedFlatAffineSectionBassDiagram i).obj T ⟶
    (boundedFlatAffineSectionBassDiagram j).obj T')
  (Hf : Homotopy (f ≫ b) (a ≫ f')) (Hg : Homotopy (g ≫ c) (a ≫ g'))

/-- Original stable Bass-stage corner maps preserve the unchanged whole-track pushout map. -/
theorem boundedFlatAffineSectionBass_wholeTrackPushout_isStableEquivalence
    (ha : IsStableEquivalence a) (hb : IsStableEquivalence b) (hc : IsStableEquivalence c) :
    IsStableEquivalence (HomotopyPushout.mapOfHomotopies f g f' g' a b c Hf Hg) :=
  KTheory.Bass.modelDiagramIterate_pushoutMapOfHomotopies_isStableEquivalence
    CommRingCat.PolynomialLaurent.laurentSquareFunctor i j
    boundedFlatAffineSectionModelFunctor boundedFlatAffineSectionModelFunctor
    R S T R' S' T' f g f' g' a b c Hf Hg ha hb hc

end Quillen.PerfectComplexes
