/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionModelTargetTrack
public import Quillen.Topology.Prespectrum.RelativeHomotopyHorizontal
public import Quillen.Topology.Prespectrum.RelativeHomotopyWhiskering
public import Quillen.Topology.Prespectrum.RelativeHomotopyLevels

/-!
# Composition of the original geometric evaluation tracks

The unchanged evaluation homotopies satisfy the two-route composition comparison with the
original split geometric composition homotopy. All endpoint transports remain explicit.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes

/-- The original evaluation comparison followed by total normalized geometric composition. -/
def boundedFlatAffineSectionCoefficientTotalRoute
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    Homotopy
      (boundedFlatAffineSectionPrespectrumFunctor.map (f ≫ g) ≫
        boundedFlatAffineSectionEvaluationPrespectrumMap T)
      ((boundedFlatAffineSectionEvaluationPrespectrumMap R ≫
        boundedFlatPerfectPrespectrumMap (Spec.map f)) ≫
          boundedFlatPerfectPrespectrumMap (Spec.map g)) :=
  ((boundedFlatAffineSectionEvaluationCoefficientHomotopy (f ≫ g)).trans
    (Homotopy.precomp (boundedFlatAffineSectionEvaluationPrespectrumMap R)
      ((boundedFlatNormalizedCompTrack (Spec.map g) (Spec.map f)).cast
        (congrArg boundedFlatPerfectPrespectrumMap (Spec.map_comp f g).symm) rfl))).cast
    rfl (Category.assoc _ _ _).symm

/-- The first route retains the existing two-part geometric composition homotopy. -/
def boundedFlatAffineSectionCoefficientSplitRoute
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    Homotopy
      (boundedFlatAffineSectionPrespectrumFunctor.map (f ≫ g) ≫
        boundedFlatAffineSectionEvaluationPrespectrumMap T)
      ((boundedFlatAffineSectionEvaluationPrespectrumMap R ≫
        boundedFlatPerfectPrespectrumMap (Spec.map f)) ≫
          boundedFlatPerfectPrespectrumMap (Spec.map g)) :=
  ((boundedFlatAffineSectionEvaluationCoefficientHomotopy (f ≫ g)).trans
    (Homotopy.precomp (boundedFlatAffineSectionEvaluationPrespectrumMap R)
      ((boundedFlatPerfectPrespectrumCompHomotopy (Spec.map g) (Spec.map f)).cast
        (congrArg boundedFlatPerfectPrespectrumMap (Spec.map_comp f g).symm) rfl))).cast
    rfl (Category.assoc _ _ _).symm

/-- The second route uses the two unchanged coefficient tracks with their actual whiskering. -/
def boundedFlatAffineSectionCoefficientWhiskeredRoute
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    Homotopy
      (boundedFlatAffineSectionPrespectrumFunctor.map (f ≫ g) ≫
        boundedFlatAffineSectionEvaluationPrespectrumMap T)
      ((boundedFlatAffineSectionEvaluationPrespectrumMap R ≫
        boundedFlatPerfectPrespectrumMap (Spec.map f)) ≫
          boundedFlatPerfectPrespectrumMap (Spec.map g)) :=
  ((Homotopy.precomp (boundedFlatAffineSectionPrespectrumFunctor.map f)
    (boundedFlatAffineSectionEvaluationCoefficientHomotopy g)).cast
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ boundedFlatAffineSectionEvaluationPrespectrumMap T)
          (boundedFlatAffineSectionPrespectrumFunctor.map_comp f g).symm))
      (Category.assoc _ _ _).symm).trans
    ((boundedFlatAffineSectionEvaluationCoefficientHomotopy f).postcomp
      (boundedFlatPerfectPrespectrumMap (Spec.map g)))

/-- The original normalization triangle substitutes the existing split geometric track. -/
def boundedFlatAffineSectionCoefficientTotalSplit
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (boundedFlatAffineSectionCoefficientTotalRoute f g).RelHomotopy
      (boundedFlatAffineSectionCoefficientSplitRoute f g) :=
  ((Homotopy.RelHomotopy.refl
    (boundedFlatAffineSectionEvaluationCoefficientHomotopy (f ≫ g))).hcomp
      (Homotopy.RelHomotopy.precomp (boundedFlatAffineSectionEvaluationPrespectrumMap R)
        ((boundedFlatNormalizedCompTrackComparison (Spec.map g) (Spec.map f)).cast
          (congrArg boundedFlatPerfectPrespectrumMap (Spec.map_comp f g).symm) rfl))).cast
    rfl (Category.assoc _ _ _).symm

/-- The genuine Model composition triangle retains the two original total/whiskered routes. -/
def boundedFlatAffineSectionCoefficientTotalWhiskered
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (boundedFlatAffineSectionCoefficientTotalRoute f g).RelHomotopy
      (boundedFlatAffineSectionCoefficientWhiskeredRoute f g) := by
  apply (boundedFlatAffineSectionModelCompositionRelHomotopy f g).ofLevels
  · intro n
    apply Homotopy.trans_level_congr
    · rfl
    · exact (boundedFlatAffineSectionModelTargetHomotopy_level f g n).symm
  · intro n
    apply Homotopy.trans_level_congr
    · exact (boundedFlatAffineSectionModelFirstRouteHomotopy_level f g n).symm
    · exact (boundedFlatAffineSectionModelSecondRouteHomotopy_level f g n).symm

/-- The two original geometric routes are relatively homotopic, with their original tracks. -/
def boundedFlatAffineSectionCoefficientCompositionRelHomotopy
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (boundedFlatAffineSectionCoefficientSplitRoute f g).RelHomotopy
      (boundedFlatAffineSectionCoefficientWhiskeredRoute f g) :=
  (boundedFlatAffineSectionCoefficientTotalSplit f g).symm.trans
    (boundedFlatAffineSectionCoefficientTotalWhiskered f g)

end Quillen.PerfectComplexes
