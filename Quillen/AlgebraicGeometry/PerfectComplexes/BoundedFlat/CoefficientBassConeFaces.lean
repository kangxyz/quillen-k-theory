/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCoherence
public import Quillen.Topology.Prespectrum.FiberHomotopySquare
/-!
# Coefficient Bass Cone Faces

Identity and composition on the actual Laurent inclusion of the fixed raw Bass cones.
These are whole prespectrum homotopies on the stated face, not laws on the whole cone.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- The original Laurent identity retains the actual geometric and normalization comparison. -/
def boundedFlatCoefficientLaurentIdentityHomotopy (a : Under R) :
    Homotopy
      (boundedFlatPerfectPrespectrumMap
        (coefficientMap P ((laurentUnderFunctor R).map (𝟙 a))))
      (𝟙 (originalPrespectrum (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj a))))) :=
  (boundedFlatCoefficientIdentityHomotopy P ((laurentUnderFunctor R).obj a)).cast
    (congrArg (fun k ↦ boundedFlatPerfectPrespectrumMap (coefficientMap P k))
      ((laurentUnderFunctor R).map_id a)).symm rfl

/-- The actual raw coefficient cone identity has a whole homotopy on its original Laurent face. -/
def boundedFlatCoefficientBassConeIdentityInclusionHomotopy (a : Under R) :
    Homotopy
      (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a) ≫
        boundedFlatCoefficientBassConeMap P (𝟙 a))
      (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)) :=
  ((boundedFlatCoefficientLaurentIdentityHomotopy P a).postcomp
    (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))).cast
    (boundedFlatCoefficientBassConeMap_inclusion P (𝟙 a)).symm (Category.id_comp _)

variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- Original coefficient composition gives a whole comparison on the literal Laurent inclusion. -/
def boundedFlatCoefficientBassConeCompositionInclusionHomotopy :
    Homotopy
      (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a) ≫
        boundedFlatCoefficientBassConeMap P (u ≫ v))
      (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a) ≫
        (boundedFlatCoefficientBassConeMap P u ≫ boundedFlatCoefficientBassConeMap P v)) :=
  ((boundedFlatCoefficientLaurentCompositionHomotopy P u v).postcomp
    (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P c))).cast
    (boundedFlatCoefficientBassConeMap_inclusion P (u ≫ v)).symm (by
      symm
      calc
        _ = (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a) ≫
            boundedFlatCoefficientBassConeMap P u) ≫ boundedFlatCoefficientBassConeMap P v :=
          (Category.assoc _ _ _).symm
        _ = (boundedFlatPerfectPrespectrumMap
              (coefficientMap P ((laurentUnderFunctor R).map u)) ≫
            mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P b)) ≫
            boundedFlatCoefficientBassConeMap P v := by
          rw [boundedFlatCoefficientBassConeMap_inclusion]
        _ = boundedFlatPerfectPrespectrumMap
              (coefficientMap P ((laurentUnderFunctor R).map u)) ≫
            (boundedFlatPerfectPrespectrumMap
                (coefficientMap P ((laurentUnderFunctor R).map v)) ≫
              mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P c)) := by
          rw [Category.assoc, boundedFlatCoefficientBassConeMap_inclusion]
        _ = _ := (Category.assoc _ _ _).symm)

/-- Parameter looping keeps the identity comparison on the actual original Raw₁ Laurent face. -/
def boundedFlatCoefficientBassStepIdentityInclusionHomotopy (a : Under R) :
    Homotopy
      (parameterLoopingMap (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)) ≫
        boundedFlatCoefficientBassStepMap P (𝟙 a))
      (parameterLoopingMap (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P
          a))) :=
  (boundedFlatCoefficientBassConeIdentityInclusionHomotopy P a).parameterLooping.cast
    (parameterLoopingFunctor.map_comp _ _) rfl

/-- The original cone-face composition comparison loops without identifying any time parameters. -/
def boundedFlatCoefficientBassStepCompositionInclusionHomotopy :
    Homotopy
      (parameterLoopingMap (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)) ≫
        boundedFlatCoefficientBassStepMap P (u ≫ v))
      (parameterLoopingMap (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)) ≫
        (boundedFlatCoefficientBassStepMap P u ≫ boundedFlatCoefficientBassStepMap P v)) :=
  (boundedFlatCoefficientBassConeCompositionInclusionHomotopy P u v).parameterLooping.cast
    (parameterLoopingFunctor.map_comp _ _) (by
      change parameterLoopingFunctor.map (_ ≫ (_ ≫ _)) = _
      rw [Functor.map_comp, Functor.map_comp]
      rfl)

/-- The exact direct raw map's original full cone nullhomotopy. -/
def boundedFlatCoefficientBassDirectConeNullTrack :=
  ((mappingConeHomotopy (boundedFlatCoefficientBassSquareComparison P a)).postcomp
    (boundedFlatCoefficientBassConeMap P (u ≫ v))).cast (Category.assoc _ _ _)
    (zeroHom_comp _)

/-- The actual composite raw map's original full cone nullhomotopy. -/
def boundedFlatCoefficientBassCompositeConeNullTrack :=
  ((mappingConeHomotopy (boundedFlatCoefficientBassSquareComparison P a)).postcomp
    (boundedFlatCoefficientBassConeMap P u ≫ boundedFlatCoefficientBassConeMap P v)).cast
    (Category.assoc _ _ _) (zeroHom_comp _)

/-- This is precisely the remaining moving nullhomotopy square for the fixed pair of raw maps.
It is a type of required data, not a claim that these data have been constructed. -/
abbrev BoundedFlatCoefficientBassCompositionNullSquare :=
  (boundedFlatCoefficientBassDirectConeNullTrack P u v).Square
    (boundedFlatCoefficientBassCompositeConeNullTrack P u v)
    (Homotopy.precomp (boundedFlatCoefficientBassSquareComparison P a)
      (boundedFlatCoefficientBassConeCompositionInclusionHomotopy P u v))
    (Quillen.LoopPrespectrum.Homotopy.refl (zeroHom
      (HomotopyPushout.prespectrum
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)))
      (mappingCone (boundedFlatCoefficientBassSquareComparison P c))))

end Quillen.PerfectComplexes
