/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTerminalChosenCubes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTargetCylinderNative

/-! Both coefficient-end pairs of original chosen cubes enter one fixed reference carrier. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedCoefficientCubeFaces
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassSeedTerminalCarrierMap
open LaurentUnitReferenceSpecialization (commonUnit)
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
local notation "pa" => CategoryTheory.NatTrans.app (polynomialUnderCoefficient R) a
local notation "qa" => CategoryTheory.NatTrans.app (underToLaurentInvert R) a
local notation "lf" => CategoryTheory.Functor.map (laurentUnderFunctor R) f

/-- The source coefficient end uses the original moving chart square and target contraction. -/
def sourceMap : C(CoefficientBassPositiveC0CarrierSeed.Carrier P pa qa,
    targetCarrier P f (underToLaurentInvert R)) :=
  CoefficientBassSeedTargetCylinderMap.map P lf (polynomialReference P pa qa)
    (laurentReference P pa qa) (ordinaryAnchor P pa qa)
    (commonUnit P pa qa ≪≫ ordinaryAnchor P pa qa)

/-- The source lift recovers the actual full Bass action after the original support inclusion. -/
theorem sourceMap_full_native (n : ℕ)
    (z : CoefficientBassPositiveC0CarrierSeed.Carrier P pa qa)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen
      (Scheme.BaseChange.Coefficients.space (op P, a))))).space n) :
    (boundedFlatCoefficientBassConeMap P lf).map n
      ((boundedFlatCoefficientBassPositiveConeInclusion P ((laurentUnderFunctor R).obj a)).map n
        (CutOpenCarrier.nativeEval (polynomialReference P pa qa)
          (CoefficientBassSeedTargetChartAttachment.Ja P
            (a := (laurentUnderFunctor R).obj a))
          (laurentReference P pa qa) (ordinaryAnchor P pa qa)
          (commonUnit P pa qa ≪≫ ordinaryAnchor P pa qa) n z x)) =
    (boundedFlatCoefficientBassPositiveConeInclusion P ((laurentUnderFunctor R).obj b)).map n
      (CoefficientBassSeedTargetCylinderNative.evaluate P lf (polynomialReference P pa qa)
        (laurentReference P pa qa) (ordinaryAnchor P pa qa)
        (commonUnit P pa qa ≪≫ ordinaryAnchor P pa qa) n (sourceMap P f z) x) :=
  CoefficientBassSeedTargetCylinderNative.map_full_native P lf
    (polynomialReference P pa qa) (laurentReference P pa qa) (ordinaryAnchor P pa qa)
    (commonUnit P pa qa ≪≫ ordinaryAnchor P pa qa) n z x

/-- The positive source cube retains its original full reference transport. -/
def sourcePositiveMap : C(CoefficientBassPositiveC0CarrierSeed.Carrier P
    pa ((underToLaurent R).app a), targetCarrier P f (underToLaurentInvert R)) :=
  ⟨fun y ↦ sourceMap P f (CoefficientBassNegativeActualRightRoute.transport P a y),
    (sourceMap P f).continuous.comp
      (CoefficientBassNegativeActualRightRoute.transport P a).continuous⟩

/-- The unchanged positive source cube is followed by the actual coefficient action lift. -/
def sourcePositiveCube : C((I × I) × I, targetCarrier P f (underToLaurentInvert R)) :=
  (sourcePositiveMap P f).comp (CoefficientBassPositiveActualMixedFiller.boundary P a).carrier

/-- The unchanged negative source cube is followed by the same actual coefficient action lift. -/
def sourceNegativeCube : C((I × I) × I, targetCarrier P f (underToLaurentInvert R)) :=
  (sourceMap P f).comp (CoefficientBassNegativeActualMixedFiller.boundary P a).carrier

/-- Every original positive source face retains its three extension coordinates. -/
theorem source_positive_face (i : Fin 3 × Bool) (z : Quillen.SimplexCubeExtension.face i) :
    sourcePositiveMap P f
      ((CoefficientBassPositiveActualMixedFiller.boundary P a).extension z.val.val) =
    sourcePositiveMap P f ((CoefficientBassPositiveActualMixedFiller.boundary P a).faces i z) :=
  congrArg (sourcePositiveMap P f)
    ((CoefficientBassPositiveActualMixedFiller.boundary P a).extension_face i z)

/-- Every original negative source face retains its three extension coordinates. -/
theorem source_negative_face (i : Fin 3 × Bool) (z : Quillen.SimplexCubeExtension.face i) :
    sourceMap P f ((CoefficientBassNegativeActualMixedFiller.boundary P a).extension z.val.val) =
      sourceMap P f ((CoefficientBassNegativeActualMixedFiller.boundary P a).faces i z) :=
  congrArg (sourceMap P f)
    ((CoefficientBassNegativeActualMixedFiller.boundary P a).extension_face i z)

/-- The shared source J0 face agrees as a whole scalar surface before native evaluation. -/
theorem source_shared_j0 (r s : I) :
    sourcePositiveMap P f (CoefficientBassPositiveJ0Conjugation.reverseComparison P a (r, s)) =
      sourceMap P f (CoefficientBassNegativeActualRightRoute.j0 P a (r, s)) :=
  (congrArg (sourceMap P f)
    (CoefficientBassNegativeActualRightRoute.j0_apply P a r s)).symm

/-- Both coefficient ends retain the same minus tip, without identifying it with the plus tip. -/
theorem minus_tip_intersection :
    sourceMap P f (CoefficientBassPositiveC0CarrierSeed.minusTip P pa qa) =
      carrierMap P f (underToLaurentInvert R)
        (CoefficientBassPositiveC0CarrierSeed.minusTip P
          ((polynomialUnderCoefficient R).app b) ((underToLaurentInvert R).app b)) := by
  have hs := CoefficientBassSeedTargetCylinderMap.map_tipMinus P lf
    (polynomialReference P pa qa) (laurentReference P pa qa) (ordinaryAnchor P pa qa)
    (commonUnit P pa qa ≪≫ ordinaryAnchor P pa qa)
  have hp := CutOpenPrecomp.map_tipMinus (BassMWholeNerve.coefficientModel P f)
    (polynomialReference P ((polynomialUnderCoefficient R).app b) ((underToLaurentInvert R).app b))
    (CoefficientBassSeedTargetChartAttachment.Jb P (b := (laurentUnderFunctor R).obj b))
    (laurentReference P ((polynomialUnderCoefficient R).app b) ((underToLaurentInvert R).app b))
    (ordinaryAnchor P ((polynomialUnderCoefficient R).app b) ((underToLaurentInvert R).app b))
    (commonUnit P ((polynomialUnderCoefficient R).app b) ((underToLaurentInvert R).app b) ≪≫
      ordinaryAnchor P ((polynomialUnderCoefficient R).app b) ((underToLaurentInvert R).app b))
  have ht := CoefficientBassSeedTerminalAttachmentMap.map_tipMinus P f (underToLaurentInvert R)
  have hm := congrArg (CoefficientBassSeedTerminalAttachmentMap.map P f
    (underToLaurentInvert R)).hom hp
  exact hs.trans (hm.trans ht).symm

/-- Both coefficient ends independently retain the same plus tip. -/
theorem plus_tip_intersection :
    sourceMap P f (CoefficientBassPositiveC0CarrierSeed.plusTip P pa qa) =
      carrierMap P f (underToLaurentInvert R)
        (CoefficientBassPositiveC0CarrierSeed.plusTip P
          ((polynomialUnderCoefficient R).app b) ((underToLaurentInvert R).app b)) := by
  have hs := CoefficientBassSeedTargetCylinderMap.map_tipPlus P lf
    (polynomialReference P pa qa) (laurentReference P pa qa) (ordinaryAnchor P pa qa)
    (commonUnit P pa qa ≪≫ ordinaryAnchor P pa qa)
  have hp := CutOpenPrecomp.map_tipPlus (BassMWholeNerve.coefficientModel P f)
    (polynomialReference P ((polynomialUnderCoefficient R).app b) ((underToLaurentInvert R).app b))
    (CoefficientBassSeedTargetChartAttachment.Jb P (b := (laurentUnderFunctor R).obj b))
    (laurentReference P ((polynomialUnderCoefficient R).app b) ((underToLaurentInvert R).app b))
    (ordinaryAnchor P ((polynomialUnderCoefficient R).app b) ((underToLaurentInvert R).app b))
    (commonUnit P ((polynomialUnderCoefficient R).app b) ((underToLaurentInvert R).app b) ≪≫
      ordinaryAnchor P ((polynomialUnderCoefficient R).app b) ((underToLaurentInvert R).app b))
  have ht := CoefficientBassSeedTerminalAttachmentMap.map_tipPlus P f (underToLaurentInvert R)
  have hm := congrArg (CoefficientBassSeedTerminalAttachmentMap.map P f
    (underToLaurentInvert R)).hom hp
  exact hs.trans (hm.trans ht).symm

end Quillen.PerfectComplexes.CoefficientBassSeedCoefficientCubeFaces
