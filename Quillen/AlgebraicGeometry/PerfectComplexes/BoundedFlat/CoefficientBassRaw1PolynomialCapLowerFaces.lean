/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialTripleLowerFaces
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCommonSheet

/-!
# Actual polynomial cap lower faces in the fixed common sheet

The three actual input caps and both signs of the three actual postcomposition caps
have their exact Laurent18 lower binary rows in the original common polynomial sheet.
The middle and last maps are the existing full-reference sheet normalizations.
All statements retain arbitrary polynomial inputs and the original binary clock;
no equality is reconstructed from native values and no filler is introduced.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCapLowerFaces
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
open CoefficientBassRaw1PolynomialTripleAnchor CoefficientBassRaw1PolynomialTripleLowerFaces

private theorem reanchor_refl_parameter {V W : Model.{u}} (F : V ⟶ W)
    (y : |parameterSSet F|) :
    mapParameter (CommonReferenceProduct.reanchor (Iso.refl F.functor)) y = y := by
  obtain ⟨k, N, x, rfl⟩ := exists_parameter F y
  rw [mapParameter_parameter]
  apply congrArg (fun M ↦ parameter F M x)
  funext i
  rcases N i with ⟨K, ρ⟩
  simp only [CommonReferenceProduct.reanchor, Iso.refl_trans]

private theorem normalization_iso {V W T : Model.{u}} (F F' : V ⟶ W) (J : W ⟶ T)
    (δ : F'.functor ≅ F.functor) :
    CoefficientBassPolynomialSheetNormalization.laurentIso F F' J (F ≫ J) (Iso.refl _) δ =
      isoWhiskerRight δ J.functor :=
  Iso.trans_refl (isoWhiskerRight δ J.functor)

private theorem normalization_left {V W T : Model.{u}} (F F' : V ⟶ W) (J : W ⟶ T)
    (δ : F'.functor ≅ F.functor) (y : |parameterSSet (F ≫ J)|) :
    CoefficientBassPolynomialSheetNormalization.map F F' J (F ≫ J) (Iso.refl _) δ
      ((SSet.toTop.map (left₀ F J (F ≫ J) (Iso.refl _))).hom y) =
    (SSet.toTop.map (left₀ F' J (F' ≫ J) (Iso.refl _))).hom
      (mapParameter (CommonReferenceProduct.reanchor (isoWhiskerRight δ J.functor)) y) := by
  have h := ConcreteCategory.congr_hom
    (CommonReferenceNerve.CutOpenMap.firstMap_left F J (F ≫ J) F' J (F' ≫ J)
      (Iso.refl _) (Iso.refl _)
      (TopCat.ofHom (mapParameter (CommonReferenceProduct.reanchor δ)))
      (TopCat.ofHom (mapParameter (CommonReferenceProduct.reanchor
        (CoefficientBassPolynomialSheetNormalization.laurentIso F F' J (F ≫ J)
          (Iso.refl _) δ))))
      (CoefficientBassPolynomialSheetNormalization.attachment_square F F' J (F ≫ J)
        (Iso.refl _) δ)) y
  change CoefficientBassPolynomialSheetNormalization.map F F' J (F ≫ J) (Iso.refl _) δ
      ((SSet.toTop.map (left₀ F J (F ≫ J) (Iso.refl _))).hom y) =
    (SSet.toTop.map (left₀ F' J (F' ≫ J) (Iso.refl _))).hom
      (mapParameter (CommonReferenceProduct.reanchor
        (CoefficientBassPolynomialSheetNormalization.laurentIso F F' J (F ≫ J)
          (Iso.refl _) δ)) y) at h
  exact h.trans (congrArg _ (congrArg (fun e ↦ mapParameter
    (CommonReferenceProduct.reanchor e) y) (normalization_iso F F' J δ)))


section Triple
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)

/-- The actual Laurent inclusion in one normalized polynomial triple sheet. -/
def tripleLaurent : C(|parameterSSet (polynomialReference P p q w ≫
    BassMWholeNerve.coefficientModel P (β.app d))|,
    CoefficientBassRaw1PolynomialPostcomp.carrier P p q w β) :=
  (SSet.toTop.map (left₀ (polynomialReference P p q w)
    (BassMWholeNerve.coefficientModel P (β.app d))
    (polynomialReference P p q w ≫ BassMWholeNerve.coefficientModel P (β.app d))
    (Iso.refl _))).hom

private theorem input_lower (r : I) :
    CoefficientBassRaw1PolynomialInputCap.placedFamily P β p q w (r, 0) =
    tripleLaurent P β p q w
      (mapParameter (inputNode P β p q w)
        (CoefficientBassLaurentCompositionCarrier.family P q w r)) := by
  have h := input_lower_parameter P β p q w
    (CoefficientBassLaurentCompositionCarrier.family P q w r)
  exact (input_placed_lower_family P β p q w r).trans (congrArg _ h.symm)

private theorem plus_postcomp_lower (r : I) :
    CoefficientBassRaw1PolynomialPostcomp.plus P p q w
      (CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurent R) p q (r, 0)) =
    tripleLaurent P (underToLaurent R) p q w
      (mapParameter (postcompNodeLower P (underToLaurent R) p q w)
        (CoefficientBassLaurentCompositionCarrier.family P p q r)) := by
  have h := postcomp_lower_parameter P (underToLaurent R) p q w
    (CoefficientBassLaurentCompositionCarrier.family P p q r)
  exact (plus_postcomp_lower_family P p q w r).trans (congrArg _ h.symm)

private theorem minus_postcomp_lower (r : I) :
    CoefficientBassRaw1PolynomialPostcomp.minus P p q w
      (CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurentInvert R) p q (r, 0)) =
    tripleLaurent P (underToLaurentInvert R) p q w
      (mapParameter (postcompNodeLower P (underToLaurentInvert R) p q w)
        (CoefficientBassLaurentCompositionCarrier.family P p q r)) := by
  have h := postcomp_lower_parameter P (underToLaurentInvert R) p q w
    (CoefficientBassLaurentCompositionCarrier.family P p q r)
  exact (minus_postcomp_lower_family P p q w r).trans (congrArg _ h.symm)

end Triple

section Rectangle
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (α β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b : Under R} (f : a ⟶ b)

/-- The actual Laurent inclusion in the one fixed original polynomial triple sheet. -/
def laurent : C(|parameterSSet (targetReference P α β f)|,
    CoefficientBassRaw1PolynomialCommonSheet.carrier P α β f) :=
  (SSet.toTop.map (left₀ (CoefficientBassRaw1PolynomialCommonSheet.reference P α f)
    (CoefficientBassRaw1PolynomialCommonSheet.chart P β (b := b))
    (targetReference P α β f) (Iso.refl _))).hom

/-- The actual first input cap, with both original height variables. -/
def firstInput : C(I × I, CoefficientBassRaw1PolynomialCommonSheet.carrier P α β f) :=
  CoefficientBassRaw1PolynomialInputCap.placedFamily P β ((polynomialUnderCoefficient R).app a)
      (α.app a) ((laurentUnderFunctor R).map f)

/-- The actual first plus postcomp cap, with both original height variables. -/
def firstPlusPostcomp : C(I × I, CoefficientBassRaw1PolynomialCommonSheet.carrier P α
    (underToLaurent R) f) :=
  (CoefficientBassRaw1PolynomialPostcomp.plus P ((polynomialUnderCoefficient R).app a) (α.app a)
      ((laurentUnderFunctor R).map f)).comp
      (CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurent R)
          ((polynomialUnderCoefficient R).app a) (α.app a))

/-- The actual first minus postcomp cap, with both original height variables. -/
def firstMinusPostcomp : C(I × I, CoefficientBassRaw1PolynomialCommonSheet.carrier P α
    (underToLaurentInvert R) f) :=
  (CoefficientBassRaw1PolynomialPostcomp.minus P ((polynomialUnderCoefficient R).app a) (α.app a)
      ((laurentUnderFunctor R).map f)).comp
      (CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurentInvert R)
          ((polynomialUnderCoefficient R).app a) (α.app a))

/-- The actual middle input cap, with both original height variables. -/
def middleInput : C(I × I, CoefficientBassRaw1PolynomialCommonSheet.carrier P α β f) :=
  (CoefficientBassRaw1PolynomialCommonSheet.middleMap P α β f).comp
    (CoefficientBassRaw1PolynomialInputCap.placedFamily P β ((polynomialUnderCoefficient R).app a)
        ((polynomialUnderFunctor R).map f) (α.app b))

/-- The actual middle plus postcomp cap, with both original height variables. -/
def middlePlusPostcomp : C(I × I, CoefficientBassRaw1PolynomialCommonSheet.carrier P α
    (underToLaurent R) f) :=
  (CoefficientBassRaw1PolynomialCommonSheet.middleMap P α (underToLaurent R) f).comp
    ((CoefficientBassRaw1PolynomialPostcomp.plus P ((polynomialUnderCoefficient R).app a)
        ((polynomialUnderFunctor R).map f) (α.app b)).comp
      (CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurent R)
          ((polynomialUnderCoefficient R).app a) ((polynomialUnderFunctor R).map f)))

/-- The actual middle minus postcomp cap, with both original height variables. -/
def middleMinusPostcomp : C(I × I, CoefficientBassRaw1PolynomialCommonSheet.carrier P α
    (underToLaurentInvert R) f) :=
  (CoefficientBassRaw1PolynomialCommonSheet.middleMap P α (underToLaurentInvert R) f).comp
    ((CoefficientBassRaw1PolynomialPostcomp.minus P ((polynomialUnderCoefficient R).app a)
        ((polynomialUnderFunctor R).map f) (α.app b)).comp
      (CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurentInvert R)
          ((polynomialUnderCoefficient R).app a) ((polynomialUnderFunctor R).map f)))

/-- The actual last input cap, with both original height variables. -/
def lastInput : C(I × I, CoefficientBassRaw1PolynomialCommonSheet.carrier P α β f) :=
  (CoefficientBassRaw1PolynomialCommonSheet.lastMap P α β f).comp
    (CoefficientBassRaw1PolynomialInputCap.placedFamily P β (f) ((polynomialUnderCoefficient
        R).app b) (α.app b))

/-- The actual last plus postcomp cap, with both original height variables. -/
def lastPlusPostcomp : C(I × I, CoefficientBassRaw1PolynomialCommonSheet.carrier P α
    (underToLaurent R) f) :=
  (CoefficientBassRaw1PolynomialCommonSheet.lastMap P α (underToLaurent R) f).comp
    ((CoefficientBassRaw1PolynomialPostcomp.plus P (f) ((polynomialUnderCoefficient R).app b)
        (α.app b)).comp
      (CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurent R) (f)
          ((polynomialUnderCoefficient R).app b)))

/-- The actual last minus postcomp cap, with both original height variables. -/
def lastMinusPostcomp : C(I × I, CoefficientBassRaw1PolynomialCommonSheet.carrier P α
    (underToLaurentInvert R) f) :=
  (CoefficientBassRaw1PolynomialCommonSheet.lastMap P α (underToLaurentInvert R) f).comp
    ((CoefficientBassRaw1PolynomialPostcomp.minus P (f) ((polynomialUnderCoefficient R).app b)
        (α.app b)).comp
      (CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurentInvert R) (f)
          ((polynomialUnderCoefficient R).app b)))

/-- The unchanged full Laurent18 row, after source-chart restriction and target reanchoring. -/
def row (face : ⦋7⦌ ⟶ ⦋17⦌) (index : Fin 3 → Fin 8) (r : I) :=
  parameter (targetReference P α β f) (nodes P α β f)
    (StdSimplex.map (fun i ↦ face.toOrderHom (index i)) (binaryPath (k := 2) 0 1 2 r))

/-- The actual middle sheet normalization has the prescribed complete Laurent reference map. -/
theorem middleMap_laurent
    (y : |parameterSSet (polynomialReference P ((polynomialUnderCoefficient R).app a)
        ((polynomialUnderFunctor R).map f) (α.app b) ≫
      BassMWholeNerve.coefficientModel P (β.app ((laurentUnderFunctor R).obj b)))|) :
    CoefficientBassRaw1PolynomialCommonSheet.middleMap P α β f
      (tripleLaurent P β ((polynomialUnderCoefficient R).app a) ((polynomialUnderFunctor R).map f)
          (α.app b) y) =
    laurent P α β f (mapParameter (CommonReferenceProduct.reanchor
      (middleTransport P α β f)) y) := by
  rw [middle_transport]
  exact normalization_left (polynomialReference P ((polynomialUnderCoefficient R).app a)
      ((polynomialUnderFunctor R).map f) (α.app b))
    (CoefficientBassRaw1PolynomialCommonSheet.reference P α f)
    (CoefficientBassRaw1PolynomialCommonSheet.chart P β (b := b))
    (CoefficientBassRaw1PolynomialRectangle.middleAnchor P α f) y

/-- The actual last sheet normalization has the prescribed complete Laurent reference map. -/
theorem lastMap_laurent
    (y : |parameterSSet (polynomialReference P (f) ((polynomialUnderCoefficient R).app b) (α.app
        b) ≫
      BassMWholeNerve.coefficientModel P (β.app ((laurentUnderFunctor R).obj b)))|) :
    CoefficientBassRaw1PolynomialCommonSheet.lastMap P α β f
      (tripleLaurent P β (f) ((polynomialUnderCoefficient R).app b) (α.app b) y) =
    laurent P α β f (mapParameter (CommonReferenceProduct.reanchor
      (lastTransport P α β f)) y) := by
  rw [last_transport]
  exact normalization_left (polynomialReference P (f) ((polynomialUnderCoefficient R).app b)
      (α.app b))
    (CoefficientBassRaw1PolynomialCommonSheet.reference P α f)
    (CoefficientBassRaw1PolynomialCommonSheet.chart P β (b := b))
    (CoefficientBassRaw1PolynomialRectangle.lastAnchor P α f) y

/-- The actual first input cap has its original lower row in the common sheet. -/
theorem first_input_lower (r : I) :
    firstInput P α β f (r, 0) =
    laurent P α β f
      (row P α β f DoubleSquareMergedSimplex.firstFace BassH0Merge.rightIndex r) := by
  let y := mapParameter (inputNode P β ((polynomialUnderCoefficient R).app a) (α.app a)
      ((laurentUnderFunctor R).map f))
    (CoefficientBassLaurentCompositionCarrier.family P (α.app a) ((laurentUnderFunctor R).map f) r)
  have hzero : mapParameter (CommonReferenceProduct.reanchor
      (firstTransport P α β f)) y = y := by
    rw [first_transport]
    exact reanchor_refl_parameter _ y
  exact (input_lower P β ((polynomialUnderCoefficient R).app a) (α.app a) ((laurentUnderFunctor
      R).map f) r).trans
    (congrArg (laurent P α β f)
      (hzero.symm.trans (first_input_family P α β f r)))

/-- The actual first plus postcomp cap has its original lower row in the common sheet. -/
theorem first_plus_postcomp_lower (r : I) :
    firstPlusPostcomp P α f (r, 0) =
    laurent P α (underToLaurent R) f
      (row P α (underToLaurent R) f DoubleSquareMergedSimplex.firstFace BassH0Merge.leftIndex r)
          := by
  let y := mapParameter (postcompNodeLower P (underToLaurent R) ((polynomialUnderCoefficient
      R).app a) (α.app a) ((laurentUnderFunctor R).map f))
    (CoefficientBassLaurentCompositionCarrier.family P ((polynomialUnderCoefficient R).app a)
        (α.app a) r)
  have hzero : mapParameter (CommonReferenceProduct.reanchor
      (firstTransport P α (underToLaurent R) f)) y = y := by
    rw [first_transport]
    exact reanchor_refl_parameter _ y
  exact (plus_postcomp_lower P ((polynomialUnderCoefficient R).app a) (α.app a)
      ((laurentUnderFunctor R).map f) r).trans
    (congrArg (laurent P α (underToLaurent R) f)
      (hzero.symm.trans (first_postcomp_family P α (underToLaurent R) f r)))

/-- The actual first minus postcomp cap has its original lower row in the common sheet. -/
theorem first_minus_postcomp_lower (r : I) :
    firstMinusPostcomp P α f (r, 0) =
    laurent P α (underToLaurentInvert R) f
      (row P α (underToLaurentInvert R) f DoubleSquareMergedSimplex.firstFace
          BassH0Merge.leftIndex r) := by
  let y := mapParameter (postcompNodeLower P (underToLaurentInvert R) ((polynomialUnderCoefficient
      R).app a) (α.app a) ((laurentUnderFunctor R).map f))
    (CoefficientBassLaurentCompositionCarrier.family P ((polynomialUnderCoefficient R).app a)
        (α.app a) r)
  have hzero : mapParameter (CommonReferenceProduct.reanchor
      (firstTransport P α (underToLaurentInvert R) f)) y = y := by
    rw [first_transport]
    exact reanchor_refl_parameter _ y
  exact (minus_postcomp_lower P ((polynomialUnderCoefficient R).app a) (α.app a)
      ((laurentUnderFunctor R).map f) r).trans
    (congrArg (laurent P α (underToLaurentInvert R) f)
      (hzero.symm.trans (first_postcomp_family P α (underToLaurentInvert R) f r)))

/-- The actual middle input cap has its original lower row in the common sheet. -/
theorem middle_input_lower (r : I) :
    middleInput P α β f (r, 0) =
    laurent P α β f
      (row P α β f DoubleSquareMergedSimplex.middleFace BassH0Merge.rightIndex r) := by
  let y := mapParameter (inputNode P β ((polynomialUnderCoefficient R).app a)
      ((polynomialUnderFunctor R).map f) (α.app b))
    (CoefficientBassLaurentCompositionCarrier.family P ((polynomialUnderFunctor R).map f) (α.app
        b) r)
  have hcap := congrArg (CoefficientBassRaw1PolynomialCommonSheet.middleMap P α β f)
    (input_lower P β ((polynomialUnderCoefficient R).app a) ((polynomialUnderFunctor R).map f)
        (α.app b) r)
  exact hcap.trans ((middleMap_laurent P α β f y).trans
    (congrArg (laurent P α β f) (middle_input_family P α β f r)))

/-- The actual middle plus postcomp cap has its original lower row in the common sheet. -/
theorem middle_plus_postcomp_lower (r : I) :
    middlePlusPostcomp P α f (r, 0) =
    laurent P α (underToLaurent R) f
      (row P α (underToLaurent R) f DoubleSquareMergedSimplex.middleFace BassH0Merge.leftIndex r)
          := by
  let y := mapParameter (postcompNodeLower P (underToLaurent R) ((polynomialUnderCoefficient
      R).app a) ((polynomialUnderFunctor R).map f) (α.app b))
    (CoefficientBassLaurentCompositionCarrier.family P ((polynomialUnderCoefficient R).app a)
        ((polynomialUnderFunctor R).map f) r)
  have hcap := congrArg (CoefficientBassRaw1PolynomialCommonSheet.middleMap P α (underToLaurent R)
      f)
    (plus_postcomp_lower P ((polynomialUnderCoefficient R).app a) ((polynomialUnderFunctor R).map
        f) (α.app b) r)
  exact hcap.trans ((middleMap_laurent P α (underToLaurent R) f y).trans
    (congrArg (laurent P α (underToLaurent R) f) (middle_postcomp_family P α (underToLaurent R) f
        r)))

/-- The actual middle minus postcomp cap has its original lower row in the common sheet. -/
theorem middle_minus_postcomp_lower (r : I) :
    middleMinusPostcomp P α f (r, 0) =
    laurent P α (underToLaurentInvert R) f
      (row P α (underToLaurentInvert R) f DoubleSquareMergedSimplex.middleFace
          BassH0Merge.leftIndex r) := by
  let y := mapParameter (postcompNodeLower P (underToLaurentInvert R) ((polynomialUnderCoefficient
      R).app a) ((polynomialUnderFunctor R).map f) (α.app b))
    (CoefficientBassLaurentCompositionCarrier.family P ((polynomialUnderCoefficient R).app a)
        ((polynomialUnderFunctor R).map f) r)
  have hcap := congrArg (CoefficientBassRaw1PolynomialCommonSheet.middleMap P α
      (underToLaurentInvert R) f)
    (minus_postcomp_lower P ((polynomialUnderCoefficient R).app a) ((polynomialUnderFunctor R).map
        f) (α.app b) r)
  exact hcap.trans ((middleMap_laurent P α (underToLaurentInvert R) f y).trans
    (congrArg (laurent P α (underToLaurentInvert R) f) (middle_postcomp_family P α
        (underToLaurentInvert R) f r)))

/-- The actual last input cap has its original lower row in the common sheet. -/
theorem last_input_lower (r : I) :
    lastInput P α β f (r, 0) =
    laurent P α β f
      (row P α β f DoubleSquareMergedSimplex.lastFace BassH0Merge.rightIndex r) := by
  let y := mapParameter (inputNode P β (f) ((polynomialUnderCoefficient R).app b) (α.app b))
    (CoefficientBassLaurentCompositionCarrier.family P ((polynomialUnderCoefficient R).app b)
        (α.app b) r)
  have hcap := congrArg (CoefficientBassRaw1PolynomialCommonSheet.lastMap P α β f)
    (input_lower P β (f) ((polynomialUnderCoefficient R).app b) (α.app b) r)
  exact hcap.trans ((lastMap_laurent P α β f y).trans
    (congrArg (laurent P α β f) (last_input_family P α β f r)))

/-- The actual last plus postcomp cap has its original lower row in the common sheet. -/
theorem last_plus_postcomp_lower (r : I) :
    lastPlusPostcomp P α f (r, 0) =
    laurent P α (underToLaurent R) f
      (row P α (underToLaurent R) f DoubleSquareMergedSimplex.lastFace BassH0Merge.leftIndex r) :=
          by
  let y := mapParameter (postcompNodeLower P (underToLaurent R) (f) ((polynomialUnderCoefficient
      R).app b) (α.app b))
    (CoefficientBassLaurentCompositionCarrier.family P (f) ((polynomialUnderCoefficient R).app b) r)
  have hcap := congrArg (CoefficientBassRaw1PolynomialCommonSheet.lastMap P α (underToLaurent R) f)
    (plus_postcomp_lower P (f) ((polynomialUnderCoefficient R).app b) (α.app b) r)
  exact hcap.trans ((lastMap_laurent P α (underToLaurent R) f y).trans
    (congrArg (laurent P α (underToLaurent R) f) (last_postcomp_family P α (underToLaurent R) f r)))

/-- The actual last minus postcomp cap has its original lower row in the common sheet. -/
theorem last_minus_postcomp_lower (r : I) :
    lastMinusPostcomp P α f (r, 0) =
    laurent P α (underToLaurentInvert R) f
      (row P α (underToLaurentInvert R) f DoubleSquareMergedSimplex.lastFace BassH0Merge.leftIndex
          r) := by
  let y := mapParameter (postcompNodeLower P (underToLaurentInvert R) (f)
      ((polynomialUnderCoefficient R).app b) (α.app b))
    (CoefficientBassLaurentCompositionCarrier.family P (f) ((polynomialUnderCoefficient R).app b) r)
  have hcap := congrArg (CoefficientBassRaw1PolynomialCommonSheet.lastMap P α
      (underToLaurentInvert R) f)
    (minus_postcomp_lower P (f) ((polynomialUnderCoefficient R).app b) (α.app b) r)
  exact hcap.trans ((lastMap_laurent P α (underToLaurentInvert R) f y).trans
    (congrArg (laurent P α (underToLaurentInvert R) f) (last_postcomp_family P α
        (underToLaurentInvert R) f r)))

end Rectangle
end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCapLowerFaces
