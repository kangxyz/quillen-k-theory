/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.KTheory.Bass.ModelDiagramBottomNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientTwoChartStableSequence
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedFiberBassTower

/-!
# Actual finite native coefficient-family bottom contractions

These comparisons use the existing native finite Bass diagrams and their original
coefficient maps. They identify the original two-chart cokernel with the actual next
finite-stage bottom. They do not redefine the original scheme/supported negative groups,
and do not assert stabilization of any original seed.
-/

@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}}

/-- The original fine ambient coefficient family has its genuine natural bottom contraction. -/
def boundedFlatCoefficientAmbientBassBottomContractionIso (Q : Over (Spec R)) (i : ℕ) :
    Quillen.Bass.TwoChart.contraction (underToLaurent R) (underToLaurentInvert R)
      (boundedFlatCoefficientAmbientBassDiagram Q i ⋙ stableHomotopyFunctor (-(i : ℤ))) ≅
    boundedFlatCoefficientAmbientBassDiagram Q (i + 1) ⋙
      stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ)) :=
  modelDiagramBottomContractionIso (boundedFlatCoefficientSectionModelRow Q) i

/-- Original ambient Laurent representatives use the unchanged cone inclusion and signed shift.
-/
@[reassoc]
theorem boundedFlatCoefficientAmbientBassBottomContractionIso_π
    (Q : Over (Spec R)) (i : ℕ) (a : Under R) :
    (Quillen.Bass.TwoChart.contractionπ (underToLaurent R) (underToLaurentInvert R)
      (boundedFlatCoefficientAmbientBassDiagram Q i ⋙
        stableHomotopyFunctor (-(i : ℤ)))).app a ≫
      (boundedFlatCoefficientAmbientBassBottomContractionIso Q i).hom.app a =
    (stableHomotopyFunctor (-(i : ℤ))).map (mappingConeInclusion (StrictSquare.comparison
      ((boundedFlatCoefficientAmbientBassDiagram Q i).mapArrow.mapArrow.obj
        (laurentUnderSquare R a)))) ≫
      (modelDiagramBottomSuccessorIso (boundedFlatCoefficientSectionModelRow Q) i).inv.app a :=
  modelDiagramBottomContractionIso_π (boundedFlatCoefficientSectionModelRow Q) i a

variable {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- The original fine supported family has the actual two-chart bottom comparison. -/
def boundedFlatCoefficientSupportedBassBottomContractionIso (i : ℕ) :
    Quillen.Bass.TwoChart.contraction (underToLaurent R) (underToLaurentInvert R)
      (boundedFlatCoefficientSupportedBassDiagram f i ⋙ stableHomotopyFunctor (-(i : ℤ))) ≅
    boundedFlatCoefficientSupportedBassDiagram f (i + 1) ⋙
      stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ)) :=
  modelDiagramBottomContractionIso (boundedFlatCoefficientSupportedModelFunctor f) i

/-- The original coarse relative-open family has the same genuine natural comparison. -/
def boundedFlatCoefficientOpenBassBottomContractionIso (i : ℕ) :
    Quillen.Bass.TwoChart.contraction (underToLaurent R) (underToLaurentInvert R)
      (boundedFlatCoefficientOpenBassDiagram f i ⋙ stableHomotopyFunctor (-(i : ℤ))) ≅
    boundedFlatCoefficientOpenBassDiagram f (i + 1) ⋙
      stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ)) :=
  modelDiagramBottomContractionIso (boundedFlatCoefficientOpenModelFunctor f) i

/-- The unchanged fine open family has its actual next-stage bottom contraction. -/
def boundedFlatCoefficientFullOpenBassBottomContractionIso (i : ℕ) :
    Quillen.Bass.TwoChart.contraction (underToLaurent R) (underToLaurentInvert R)
      (boundedFlatCoefficientFullOpenBassDiagram f i ⋙ stableHomotopyFunctor (-(i : ℤ))) ≅
    boundedFlatCoefficientFullOpenBassDiagram f (i + 1) ⋙
      stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ)) :=
  modelDiagramBottomContractionIso (boundedFlatCoefficientFullOpenModelFunctor f) i

/-- Supported Laurent representatives keep their actual original cone inclusion and signed shift.
-/
@[reassoc]
theorem boundedFlatCoefficientSupportedBassBottomContractionIso_π (i : ℕ) (a : Under R) :
    (Quillen.Bass.TwoChart.contractionπ (underToLaurent R) (underToLaurentInvert R)
      (boundedFlatCoefficientSupportedBassDiagram f i ⋙
        stableHomotopyFunctor (-(i : ℤ)))).app a ≫
      (boundedFlatCoefficientSupportedBassBottomContractionIso f i).hom.app a =
    (stableHomotopyFunctor (-(i : ℤ))).map (mappingConeInclusion (StrictSquare.comparison
      ((boundedFlatCoefficientSupportedBassDiagram f i).mapArrow.mapArrow.obj
        (laurentUnderSquare R a)))) ≫
      (modelDiagramBottomSuccessorIso (boundedFlatCoefficientSupportedModelFunctor f) i).inv.app
        a :=
  modelDiagramBottomContractionIso_π (boundedFlatCoefficientSupportedModelFunctor f) i a

/-- The bottom comparison preserves the existing finite supported-to-ambient map at its successor.
-/
@[reassoc]
theorem boundedFlatCoefficientSupportedBassBottomContractionIso_forget
    (i : ℕ) (a : Under R) :
    (Quillen.Bass.TwoChart.contractionMap (underToLaurent R) (underToLaurentInvert R)
      (Functor.whiskerRight (boundedFlatCoefficientSupportedBassForget f i)
        (stableHomotopyFunctor (-(i : ℤ))))).app a ≫
      (boundedFlatCoefficientAmbientBassBottomContractionIso Q i).hom.app a =
    (boundedFlatCoefficientSupportedBassBottomContractionIso f i).hom.app a ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((boundedFlatCoefficientSupportedBassForget f (i + 1)).app a) :=
  modelDiagramBottomContractionIso_map
    (boundedFlatCoefficientSupportedForgetPrespectrumTransformation f) i a

/-- The actual fine-to-coarse native open map survives the same bottom comparison. -/
@[reassoc]
theorem boundedFlatCoefficientAmbientBassBottomContractionIso_open
    (i : ℕ) (a : Under R) :
    (Quillen.Bass.TwoChart.contractionMap (underToLaurent R) (underToLaurentInvert R)
      (Functor.whiskerRight (boundedFlatCoefficientAmbientBassOpen f i)
        (stableHomotopyFunctor (-(i : ℤ))))).app a ≫
      (boundedFlatCoefficientOpenBassBottomContractionIso f i).hom.app a =
    (boundedFlatCoefficientAmbientBassBottomContractionIso Q i).hom.app a ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((boundedFlatCoefficientAmbientBassOpen f (i + 1)).app a) :=
  modelDiagramBottomContractionIso_map
    (boundedFlatCoefficientAmbientOpenPrespectrumTransformation f) i a

/-- The existing native coarse-to-fine open restriction is retained at the actual successor. -/
@[reassoc]
theorem boundedFlatCoefficientOpenBassBottomContractionIso_restriction
    (i : ℕ) (a : Under R) :
    (Quillen.Bass.TwoChart.contractionMap (underToLaurent R) (underToLaurentInvert R)
      (Functor.whiskerRight (boundedFlatCoefficientOpenBassRestriction f i)
        (stableHomotopyFunctor (-(i : ℤ))))).app a ≫
      (boundedFlatCoefficientFullOpenBassBottomContractionIso f i).hom.app a =
    (boundedFlatCoefficientOpenBassBottomContractionIso f i).hom.app a ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((boundedFlatCoefficientOpenBassRestriction f (i + 1)).app a) :=
  modelDiagramBottomContractionIso_map
    (boundedFlatCoefficientOpenRestrictionPrespectrumTransformation f) i a

variable (T : Q.left.Opens)

/-- The actual auxiliary-supported ambient family has the original chart bottom cokernel. -/
def boundedFlatCoefficientSupportedAmbientBassBottomContractionIso (i : ℕ) :
    Quillen.Bass.TwoChart.contraction (underToLaurent R) (underToLaurentInvert R)
      (boundedFlatCoefficientSupportedAmbientBassDiagram T i ⋙
        stableHomotopyFunctor (-(i : ℤ))) ≅
    boundedFlatCoefficientSupportedAmbientBassDiagram T (i + 1) ⋙
      stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ)) :=
  modelDiagramBottomContractionIso (boundedFlatCoefficientSupportedAmbientModelFunctor T) i

/-- The original intersection-support fiber has its actual next-stage bottom contraction. -/
def boundedFlatCoefficientSupportedFiberBassBottomContractionIso (i : ℕ) :
    Quillen.Bass.TwoChart.contraction (underToLaurent R) (underToLaurentInvert R)
      (boundedFlatCoefficientSupportedFiberBassDiagram f T i ⋙
        stableHomotopyFunctor (-(i : ℤ))) ≅
    boundedFlatCoefficientSupportedFiberBassDiagram f T (i + 1) ⋙
      stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ)) :=
  modelDiagramBottomContractionIso (boundedFlatCoefficientSupportedFiberModelFunctor f T) i

/-- The actual auxiliary-supported coarse open stages retain their original chart bottom groups.
-/
def boundedFlatCoefficientSupportedOpenBassBottomContractionIso (i : ℕ) :
    Quillen.Bass.TwoChart.contraction (underToLaurent R) (underToLaurentInvert R)
      (boundedFlatCoefficientSupportedOpenBassDiagram f T i ⋙
        stableHomotopyFunctor (-(i : ℤ))) ≅
    boundedFlatCoefficientSupportedOpenBassDiagram f T (i + 1) ⋙
      stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ)) :=
  modelDiagramBottomContractionIso (boundedFlatCoefficientSupportedOpenModelFunctor f T) i

/-- The original auxiliary-supported fine open family has its genuine bottom contraction. -/
def boundedFlatCoefficientSupportedFullOpenBassBottomContractionIso (i : ℕ) :
    Quillen.Bass.TwoChart.contraction (underToLaurent R) (underToLaurentInvert R)
      (boundedFlatCoefficientSupportedFullOpenBassDiagram f T i ⋙
        stableHomotopyFunctor (-(i : ℤ))) ≅
    boundedFlatCoefficientSupportedFullOpenBassDiagram f T (i + 1) ⋙
      stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ)) :=
  modelDiagramBottomContractionIso (boundedFlatCoefficientSupportedFullOpenModelFunctor f T) i

/-- The original intersection-support forget map is retained at the successor bottom. -/
@[reassoc]
theorem boundedFlatCoefficientSupportedFiberBassBottomContractionIso_forget
    (i : ℕ) (a : Under R) :
    (Quillen.Bass.TwoChart.contractionMap (underToLaurent R) (underToLaurentInvert R)
      (Functor.whiskerRight (boundedFlatCoefficientSupportedFiberBassForget f T i)
        (stableHomotopyFunctor (-(i : ℤ))))).app a ≫
      (boundedFlatCoefficientSupportedAmbientBassBottomContractionIso T i).hom.app a =
    (boundedFlatCoefficientSupportedFiberBassBottomContractionIso f T i).hom.app a ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((boundedFlatCoefficientSupportedFiberBassForget f T (i + 1)).app a) :=
  modelDiagramBottomContractionIso_map
    (boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T) i a

omit [IsOpenImmersion f.left] in
/-- The same original auxiliary-supported r-map is preserved by the bottom comparison. -/
@[reassoc]
theorem boundedFlatCoefficientSupportedOpenBassBottomContractionIso_restriction
    (i : ℕ) (a : Under R) :
    (Quillen.Bass.TwoChart.contractionMap (underToLaurent R) (underToLaurentInvert R)
      (Functor.whiskerRight (boundedFlatCoefficientSupportedOpenBassRestriction f T i)
        (stableHomotopyFunctor (-(i : ℤ))))).app a ≫
      (boundedFlatCoefficientSupportedFullOpenBassBottomContractionIso f T i).hom.app a =
    (boundedFlatCoefficientSupportedOpenBassBottomContractionIso f T i).hom.app a ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((boundedFlatCoefficientSupportedOpenBassRestriction f T (i + 1)).app a) :=
  modelDiagramBottomContractionIso_map
    (boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T) i a

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- The original graded native Model stages have the same actual chart bottom contraction. -/
def boundedFlatCoefficientGradedOpenBassBottomContractionIso (i : ℕ) :
    Quillen.Bass.TwoChart.contraction (underToLaurent R) (underToLaurentInvert R)
      (boundedFlatCoefficientGradedOpenBassDiagram f i ⋙ stableHomotopyFunctor (-(i : ℤ))) ≅
    boundedFlatCoefficientGradedOpenBassDiagram f (i + 1) ⋙
      stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ)) :=
  modelDiagramBottomContractionIso (boundedFlatCoefficientGradedOpenModelFunctor f) i

/-- The auxiliary-supported graded native Model stages retain their actual bottom contraction. -/
def boundedFlatCoefficientSupportedGradedOpenBassBottomContractionIso (i : ℕ) :
    Quillen.Bass.TwoChart.contraction (underToLaurent R) (underToLaurentInvert R)
      (boundedFlatCoefficientSupportedGradedOpenBassDiagram f T i ⋙
        stableHomotopyFunctor (-(i : ℤ))) ≅
    boundedFlatCoefficientSupportedGradedOpenBassDiagram f T (i + 1) ⋙
      stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ)) :=
  modelDiagramBottomContractionIso (boundedFlatCoefficientSupportedGradedOpenModelFunctor f T) i

end Quillen.PerfectComplexes
