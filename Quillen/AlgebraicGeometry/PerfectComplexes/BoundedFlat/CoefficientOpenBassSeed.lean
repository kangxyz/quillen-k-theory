/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.CoefficientSectionUnits
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientOpenGrading
public import Quillen.KTheory.Bass.StrictLaurentSeed

/-!
# Actual global native Laurent actions and Bass seeds

The original joint native ambient and open sections carry their coefficient-pulled forward
Laurent units. Their unchanged C/F/G Models realize those units as complete natural tracks.
One shared Bass constructor preserves the original coefficient square, its chosen joint zero,
its source-leg null and the prescribed scalar/null concatenation for all three diagrams.
Only the graded coefficient diagram requires compactness of the original ambient and open.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- The original ambient forward Laurent unit, with its proved coefficient naturality. -/
def boundedFlatCoefficientOpenLaurentAction :
    LaurentSeed.ModelAction (boundedFlatCoefficientOpenModelFunctor f) where
  unit a := boundedFlatCoefficientSectionLaurentUnitIso Q a
  naturality g := boundedFlatCoefficientSectionLaurentUnitIso_coefficient Q g

/-- The original restricted forward Laurent unit on the actual native fine open row. -/
def boundedFlatCoefficientFullOpenLaurentAction :
    LaurentSeed.ModelAction (boundedFlatCoefficientFullOpenModelFunctor f) where
  unit a := boundedFlatCoefficientSectionLaurentUnitIso P a
  naturality g := boundedFlatCoefficientSectionLaurentUnitIso_coefficient P g

/-- The entire original ambient Laurent action track on the unchanged coefficient Model map. -/
def boundedFlatCoefficientOpenLaurentHomotopy (a : Under R) :=
  (boundedFlatCoefficientOpenLaurentAction f).track.homotopy a

/-- The entire original restricted Laurent action track on the actual fine open Model map. -/
def boundedFlatCoefficientFullOpenLaurentHomotopy (a : Under R) :=
  (boundedFlatCoefficientFullOpenLaurentAction f).track.homotopy a

/-- All four original ambient native corners with their original positive and inverse charts. -/
def boundedFlatCoefficientOpenBassSquare (a : Under R) :=
  LaurentSeed.square (boundedFlatCoefficientOpenPrespectrumFunctor f) a

/-- All four original fine open corners with the same coefficient charts. -/
def boundedFlatCoefficientFullOpenBassSquare (a : Under R) :=
  LaurentSeed.square (boundedFlatCoefficientFullOpenPrespectrumFunctor f) a

/-- The actual mapping cone of the original ambient square comparison. -/
def boundedFlatCoefficientOpenBassCone (a : Under R) :=
  LaurentSeed.cone (boundedFlatCoefficientOpenPrespectrumFunctor f) a

/-- The actual mapping cone of the original fine open square comparison. -/
def boundedFlatCoefficientFullOpenBassCone (a : Under R) :=
  LaurentSeed.cone (boundedFlatCoefficientFullOpenPrespectrumFunctor f) a

/-- The original ambient source-leg cylinder; it is not a localization-null substitution. -/
def boundedFlatCoefficientOpenBassNullHomotopy (a : Under R) :=
  LaurentSeed.sourceNull (boundedFlatCoefficientOpenPrespectrumFunctor f) a

/-- The original fine open source-leg cylinder on its unchanged native square. -/
def boundedFlatCoefficientFullOpenBassNullHomotopy (a : Under R) :=
  LaurentSeed.sourceNull (boundedFlatCoefficientFullOpenPrespectrumFunctor f) a

/-- The original ambient pointwise seed retains the prescribed scalar/null concatenation. -/
def boundedFlatCoefficientOpenBassSeedMap (a : Under R) :=
  (boundedFlatCoefficientOpenLaurentAction f).track.seedMap a

/-- The original fine open pointwise seed retains that same prescribed concatenation. -/
def boundedFlatCoefficientFullOpenBassSeedMap (a : Under R) :=
  (boundedFlatCoefficientFullOpenLaurentAction f).track.seedMap a

/-- The constructed coefficient-natural original ambient Bass seed. -/
def boundedFlatCoefficientOpenBassSeed :
    boundedFlatCoefficientOpenPrespectrumFunctor f ⟶
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedFlatCoefficientOpenPrespectrumFunctor f) :=
  (boundedFlatCoefficientOpenLaurentAction f).track.seed

/-- The constructed coefficient-natural original fine open Bass seed. -/
def boundedFlatCoefficientFullOpenBassSeed :
    boundedFlatCoefficientFullOpenPrespectrumFunctor f ⟶
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedFlatCoefficientFullOpenPrespectrumFunctor f) :=
  (boundedFlatCoefficientFullOpenLaurentAction f).track.seed

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- The same actual open unit acts on the original graded Model; only weakness changes. -/
def boundedFlatCoefficientGradedOpenLaurentAction :
    LaurentSeed.ModelAction (boundedFlatCoefficientGradedOpenModelFunctor f) where
  unit a := boundedFlatCoefficientSectionLaurentUnitIso P a
  naturality g := boundedFlatCoefficientSectionLaurentUnitIso_coefficient P g

/-- The unchanged forward Laurent unit realized in the original graded coefficient diagram. -/
def boundedFlatCoefficientGradedOpenLaurentHomotopy (a : Under R) :=
  (boundedFlatCoefficientGradedOpenLaurentAction f).track.homotopy a

/-- The original graded native four-corner square. -/
def boundedFlatCoefficientGradedOpenBassSquare (a : Under R) :=
  LaurentSeed.square (boundedFlatCoefficientGradedOpenPrespectrumFunctor f) a

/-- The actual mapping cone of the original graded comparison map. -/
def boundedFlatCoefficientGradedOpenBassCone (a : Under R) :=
  LaurentSeed.cone (boundedFlatCoefficientGradedOpenPrespectrumFunctor f) a

/-- The original graded source-leg cylinder, with every time parameter unchanged. -/
def boundedFlatCoefficientGradedOpenBassNullHomotopy (a : Under R) :=
  LaurentSeed.sourceNull (boundedFlatCoefficientGradedOpenPrespectrumFunctor f) a

/-- The graded pointwise seed uses that original source-leg null and forward scalar action. -/
def boundedFlatCoefficientGradedOpenBassSeedMap (a : Under R) :=
  (boundedFlatCoefficientGradedOpenLaurentAction f).track.seedMap a

/-- The constructed coefficient-natural original graded Bass seed. -/
def boundedFlatCoefficientGradedOpenBassSeed :
    boundedFlatCoefficientGradedOpenPrespectrumFunctor f ⟶
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedFlatCoefficientGradedOpenPrespectrumFunctor f) :=
  (boundedFlatCoefficientGradedOpenLaurentAction f).track.seed

end Quillen.PerfectComplexes
