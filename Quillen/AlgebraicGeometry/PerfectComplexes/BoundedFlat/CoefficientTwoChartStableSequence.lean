/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Bass.ModelDiagramTwoChartStableSequence
public import Quillen.AlgebraicGeometry.Scheme.CoefficientPolynomialLaurent
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedBassTower
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedOpenBassTower

/-!
# The realized spectral Bass row for the original native coefficient families

Actual polynomial evaluation at zero gives a strict retraction on every original finite
coefficient Model stage. Finite Model geometry discharges the original plus, right-inclusion,
and span-to-Laurent cone excisions and the unchanged right-cone collapse. The resulting
all-integer row applies to the actual ambient, open, supported, and auxiliary-supported rows.
The geometric zero map below keeps the native chosen fibers and their original projections.

No chart middle exactness, classical fundamental row, seed preservation, or finite transition
equivalence is asserted here. Each family retains the hypotheses of its original Model constructor.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Quillen.KTheory.Bass Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Bass.TwoChartStable
universe u
namespace Quillen.PerfectComplexes

variable {R : CommRingCat.{u}}

/-- The actual zero section between the original chosen native coefficient fibers. -/
def boundedFlatCoefficientPolynomialZero (Q : Over (Spec R)) (a : Under R) :
    space (op Q, a) ⟶ space (op Q, (polynomialUnderFunctor R).obj a) :=
  coefficientMap Q (modelDiagramPolynomialZero a)

/-- The native zero section lies over the original affine polynomial evaluation at zero. -/
@[reassoc]
theorem boundedFlatCoefficientPolynomialZero_coefficientProjection
    (Q : Over (Spec R)) (a : Under R) :
    boundedFlatCoefficientPolynomialZero Q a ≫
      coefficientProjection (op Q, (polynomialUnderFunctor R).obj a) =
        coefficientProjection (op Q, a) ≫
          Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : a.right))) :=
  coefficientMap_coefficientProjection Q (modelDiagramPolynomialZero a)

/-- The original native polynomial projection is strictly split by this actual zero section. -/
@[reassoc]
theorem boundedFlatCoefficientPolynomialZero_projection (Q : Over (Spec R)) (a : Under R) :
    boundedFlatCoefficientPolynomialZero Q a ≫ polynomialProjection Q a =
      𝟙 (space (op Q, a)) := by
  unfold boundedFlatCoefficientPolynomialZero polynomialProjection
  rw [← coefficientMap_comp, modelDiagramPolynomialCoefficient_zero]
  change Quillen.Scheme.CoefficientBaseChange.map (𝟙 (op Q, a)) = _
  exact Quillen.Scheme.CoefficientBaseChange.map_id (op Q, a)

/-- All structural-row inputs are constructed on every original fine ambient coefficient stage.
-/
def boundedFlatCoefficientAmbientTwoChartSpectralConditions
    (Q : Over (Spec R)) (i : ℕ) (a : Under R) :
    SpectralConditions ((boundedFlatCoefficientAmbientBassDiagram Q i).mapArrow.mapArrow.obj
      (laurentUnderSquare R a)) :=
  modelDiagramTwoChartSpectralConditions (boundedFlatCoefficientSectionModelRow Q) i a

/-- The actual ambient spectral Bass row, retaining its original cone inclusion and shift. -/
def boundedFlatCoefficientAmbientTwoChartSequence
    (Q : Over (Spec R)) (i : ℕ) (a : Under R) (d : ℤ) : ShortComplex AddCommGrpCat :=
  bassSequence ((boundedFlatCoefficientAmbientBassDiagram Q i).mapArrow.mapArrow.obj
    (laurentUnderSquare R a)) (boundedFlatCoefficientAmbientTwoChartSpectralConditions Q i a) d

/-- The native fine ambient spectral row is short exact in every signed degree. -/
theorem boundedFlatCoefficientAmbientTwoChartSequence_shortExact
    (Q : Over (Spec R)) (i : ℕ) (a : Under R) (d : ℤ) :
    (boundedFlatCoefficientAmbientTwoChartSequence Q i a d).ShortExact :=
  bassSequence_shortExact _ _ d

variable {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- Every actual fine supported coefficient stage has the full original spectral-row inputs. -/
def boundedFlatCoefficientSupportedTwoChartSpectralConditions (i : ℕ) (a : Under R) :
    SpectralConditions ((boundedFlatCoefficientSupportedBassDiagram f i).mapArrow.mapArrow.obj
      (laurentUnderSquare R a)) :=
  modelDiagramTwoChartSpectralConditions (boundedFlatCoefficientSupportedModelFunctor f) i a

/-- The actual supported spectral row, using the unchanged native supported Bass diagram. -/
def boundedFlatCoefficientSupportedTwoChartSequence (i : ℕ) (a : Under R) (d : ℤ) :
    ShortComplex AddCommGrpCat :=
  bassSequence ((boundedFlatCoefficientSupportedBassDiagram f i).mapArrow.mapArrow.obj
    (laurentUnderSquare R a)) (boundedFlatCoefficientSupportedTwoChartSpectralConditions f i a) d

/-- The original supported spectral row is short exact in every signed degree. -/
theorem boundedFlatCoefficientSupportedTwoChartSequence_shortExact
    (i : ℕ) (a : Under R) (d : ℤ) :
    (boundedFlatCoefficientSupportedTwoChartSequence f i a d).ShortExact :=
  bassSequence_shortExact _ _ d

/-- Actual coarse open Models discharge every retained condition at all original finite stages.
-/
def boundedFlatCoefficientOpenTwoChartSpectralConditions (i : ℕ) (a : Under R) :
    SpectralConditions ((boundedFlatCoefficientOpenBassDiagram f i).mapArrow.mapArrow.obj
      (laurentUnderSquare R a)) :=
  modelDiagramTwoChartSpectralConditions (boundedFlatCoefficientOpenModelFunctor f) i a

/-- The actual coarse open spectral row, with both original Laurent chart maps. -/
def boundedFlatCoefficientOpenTwoChartSequence (i : ℕ) (a : Under R) (d : ℤ) :
    ShortComplex AddCommGrpCat :=
  bassSequence ((boundedFlatCoefficientOpenBassDiagram f i).mapArrow.mapArrow.obj
    (laurentUnderSquare R a)) (boundedFlatCoefficientOpenTwoChartSpectralConditions f i a) d

/-- The original coarse open spectral row is short exact in every signed degree. -/
theorem boundedFlatCoefficientOpenTwoChartSequence_shortExact
    (i : ℕ) (a : Under R) (d : ℤ) :
    (boundedFlatCoefficientOpenTwoChartSequence f i a d).ShortExact :=
  bassSequence_shortExact _ _ d

/-- The fine native open coefficient stages have the same completely realized inputs. -/
def boundedFlatCoefficientFullOpenTwoChartSpectralConditions (i : ℕ) (a : Under R) :
    SpectralConditions ((boundedFlatCoefficientFullOpenBassDiagram f i).mapArrow.mapArrow.obj
      (laurentUnderSquare R a)) :=
  modelDiagramTwoChartSpectralConditions (boundedFlatCoefficientFullOpenModelFunctor f) i a

/-- The actual fine open spectral row of the unchanged open-side Bass diagram. -/
def boundedFlatCoefficientFullOpenTwoChartSequence (i : ℕ) (a : Under R) (d : ℤ) :
    ShortComplex AddCommGrpCat :=
  bassSequence ((boundedFlatCoefficientFullOpenBassDiagram f i).mapArrow.mapArrow.obj
    (laurentUnderSquare R a)) (boundedFlatCoefficientFullOpenTwoChartSpectralConditions f i a) d

omit [IsOpenImmersion f.left] in
/-- The original fine open spectral row is short exact in every signed degree. -/
theorem boundedFlatCoefficientFullOpenTwoChartSequence_shortExact
    (i : ℕ) (a : Under R) (d : ℤ) :
    (boundedFlatCoefficientFullOpenTwoChartSequence f i a d).ShortExact :=
  bassSequence_shortExact _ _ d

variable (T : Q.left.Opens)

/-- Actual auxiliary-supported ambient Models satisfy all inputs at every finite Bass stage. -/
def boundedFlatCoefficientSupportedAmbientTwoChartSpectralConditions (i : ℕ) (a : Under R) :
    SpectralConditions (modelDiagramTwoChartSquare
      (boundedFlatCoefficientSupportedAmbientModelFunctor T) i a) :=
  modelDiagramTwoChartSpectralConditions (boundedFlatCoefficientSupportedAmbientModelFunctor T) i a

/-- All retained inputs are discharged for the original auxiliary-supported coarse open stage. -/
def boundedFlatCoefficientSupportedOpenTwoChartSpectralConditions (i : ℕ) (a : Under R) :
    SpectralConditions ((boundedFlatCoefficientSupportedOpenBassDiagram f T i).mapArrow.mapArrow.obj
      (laurentUnderSquare R a)) :=
  modelDiagramTwoChartSpectralConditions (boundedFlatCoefficientSupportedOpenModelFunctor f T) i a

/-- The unchanged auxiliary-supported coarse open spectral row. -/
def boundedFlatCoefficientSupportedOpenTwoChartSequence (i : ℕ) (a : Under R) (d : ℤ) :
    ShortComplex AddCommGrpCat :=
  bassSequence ((boundedFlatCoefficientSupportedOpenBassDiagram f T i).mapArrow.mapArrow.obj
    (laurentUnderSquare R a))
      (boundedFlatCoefficientSupportedOpenTwoChartSpectralConditions f T i a) d

omit [IsOpenImmersion f.left] in
/-- The original auxiliary-supported coarse row is short exact in every signed degree. -/
theorem boundedFlatCoefficientSupportedOpenTwoChartSequence_shortExact
    (i : ℕ) (a : Under R) (d : ℤ) :
    (boundedFlatCoefficientSupportedOpenTwoChartSequence f T i a d).ShortExact :=
  bassSequence_shortExact _ _ d

/-- The original auxiliary-supported fine open stage has completely realized spectral inputs. -/
def boundedFlatCoefficientSupportedFullOpenTwoChartSpectralConditions (i : ℕ) (a : Under R) :
    SpectralConditions
      ((boundedFlatCoefficientSupportedFullOpenBassDiagram f T i).mapArrow.mapArrow.obj
        (laurentUnderSquare R a)) :=
  modelDiagramTwoChartSpectralConditions
    (boundedFlatCoefficientSupportedFullOpenModelFunctor f T) i a

/-- The unchanged auxiliary-supported fine open spectral row. -/
def boundedFlatCoefficientSupportedFullOpenTwoChartSequence (i : ℕ) (a : Under R) (d : ℤ) :
    ShortComplex AddCommGrpCat :=
  bassSequence ((boundedFlatCoefficientSupportedFullOpenBassDiagram f T i).mapArrow.mapArrow.obj
    (laurentUnderSquare R a))
      (boundedFlatCoefficientSupportedFullOpenTwoChartSpectralConditions f T i a) d

omit [IsOpenImmersion f.left] in
/-- The original auxiliary-supported fine row is short exact in every signed degree. -/
theorem boundedFlatCoefficientSupportedFullOpenTwoChartSequence_shortExact
    (i : ℕ) (a : Under R) (d : ℤ) :
    (boundedFlatCoefficientSupportedFullOpenTwoChartSequence f T i a d).ShortExact :=
  bassSequence_shortExact _ _ d

/-- The actual auxiliary-supported closed-fiber Models satisfy the same finite-stage inputs. -/
def boundedFlatCoefficientSupportedFiberTwoChartSpectralConditions (i : ℕ) (a : Under R) :
    SpectralConditions (modelDiagramTwoChartSquare
      (boundedFlatCoefficientSupportedFiberModelFunctor f T) i a) :=
  modelDiagramTwoChartSpectralConditions (boundedFlatCoefficientSupportedFiberModelFunctor f T) i a

end Quillen.PerfectComplexes
