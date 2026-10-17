/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassFiniteSourceSheetNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPairCorrectedNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialSourceProjection

/-!
# The unchanged polynomial cap on the original polynomial-square input

The first, second and fourth source overlap cells use this one finite source action. Its
five-node input and the entire selected pair cap retain their independent clocks. The full
reference placement includes the source projection, original right-first triple route and
the original polynomial square's binary total.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.InputPolynomial
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)

/-- The original polynomial-square source reference for the first coefficient arrow `p`. -/
abbrev sourceReference := CoefficientSquareFamilies.polynomialSource P p
/-- The original paused polynomial reference for the following pair `q`, `w`. -/
abbrev pairReference := CoefficientBassRaw1PolynomialPausedChart.polynomialReference P q w
/-- The full composite reference combining the first polynomial square with the following pair
cap. -/
abbrev reference := sourceReference P p ≫ pairReference P q w
/-- The original unextended triple source reference retained by the polynomial cap. -/
abbrev input := CoefficientBassRaw1PolynomialSourceProjection.input P p q w
/-- The normalized original polynomial projection at the final coefficient algebra `d`. -/
abbrev targetProjection := normalizedMap (polynomialProjection P d)

/-- The actual source projection and the original right-first route meet before chart attachment. -/
def polynomialAnchor : (input P p q w ≫ targetProjection P (d := d)).functor ≅
    (reference P p q w).functor :=
  CoefficientBassRaw1PolynomialSourceProjection.polynomialIso P p q w ≪≫
    isoWhiskerLeft (normalizedMap (polynomialProjection P a)).functor
      (NormalizedTripleSimplex.rightFirst
        (coefficientMap P ((polynomialUnderFunctor R).map w))
        (coefficientMap P ((polynomialUnderFunctor R).map q))
        (coefficientMap P ((polynomialUnderFunctor R).map p))) ≪≫
    (Functor.associator (normalizedMap (polynomialProjection P a)).functor
      (normalizedMap (coefficientMap P ((polynomialUnderFunctor R).map p))).functor
      (pairReference P q w).functor).symm ≪≫
    isoWhiskerRight (BinaryNormalizationSimplex.total
      (coefficientMap P ((polynomialUnderFunctor R).map p)) (polynomialProjection P a)).symm
      (pairReference P q w).functor

variable (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
local notation "J" => BassMWholeNerve.coefficientModel P (β.app d)

/-- The product first sheet accepts actual base inputs through the original five-node square. -/
abbrev carrier := FiniteSourceSheet.target (sourceReference P p) (pairReference P q w) J

/-- The existing corrected polynomial cap is acted on; its interior is not chosen again. -/
def family : C((I × I) × I, carrier P p q w β) :=
  (FiniteSourceSheet.action (sourceReference P p) (pairReference P q w) J
    (CoefficientSquareFamilies.polynomialNodes P p)).comp
    ⟨fun z ↦ (CoefficientBassRaw1PolynomialPairCone.corrected P β q w z.1,
      NativeSquareFiveSimplex.parameter z.2), by fun_prop⟩

/-- All three clocks remain independent in the whole native first-sheet evaluation. -/
theorem family_native (n : ℕ) (r h t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CoefficientBassFiniteSourceSheetNative.evaluate (reference P p q w) J n
        (family P p q w β ((r, h), t)) x =
      CoefficientBassRaw1PolynomialPairCone.evaluate P β q w n
        (CoefficientBassRaw1PolynomialPairCone.corrected P β q w (r, h))
        ((boundedFlatCoefficientPolynomialSquareHomotopy P p).level n (t, x)) := by
  have hf := CoefficientBassFiniteSourceSheetNative.action_native
    (sourceReference P p) (pairReference P q w) J
    (CoefficientSquareFamilies.polynomialNodes P p) n
    (CoefficientBassRaw1PolynomialPairCone.corrected P β q w (r, h))
    (NativeSquareFiveSimplex.parameter t) x
  have hs : prespectrumFamily (sourceReference P p)
      (CoefficientSquareFamilies.polynomialNodes P p) n
      (NativeSquareFiveSimplex.parameter t, x) =
        (boundedFlatCoefficientPolynomialSquareHomotopy P p).level n (t, x) := by
    rw [prespectrumFamily_eq]
    exact CoefficientSquareFamilies.polynomial_native P p n t x
  exact hf.trans (congrArg (CoefficientBassRaw1PolynomialPairCone.evaluate P β q w n
    (CoefficientBassRaw1PolynomialPairCone.corrected P β q w (r, h))) hs)

end Quillen.PerfectComplexes.BassMWholeConeCarrier.InputPolynomial
