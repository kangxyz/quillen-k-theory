/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1LaurentChartRestriction

/-!
# The actual polynomial-sheet reference over the fixed Laurent comparison

The polynomial triple starts at Polynomial(a), passes through Polynomial(Polynomial(a))
and Polynomial(Laurent(a)), and ends at Polynomial(Laurent(b)). The final chart has its
own sign, independent of the outer route sign. Its full reference is compared with the
fixed Laurent triple after the source chart using the actual chart naturality equation and
both original binary normalization totals. No equality of comparison interiors is asserted.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialReference
open BassH0Merge CommonReferenceNerve
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (α β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b : Under R} (f : a ⟶ b)

/-- The first polynomial arrow has target Polynomial(Polynomial(a)). -/
abbrev first := coefficientMap P
  ((polynomialUnderFunctor R).map ((polynomialUnderCoefficient R).app a))

/-- The second polynomial arrow has target Polynomial(Laurent(a)). -/
abbrev second := coefficientMap P ((polynomialUnderFunctor R).map (α.app a))

/-- The last polynomial arrow has target Polynomial(Laurent(b)). -/
abbrev last := coefficientMap P
  ((polynomialUnderFunctor R).map ((laurentUnderFunctor R).map f))

/-- The literal polynomial triple retains its original right-associated scheme composite. -/
abbrev polynomialTotal := last P f ≫ (second P α (a := a) ≫ first P (a := a))

/-- The fixed Laurent triple retains the same original association. -/
abbrev laurentTotal := CoefficientBassLaurentProjectionScalar.cMap P f ≫
  (CoefficientBassLaurentProjectionScalar.q P α (a := a) ≫
    CoefficientBassLaurentProjectionScalar.p P (a := a))

/-- The actual source chart acts on genuine Polynomial(a) inputs. -/
abbrev sourceChart := coefficientMap P (β.app a)

/-- The final chart is evaluated at Laurent(b), rather than at b. -/
abbrev targetChart := coefficientMap P (β.app ((laurentUnderFunctor R).obj b))

/-- Naturality of the actual source-to-target three-arrow composite, with both chart signs. -/
theorem total_naturality :
    laurentTotal P α f ≫ sourceChart P β (a := a) =
      targetChart P β (b := b) ≫ polynomialTotal P α f := by
  have h := coefficientMap_naturality P β
    (((polynomialUnderCoefficient R).app a ≫ α.app a) ≫ (laurentUnderFunctor R).map f)
  simp only [Functor.map_comp, coefficientMap_comp] at h
  change laurentTotal P α f ≫ sourceChart P β (a := a) =
    targetChart P β (b := b) ≫ polynomialTotal P α f at h
  exact h

/-- The original polynomial normalized triple is kept as a map from its own input model. -/
abbrev polynomialReference := NormalizedTripleSimplex.sourceMap
  (last P f) (second P α (a := a)) (first P (a := a))

/-- The common reference is literally the fixed Laurent family after the actual source chart. -/
abbrev reference := CoefficientBassRaw1LaurentChartRestriction.chart P β (a := a) ≫
  CoefficientBassLaurentProjectionScalar.reference P α f

/-- The target chart model map acts after the whole polynomial reference. -/
abbrev chartMap := BassMWholeNerve.coefficientModel P (β.app ((laurentUnderFunctor R).obj b))

/-- The full attachment anchor has the required direction from the fixed Laurent reference. -/
def referenceIso : (reference P α β f).functor ≅
    (polynomialReference P α f ≫ chartMap P β (b := b)).functor :=
  (BinaryNormalizationSimplex.total (laurentTotal P α f) (sourceChart P β (a := a))).symm ≪≫
    NativeSquareFiveSimplex.sourceIso (laurentTotal P α f) (sourceChart P β (a := a))
      (targetChart P β (b := b)) (polynomialTotal P α f) (total_naturality P α β f) ≪≫
        BinaryNormalizationSimplex.total (targetChart P β (b := b)) (polynomialTotal P α f)

/-- The entire polynomial node is attached with this exact full reference. -/
def attachNode (N : Node (polynomialReference P α f)) : Node (reference P α β f) :=
  CommonReferenceProduct.postNode (reference P α β f) (chartMap P β (b := b))
    (referenceIso P α β f) N

/-- Attaching a polynomial node keeps its actual model map and final chart. -/
theorem attachNode_model (N : Node (polynomialReference P α f)) :
    (attachNode P α β f N).1 = N.1 ≫ chartMap P β (b := b) := rfl

/-- The whole node reference retains the original three-factor naturality anchor. -/
theorem attachNode_reference (N : Node (polynomialReference P α f)) :
    (attachNode P α β f N).2 = referenceIso P α β f ≪≫
      isoWhiskerRight N.2 (chartMap P β (b := b)).functor := rfl

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialReference
