/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassLaurentTripleCarrier
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveCompositionReferences
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceReanchorAttachment

/-! The unchanged triple comparison in its canonical composite-arrow reference. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassLaurentTripleCanonicalFamily
open BassReferenceMerge BassMWholeNerve
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (r : c ⟶ d)

/-- The coefficient reference for the Laurent image of the left-associated triple composite. -/
abbrev reference := coefficientModel P ((laurentUnderFunctor R).map ((p ≫ q) ≫ r))

/-- The original composite scheme arrow, with its full specified normalization transport. -/
theorem total : coefficientMap P ((laurentUnderFunctor R).map ((p ≫ q) ≫ r)) =
    coefficientMap P ((laurentUnderFunctor R).map r) ≫
      coefficientMap P ((laurentUnderFunctor R).map q) ≫
        coefficientMap P ((laurentUnderFunctor R).map p) :=
  (laurentComposition_total P (p ≫ q) r).trans
    (congrArg (fun k ↦ coefficientMap P ((laurentUnderFunctor R).map r) ≫ k)
      (laurentComposition_total P p q))

/-- The normalization isomorphism from the canonical coefficient reference to the triple carrier. -/
def anchor : (reference P p q r).functor ≅
    (CoefficientBassLaurentTripleCarrier.reference P p q r).functor :=
  smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (total P p q r)))

/-- The eight triple-carrier nodes reanchored in the canonical coefficient reference. -/
def nodes (i : Fin 8) : CommonReferenceNerve.Node (reference P p q r) :=
  CommonReferenceProduct.reanchor (anchor P p q r)
    (CoefficientBassLaurentTripleCarrier.nodes P p q r i)

/-- All six original scalar triangles retain their clocks under the full reference map. -/
def family : C(I × I, |nerve (Codiscrete (CommonReferenceNerve.Node (reference P p q r)))|) :=
  (CommonReferenceNerve.mapParameter (CommonReferenceProduct.reanchor (anchor P p q r))).comp
    (CoefficientBassLaurentTripleCarrier.family P p q r)

theorem family_parameter (s t : I) : family P p q r (s, t) =
    CommonReferenceNerve.parameter (reference P p q r) (nodes P p q r)
      (SplitTripleSimplex.comparisonParameter (s, t)) :=
  CommonReferenceNerve.mapParameter_parameter (CommonReferenceProduct.reanchor (anchor P p q r))
    (CoefficientBassLaurentTripleCarrier.nodes P p q r)
    (SplitTripleSimplex.comparisonParameter (s, t))

theorem family_native (n : ℕ) (s t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (reference P p q r)
      (family P p q r) n ((s, t), x) =
    (boundedFlatTripleTrackComparison
      (coefficientMap P ((laurentUnderFunctor R).map r))
      (coefficientMap P ((laurentUnderFunctor R).map q))
      (coefficientMap P ((laurentUnderFunctor R).map p))).level n (s, (t, x)) := by
  have h0 := CommonReferenceNerve.pointwisePrespectrumFamily_eq_compact
    (reference P p q r) (family P p q r) n (s, t) x
  have h1 := CommonReferenceNerve.pointwise_reanchor (anchor P p q r) n
    (CoefficientBassLaurentTripleCarrier.family P p q r (s, t)) x
  have h2 := CommonReferenceNerve.pointwisePrespectrumFamily_eq_compact
    (CoefficientBassLaurentTripleCarrier.reference P p q r)
    (CoefficientBassLaurentTripleCarrier.family P p q r) n (s, t) x
  exact h0.symm.trans (h1.trans (h2.trans
    (CoefficientBassLaurentTripleCarrier.family_native P p q r n s t x)))

end Quillen.PerfectComplexes.CoefficientBassLaurentTripleCanonicalFamily
