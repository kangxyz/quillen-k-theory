/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveCompositionReferences
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeReferenceWordCoherence

/-! Exact canonical Laurent three-factor reference coherence. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes.CoefficientBassLaurentTripleReference
open BassReferenceMerge BassMWholeNerve
private theorem eqToIso_congr_trans {A C : Type*} [Category C] (f : A → C)
    {x y z : A} (h : x = y) (k : y = z) :
    eqToIso (congrArg f (h.trans k)) = eqToIso (congrArg f h) ≪≫ eqToIso (congrArg f k) := by
  rw [eqToIso_trans]

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (r : c ⟶ d)

/-- The scheme coefficient map induced by the Laurent image of `p`. -/
abbrev geometric {a b : Under R} (p : a ⟶ b) :=
  coefficientMap P ((laurentUnderFunctor R).map p)

/-- The normalized reference isomorphism induced by associativity of `p`, `q`, and `r`. -/
def assocReference :
    (coefficientModel P ((laurentUnderFunctor R).map ((p ≫ q) ≫ r))).functor ≅
      (coefficientModel P ((laurentUnderFunctor R).map (p ≫ (q ≫ r)))).functor :=
  smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
    (congrArg (geometric P) (Category.assoc p q r))))

/-- All three original normalized coefficient constraints agree as complete reference isos. -/
theorem reference_associativity :
    assocReference P p q r ≪≫ laurentCompositionIso P p (q ≫ r) ≪≫
      isoWhiskerLeft (coefficientModel P ((laurentUnderFunctor R).map p)).functor
        (laurentCompositionIso P q r) =
    laurentCompositionIso P (p ≫ q) r ≪≫
      isoWhiskerRight (laurentCompositionIso P p q)
        (coefficientModel P ((laurentUnderFunctor R).map r)).functor := by
  have h := anchored_factorizations_strict
    (geometric P r) (geometric P q) (geometric P p)
    (geometric P (q ≫ r)) (geometric P (p ≫ q)) (geometric P ((p ≫ q) ≫ r))
    (laurentComposition_total P q r) (laurentComposition_total P p q)
    ((congrArg (geometric P) (Category.assoc p q r)).trans
      (laurentComposition_total P p (q ≫ r)))
    (laurentComposition_total P (p ≫ q) r)
  rw [eqToIso_congr_trans boundedFlatNormalizedPullback
    (congrArg (geometric P) (Category.assoc p q r))
    (laurentComposition_total P p (q ≫ r))] at h
  rw [assocReference, laurentCompositionIso, laurentCompositionIso,
    laurentCompositionIso, laurentCompositionIso]
  erw [smallIso_precomp, smallIso_postcomp]
  exact smallIso_word_four_three _ _ _ _ _ _ _ h

end Quillen.PerfectComplexes.CoefficientBassLaurentTripleReference
