/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveCompositionReferences

/-! Exact original composition comparisons and all 31 full dependent reference arrows. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option linter.mathlibStandardSet true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes
open Quillen.PerfectComplexes.BassMWholeNerve
universe u
namespace QuillenTest.MWholeNerveCompositionReferences
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)

/-- The exact original anchored comparison is retained by this named consumer. -/
theorem right_first_entire_anchor :
    (rightStartingAnchor P u v w ≪≫ BassH1References.firstIso P u (v ≫ w)) ≪≫
        isoWhiskerLeft (BassH0Diagram.reference P u).functor (laurentCompositionIso P v w) ≪≫
        (Functor.associator (BassH0Diagram.reference P u).functor
          (coefficientModel P ((laurentUnderFunctor R).map v)).functor
          (coefficientModel P ((laurentUnderFunctor R).map w)).functor).symm =
      postcompAnchor P u v w ≪≫ isoWhiskerRight (BassH1References.firstIso P u v)
        (coefficientModel P ((laurentUnderFunctor R).map w)).functor :=
  right_first_composition_anchor P u v w

/-- The exact original anchored comparison is retained by this named consumer. -/
theorem left_middle_entire_anchor :
    (h0Anchor P (u ≫ v) w ≪≫ BassH1References.middleIso P (u ≫ v) w) ≪≫
        isoWhiskerRight (coefficientCompositionIso P u v) (BassH0Diagram.reference P w).functor ≪≫
        Functor.associator (coefficientModel P u).functor (coefficientModel P v).functor
          (BassH0Diagram.reference P w).functor =
      precompAnchor P u v w ≪≫ isoWhiskerLeft (coefficientModel P u).functor
        (BassH1References.middleIso P v w) :=
  left_middle_composition_anchor P u v w

/-- The exact original anchored comparison is retained by this named consumer. -/
theorem right_first_all_original_references (i : Fin 31) :
    (ModelSimplex.reanchorNodes (rightStartingAnchor P u v w)
      (BassMWhole.nodes P u (v ≫ w)) (firstIndex i)).2.symm ≪≫
        (postcompNodes P u v w (firstIndex i)).2 = rightFirstComparisonIso P u v w i :=
  right_first_reference_comparison P u v w i

/-- The exact original anchored comparison is retained by this named consumer. -/
theorem left_middle_all_original_references (i : Fin 31) :
    (ModelSimplex.reanchorNodes (h0Anchor P (u ≫ v) w)
      (BassMWhole.nodes P (u ≫ v) w) (middleIndex i)).2.symm ≪≫
        (precompNodes P u v w (middleIndex i)).2 = leftMiddleComparisonIso P u v w i :=
  left_middle_reference_comparison P u v w i

/-- The coefficient comparison is exactly the original transported normalized pullback iso. -/
theorem actual_coefficient_comparison :
    coefficientCompositionIso P u v =
      BassReferenceMerge.smallIso
        (eqToIso (congrArg boundedFlatNormalizedPullback (coefficientMap_comp P u v)) ≪≫
          boundedFlatNormalizedPullbackCompIso (coefficientMap P v) (coefficientMap P u)) := rfl

/-- The Laurent comparison retains the actual Laurent image of the composite arrow. -/
theorem actual_laurent_total :
    coefficientMap P ((laurentUnderFunctor R).map (v ≫ w)) =
      coefficientMap P ((laurentUnderFunctor R).map w) ≫
        coefficientMap P ((laurentUnderFunctor R).map v) :=
  laurentComposition_total P v w

end QuillenTest.MWholeNerveCompositionReferences
