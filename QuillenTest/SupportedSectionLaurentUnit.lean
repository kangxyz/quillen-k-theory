/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionLaurentUnit

/-!
# Consumers of the original supported Laurent action

The actual target unit, chosen section zero, original Laurent coordinate and inverse coordinate
remain explicit. Whole realized tracks keep their original endpoints, points and independent
structure parameter. The Laurent open-pair square is supplied as genuine geometric data, not as
an assumed homotopy or compatibility conclusion.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent
open Quillen.PerfectComplexes

noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent
open scoped unitInterval
universe u
namespace QuillenTest.SupportedSectionLaurentUnit

open Quillen
open PerfectComplexes
variable {R S : CommRingCat.{u}} {U V : Scheme.{u}}
attribute [local irreducible] boundedFlatAffineOriginalEvaluation boundedFlatAffineEvaluationAt
  boundedFlatPerfectGlobalUnitIso

/-- The specified original target unit acts trivially on the actual chosen source-zero image. -/
theorem original_target_unit_zero (j : U ⟶ Spec R) (j' : V ⟶ Spec S)
    [IsOpenImmersion j] [IsOpenImmersion j'] (f : R ⟶ S) (l : V ⟶ U)
    (h : l ≫ j = j' ≫ Spec.map f) (r : (Γ(Spec S, ⊤))ˣ) :
    (boundedFlatAffineSupportedSectionPullbackUnitIso j j' f l h r).hom.app
        (boundedFlatAffineSupportedSectionWaldhausen j).zero = 𝟙 _ :=
  boundedFlatAffineSupportedSectionPullbackUnitIso_zero j j' f l h r

/-- The unchanged supported forward map is the original Laurent automorphism on the full section.
-/
theorem original_forward_section_action
    (j : U ⟶ Spec (.of (LaurentPolynomial R))) [IsOpenImmersion j]
    (s : BoundedFlatAffineSupportedSections j) :
    ((boundedFlatAffineSupportedSectionLaurentUnitIso j).hom.app s).hom =
      (boundedFlatAffineSectionLaurentUnitIso R).hom.app s.obj :=
  boundedFlatAffineSupportedSectionLaurentUnitIso_hom_original j s

/-- The inverse retains the original inverse Laurent map on that same section. -/
theorem original_inverse_section_action
    (j : U ⟶ Spec (.of (LaurentPolynomial R))) [IsOpenImmersion j]
    (s : BoundedFlatAffineSupportedSections j) :
    ((boundedFlatAffineSupportedSectionLaurentUnitIso j).inv.app s).hom =
      (boundedFlatAffineSectionLaurentUnitIso R).inv.app s.obj :=
  boundedFlatAffineSupportedSectionLaurentUnitIso_inv_original j s

/-- At every original target coefficient arrow, the specified scalar and inverse are T and T⁻¹. -/
theorem original_target_coordinate_parameters (q : CommRingCat.of (LaurentPolynomial R) ⟶ S) :
    (Scheme.ΓSpecIso S).hom
        (↑(Units.map (Spec.map q).appTop.hom.toMonoidHom (laurentGlobalUnit R))) =
        q.hom (LaurentPolynomial.T 1) ∧
      (Scheme.ΓSpecIso S).hom
        (↑((Units.map (Spec.map q).appTop.hom.toMonoidHom (laurentGlobalUnit R))⁻¹)) =
        q.hom (LaurentPolynomial.T (-1)) :=
  ⟨laurentGlobalUnit_image q, laurentGlobalUnit_image_inv q⟩

variable (j : U ⟶ Spec R) (jL : V ⟶ Spec (.of (LaurentPolynomial R)))
    [IsOpenImmersion j] [IsOpenImmersion jL] (l : V ⟶ U)
    (h : l ≫ j = jL ≫ Spec.map (laurentCoefficient R))

/-- Both original level-zero loop endpoints are the unchanged supported Laurent map. -/
theorem original_laurent_level_zero_endpoints
    (x : (prespectrum (boundedFlatAffineSupportedSectionModel j)).space 0) :
    (boundedFlatAffineSupportedSectionLaurentUnitHomotopy j jL l h).level 0 (0, x) =
        (boundedFlatAffineSupportedSectionPrespectrumMap j jL (laurentCoefficient R) l h).map 0 x ∧
      (boundedFlatAffineSupportedSectionLaurentUnitHomotopy j jL l h).level 0 (1, x) =
        (boundedFlatAffineSupportedSectionPrespectrumMap j jL (laurentCoefficient R) l h).map 0 x :=
  ⟨(boundedFlatAffineSupportedSectionLaurentUnitHomotopy j jL l h).at_zero 0 x,
    (boundedFlatAffineSupportedSectionLaurentUnitHomotopy j jL l h).at_one 0 x⟩

/-- The original point remains fixed at every Laurent action time. -/
theorem original_laurent_point_track (n : ℕ) (s : unitInterval) :
    (boundedFlatAffineSupportedSectionLaurentUnitHomotopy j jL l h).level n
        (s, (prespectrum (boundedFlatAffineSupportedSectionModel j)).point n) =
      (prespectrum (boundedFlatAffineSupportedSectionModel jL)).point n :=
  (boundedFlatAffineSupportedSectionLaurentUnitHomotopy j jL l h).at_point n s

/-- Original action time and structure time remain independent. -/
theorem original_laurent_structure_track (n : ℕ) (s t : unitInterval)
    (x : (prespectrum (boundedFlatAffineSupportedSectionModel j)).space n) :
    (boundedFlatAffineSupportedSectionLaurentUnitHomotopy j jL l h).level (n + 1)
        (s, (prespectrum (boundedFlatAffineSupportedSectionModel j)).structureMap n x t) =
      (prespectrum (boundedFlatAffineSupportedSectionModel jL)).structureMap n
        ((boundedFlatAffineSupportedSectionLaurentUnitHomotopy j jL l h).level n (s, x)) t :=
  (boundedFlatAffineSupportedSectionLaurentUnitHomotopy j jL l h).comm n s x t

end QuillenTest.SupportedSectionLaurentUnit
