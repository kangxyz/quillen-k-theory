/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenSectionDiagramLaurent

/-!
# Original-coordinate consumers for the actual full-open Laurent track

The forward and inverse components retain the literal original coordinates T and T inverse.
The degree-zero consumer retains the same unit-action time through every coefficient map.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Scheme.AffineOpenPair Quillen.PerfectComplexes Quillen.PolynomialBaseChange
universe u
namespace Quillen.Tests.FullOpenSectionLaurent
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The forward component on each original term multiplies by the restriction of T itself. -/
theorem original_T_hom_terms (a : Under R)
    (s : BoundedFlatAffineFullOpenSections j ((laurentUnderFunctor R).obj a)) (n : ℤ) :
    ((boundedFlatPerfect (openSpace j ((laurentUnderFunctor R).obj a))).ι.map
      ((boundedFlatAffineFullOpenOriginalEvaluation j ((laurentUnderFunctor R).obj a)).map
        ((boundedFlatAffineFullOpenSectionLaurentUnitIso j a).hom.app s))).f n =
      (Quillen.SchemeSheaf.globalScalar (openSpace j ((laurentUnderFunctor R).obj a))
        ((inclusion j ((laurentUnderFunctor R).obj a)).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial a.right))).inv
            (LaurentPolynomial.T 1)))).app
          (((boundedFlatAffineFullOpenOriginalEvaluation j
            ((laurentUnderFunctor R).obj a)).obj s).obj.X n) := by
  rw [boundedFlatAffineFullOpenSectionLaurentUnitIso,
    boundedFlatAffineFullOpenOriginalEvaluation_map_sectionUnitIso_hom,
    boundedFlatPerfectGlobalUnitIso_hom_original, complexGlobalUnitIso_original_terms]
  rfl

/-- Only the inverse component uses the restriction of the original inverse coordinate. -/
theorem original_T_inv_terms (a : Under R)
    (s : BoundedFlatAffineFullOpenSections j ((laurentUnderFunctor R).obj a)) (n : ℤ) :
    ((boundedFlatPerfect (openSpace j ((laurentUnderFunctor R).obj a))).ι.map
      ((boundedFlatAffineFullOpenOriginalEvaluation j ((laurentUnderFunctor R).obj a)).map
        ((boundedFlatAffineFullOpenSectionLaurentUnitIso j a).inv.app s))).f n =
      (Quillen.SchemeSheaf.globalScalar (openSpace j ((laurentUnderFunctor R).obj a))
        ((inclusion j ((laurentUnderFunctor R).obj a)).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial a.right))).inv
            (LaurentPolynomial.T (-1))))).app
          (((boundedFlatAffineFullOpenOriginalEvaluation j
            ((laurentUnderFunctor R).obj a)).obj s).obj.X n) := by
  rw [boundedFlatAffineFullOpenSectionLaurentUnitIso,
    boundedFlatAffineFullOpenOriginalEvaluation_map_sectionUnitIso_inv,
    boundedFlatPerfectGlobalUnitIso_inv_terms]
  rfl

/-- The original degree-zero loop track is natural at the identical action time. -/
theorem degreeZero_coefficient_track {a b : Under R} (f : a ⟶ b) (t : unitInterval)
    (x : ((boundedFlatAffineFullOpenSectionPrespectrumFunctor j).obj a).space 0) :
    ((boundedFlatAffineFullOpenSectionPrespectrumFunctor j).map
        ((laurentUnderFunctor R).map f)).map 0
        ((boundedFlatAffineFullOpenSectionDiagramLaurentHomotopy j a).level 0 (t, x)) =
      (boundedFlatAffineFullOpenSectionDiagramLaurentHomotopy j b).level 0
        (t, ((boundedFlatAffineFullOpenSectionPrespectrumFunctor j).map f).map 0 x) :=
  boundedFlatAffineFullOpenSectionDiagramLaurentHomotopy_naturality_apply j f 0 t x

end Quillen.Tests.FullOpenSectionLaurent
