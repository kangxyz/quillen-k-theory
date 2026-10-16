/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.FullOpenSectionUnit
public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Units
public import Aglib.Algebra.Polynomial.Laurent.UnderSquare

/-!
# The original Laurent unit on actual full-open sections

The unchanged original global coordinate unit is restricted along the specified full-open
inclusion and acts on its actual section category. Its original evaluation and coefficient
square retain that same forward unit. The inverse-coordinate polynomial chart does not change
this action to the inverse unit.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.AffineOpenPair AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedFlatAffineFullOpenOriginalEvaluation
  boundedFlatPerfectGlobalUnitIso

/-- The actual full-open Laurent fiber carries the original forward coordinate automorphism. -/
def boundedFlatAffineFullOpenSectionLaurentUnitIso (a : Under R) :
    𝟭 (BoundedFlatAffineFullOpenSections j ((laurentUnderFunctor R).obj a)) ≅
      𝟭 (BoundedFlatAffineFullOpenSections j ((laurentUnderFunctor R).obj a)) :=
  boundedFlatAffineFullOpenSectionUnitIso j ((laurentUnderFunctor R).obj a)
    (boundedFlatAffineFullOpenUnit j ((laurentUnderFunctor R).obj a) (laurentGlobalUnit a.right))

/-- Original evaluation retains exactly the inclusion-restricted original Laurent unit. -/
theorem boundedFlatAffineFullOpenSectionLaurentUnitIso_evaluation (a : Under R)
    (s : BoundedFlatAffineFullOpenSections j ((laurentUnderFunctor R).obj a)) :
    (boundedFlatAffineFullOpenOriginalEvaluation j ((laurentUnderFunctor R).obj a)).mapIso
        ((boundedFlatAffineFullOpenSectionLaurentUnitIso j a).app s) =
      (boundedFlatPerfectGlobalUnitIso (openSpace j ((laurentUnderFunctor R).obj a))
        (boundedFlatAffineFullOpenUnit j ((laurentUnderFunctor R).obj a)
          (laurentGlobalUnit a.right))).app
            ((boundedFlatAffineFullOpenOriginalEvaluation j
              ((laurentUnderFunctor R).obj a)).obj s) := by
  rw [boundedFlatAffineFullOpenSectionLaurentUnitIso]
  exact boundedFlatAffineFullOpenOriginalEvaluation_mapIso_sectionUnitIso j
    ((laurentUnderFunctor R).obj a)
    (boundedFlatAffineFullOpenUnit j ((laurentUnderFunctor R).obj a)
      (laurentGlobalUnit a.right)) s

/-- Every original Laurent coefficient arrow preserves the same forward section action. -/
theorem boundedFlatAffineFullOpenSectionLaurentUnitIso_coefficient {a b : Under R}
    (f : a ⟶ b) :
    Functor.whiskerRight (boundedFlatAffineFullOpenSectionLaurentUnitIso j a).hom
        (boundedFlatAffineFullOpenSectionsMap j ((laurentUnderFunctor R).map f)) =
      Functor.whiskerLeft
        (boundedFlatAffineFullOpenSectionsMap j ((laurentUnderFunctor R).map f))
        (boundedFlatAffineFullOpenSectionLaurentUnitIso j b).hom := by
  have hr : Units.map (Spec.map ((laurentUnderFunctor R).map f).right).appTop.hom.toMonoidHom
      (laurentGlobalUnit a.right) = laurentGlobalUnit b.right :=
    laurentGlobalUnit_coefficient f.right
  unfold boundedFlatAffineFullOpenSectionLaurentUnitIso
  simpa only [hr] using
    (boundedFlatAffineFullOpenSectionUnitIso_original_coefficient_hom j
      ((laurentUnderFunctor R).map f) (laurentGlobalUnit a.right))

end Quillen.PerfectComplexes
