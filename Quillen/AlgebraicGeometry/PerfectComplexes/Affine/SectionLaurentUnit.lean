/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionUnitNaturality
public import Quillen.AlgebraicGeometry.Scheme.Affine.LaurentUnitImage
public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Units

/-!
# The original Laurent unit on the strict section model

The section automorphism comes from the original Laurent global unit. At every actual coefficient
arrow from the Laurent ring its scalar is the image of the original coordinate, with the original
inverse coordinate. Coefficient reindexing commutes strictly with this action. This is the original
seed action; no new unit is supplied at later Bass iterates.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes

/-- The strict Laurent section action lifts the original coordinate global unit. -/
def boundedFlatAffineSectionLaurentUnitIso (R : CommRingCat.{u}) :
    𝟭 (BoundedFlatAffineSections (.of (LaurentPolynomial R))) ≅
      𝟭 (BoundedFlatAffineSections (.of (LaurentPolynomial R))) :=
  boundedFlatAffineSectionUnitIso (.of (LaurentPolynomial R)) (laurentGlobalUnit R)

/-- Every original coefficient arrow retains the actual pulled-back Laurent-unit automorphism. -/
theorem boundedFlatAffineSectionLaurentUnitIso_evaluation {R S : CommRingCat.{u}}
    (h : CommRingCat.of (LaurentPolynomial R) ⟶ S)
    (s : BoundedFlatAffineSections (.of (LaurentPolynomial R))) :
    (boundedFlatAffineEvaluationAt (.of (LaurentPolynomial R)) (Under.mk h)).mapIso
        ((boundedFlatAffineSectionLaurentUnitIso R).app s) =
      (boundedFlatPerfectGlobalUnitIso (Spec S)
        (Units.map (Spec.map h).appTop.hom.toMonoidHom (laurentGlobalUnit R))).app
          ((boundedFlatAffineEvaluationAt (.of (LaurentPolynomial R)) (Under.mk h)).obj s) :=
  boundedFlatAffineEvaluationAt_mapIso_sectionUnitIso _ _ s (Under.mk h)

/-- Actual Laurent coefficient restriction commutes strictly with the original unit action. -/
theorem boundedFlatAffineSectionLaurentUnitIso_coefficient {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Functor.whiskerRight (boundedFlatAffineSectionLaurentUnitIso R).hom
        (boundedFlatAffineSectionsMap (laurentMap f)) =
      Functor.whiskerLeft (boundedFlatAffineSectionsMap (laurentMap f))
        (boundedFlatAffineSectionLaurentUnitIso S).hom := by
  simpa only [boundedFlatAffineSectionLaurentUnitIso, laurentGlobalUnit_coefficient] using
    boundedFlatAffineSectionUnitIso_coefficient_hom (laurentMap f) (laurentGlobalUnit R)

/-- The forward action on every original complex term multiplies by the actual image of T. -/
theorem boundedFlatAffineSectionLaurentUnitIso_hom_terms {R S : CommRingCat.{u}}
    (h : CommRingCat.of (LaurentPolynomial R) ⟶ S)
    (s : BoundedFlatAffineSections (.of (LaurentPolynomial R))) (n : ℤ) :
    ((boundedFlatPerfect (Spec S)).ι.map
      ((boundedFlatAffineEvaluationAt (.of (LaurentPolynomial R)) (Under.mk h)).map
        ((boundedFlatAffineSectionLaurentUnitIso R).hom.app s))).f n =
      (AlgebraicGeometry.Scheme.Modules.globalScalar (Spec S)
        ((Scheme.ΓSpecIso S).inv (h.hom (LaurentPolynomial.T 1)))).app
          (((boundedFlatAffineEvaluationAt (.of (LaurentPolynomial R))
            (Under.mk h)).obj s).obj.X n) := by
  rw [boundedFlatAffineSectionLaurentUnitIso,
    boundedFlatAffineEvaluationAt_map_sectionUnitIso_hom]
  dsimp only [Under.mk, Under.right, Under.hom, StructuredArrow.mk]
  rw [boundedFlatPerfectGlobalUnitIso_hom_original, complexGlobalUnitIso_original_terms]
  dsimp only [AlgebraicGeometry.Scheme.Modules.globalUnitIso]
  congr 2
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso S).hom_inv_id _).symm.trans
    (congrArg (fun x ↦ (Scheme.ΓSpecIso S).inv x) (laurentGlobalUnit_image h))

/-- The inverse action on every original complex term multiplies by the image of T inverse. -/
theorem boundedFlatAffineSectionLaurentUnitIso_inv_terms {R S : CommRingCat.{u}}
    (h : CommRingCat.of (LaurentPolynomial R) ⟶ S)
    (s : BoundedFlatAffineSections (.of (LaurentPolynomial R))) (n : ℤ) :
    ((boundedFlatPerfect (Spec S)).ι.map
      ((boundedFlatAffineEvaluationAt (.of (LaurentPolynomial R)) (Under.mk h)).map
        ((boundedFlatAffineSectionLaurentUnitIso R).inv.app s))).f n =
      (AlgebraicGeometry.Scheme.Modules.globalScalar (Spec S)
        ((Scheme.ΓSpecIso S).inv (h.hom (LaurentPolynomial.T (-1))))).app
          (((boundedFlatAffineEvaluationAt (.of (LaurentPolynomial R))
            (Under.mk h)).obj s).obj.X n) := by
  rw [boundedFlatAffineSectionLaurentUnitIso,
    boundedFlatAffineEvaluationAt_map_sectionUnitIso_inv]
  dsimp only [Under.mk, Under.right, Under.hom, StructuredArrow.mk]
  rw [boundedFlatPerfectGlobalUnitIso_inv_terms]
  congr 2
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso S).hom_inv_id _).symm.trans
    (congrArg (fun x ↦ (Scheme.ΓSpecIso S).inv x) (laurentGlobalUnit_image_inv h))

end Quillen.PerfectComplexes
