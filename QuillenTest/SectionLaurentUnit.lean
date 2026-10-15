/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionLaurentPullback
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionZero

/-!
Actual section transitions, arbitrary Laurent coefficient images and the original chosen zero.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.PolynomialLaurent
open Quillen.PerfectComplexes

noncomputable section
open CategoryTheory AlgebraicGeometry
  AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace QuillenTest.SectionLaurentUnit

open Quillen

/-- The actual coordinate action is a vertical natural transformation along every section arrow. -/
theorem original_section_transition (R : CommRingCat.{u})
    (s : BoundedFlatAffineSections (.of (LaurentPolynomial R)))
    {i j : Under (CommRingCat.of (LaurentPolynomial R))} (a : i ⟶ j) :
    let φ : s ⟶ s := (boundedFlatAffineSectionLaurentUnitIso R).hom.app s
    s.obj.val.map a ≫ φ.hom.val.app j = φ.hom.val.app i ≫ s.obj.val.map a := by
  exact (fun φ : s ⟶ s ↦ φ.hom.val.naturality a)
    ((boundedFlatAffineSectionLaurentUnitIso R).hom.app s)

/-- After any independent second coefficient map the original scalar remains the image of T. -/
theorem further_coefficient_scalar {R S T : CommRingCat.{u}}
    (h : CommRingCat.of (LaurentPolynomial R) ⟶ S) (g : S ⟶ T) :
    (Scheme.ΓSpecIso T).hom
        (↑(Units.map (Spec.map (h ≫ g)).appTop.hom.toMonoidHom (laurentGlobalUnit R))) =
      g.hom (h.hom (LaurentPolynomial.T 1)) :=
  laurentGlobalUnit_image (h ≫ g)

/-- Independent further coefficients likewise preserve the original inverse coordinate. -/
theorem further_coefficient_inverse_scalar {R S T : CommRingCat.{u}}
    (h : CommRingCat.of (LaurentPolynomial R) ⟶ S) (g : S ⟶ T) :
    (Scheme.ΓSpecIso T).hom
        (↑((Units.map (Spec.map (h ≫ g)).appTop.hom.toMonoidHom (laurentGlobalUnit R))⁻¹)) =
      g.hom (h.hom (LaurentPolynomial.T (-1))) :=
  laurentGlobalUnit_image_inv (h ≫ g)

/-- The unchanged section action retains the original coordinate after two coefficient arrows. -/
theorem further_coefficient_action_on_terms {R S T : CommRingCat.{u}}
    (h : CommRingCat.of (LaurentPolynomial R) ⟶ S) (g : S ⟶ T)
    (s : BoundedFlatAffineSections (.of (LaurentPolynomial R))) (n : ℤ) :
    ((boundedFlatPerfect (Spec T)).ι.map
      ((boundedFlatAffineEvaluationAt (.of (LaurentPolynomial R)) (Under.mk (h ≫ g))).map
        ((boundedFlatAffineSectionLaurentUnitIso R).hom.app s))).f n =
      (AlgebraicGeometry.Scheme.Modules.globalScalar (Spec T)
        ((Scheme.ΓSpecIso T).inv (g.hom (h.hom (LaurentPolynomial.T 1))))).app
          (((boundedFlatAffineEvaluationAt (.of (LaurentPolynomial R))
            (Under.mk (h ≫ g))).obj s).obj.X n) :=
  boundedFlatAffineSectionLaurentUnitIso_hom_terms (h ≫ g) s n

/-- The inverse section action likewise retains the original inverse coordinate after both maps. -/
theorem further_coefficient_inverse_action_on_terms {R S T : CommRingCat.{u}}
    (h : CommRingCat.of (LaurentPolynomial R) ⟶ S) (g : S ⟶ T)
    (s : BoundedFlatAffineSections (.of (LaurentPolynomial R))) (n : ℤ) :
    ((boundedFlatPerfect (Spec T)).ι.map
      ((boundedFlatAffineEvaluationAt (.of (LaurentPolynomial R)) (Under.mk (h ≫ g))).map
        ((boundedFlatAffineSectionLaurentUnitIso R).inv.app s))).f n =
      (AlgebraicGeometry.Scheme.Modules.globalScalar (Spec T)
        ((Scheme.ΓSpecIso T).inv (g.hom (h.hom (LaurentPolynomial.T (-1)))))).app
          (((boundedFlatAffineEvaluationAt (.of (LaurentPolynomial R))
            (Under.mk (h ≫ g))).obj s).obj.X n) :=
  boundedFlatAffineSectionLaurentUnitIso_inv_terms (h ≫ g) s n

/-- The section coordinate action fixes the original pointwise chosen zero by its unique map. -/
theorem original_zero_action (R : CommRingCat.{u}) :
    (boundedFlatAffineSectionLaurentUnitIso R).hom.app
        (boundedFlatAffineSectionZero (.of (LaurentPolynomial R))) =
      𝟙 (boundedFlatAffineSectionZero (.of (LaurentPolynomial R))) :=
  (isZero_boundedFlatAffineSectionZero (.of (LaurentPolynomial R))).eq_of_src _ _

/-- Forward and inverse actions cancel after every actual arrow evaluation. -/
theorem original_evaluated_inverse {R S : CommRingCat.{u}}
    (h : CommRingCat.of (LaurentPolynomial R) ⟶ S)
    (s : BoundedFlatAffineSections (.of (LaurentPolynomial R))) :
    (boundedFlatAffineEvaluationAt (.of (LaurentPolynomial R)) (Under.mk h)).map
        ((boundedFlatAffineSectionLaurentUnitIso R).hom.app s) ≫
      (boundedFlatAffineEvaluationAt (.of (LaurentPolynomial R)) (Under.mk h)).map
        ((boundedFlatAffineSectionLaurentUnitIso R).inv.app s) =
      𝟙 ((boundedFlatAffineEvaluationAt (.of (LaurentPolynomial R)) (Under.mk h)).obj s) := by
  rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app]
  exact CategoryTheory.Functor.map_id _ _

end QuillenTest.SectionLaurentUnit
