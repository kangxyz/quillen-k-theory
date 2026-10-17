/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionEvaluationNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeBassCharts
public import Aglib.AlgebraicGeometry.BaseChange.Coefficients.PolynomialLaurent

/-!
# Original coefficient K-groups and the native polynomial/Laurent charts

The chosen polynomial and Laurent fiber isomorphisms, followed by the literal bounded-flat
inclusion, give actual K-equivalences. Both original chart maps and the original polynomial
coefficient map commute with these comparisons. Compactness is the only geometric hypothesis.
-/
@[expose] public section
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes

private theorem boundedFlatK_flat_square {A B C D : Scheme.{u}}
    (f : A ⟶ B) [Flat f] (g : C ⟶ D) (i : A ⟶ C) (j : B ⟶ D)
    (h : i ≫ g = f ≫ j) (n : ℕ) :
    (perfectKFlatPullback f n).comp
        ((boundedFlatPerfectToPerfectKMap B n).comp (boundedFlatPerfectKPullback j n)) =
      (boundedFlatPerfectToPerfectKMap A n).comp
        ((boundedFlatPerfectKPullback i n).comp (boundedFlatPerfectKPullback g n)) := by
  rw [← MonoidHom.comp_assoc, boundedFlatPerfectToPerfectKMap_flatPullback,
    MonoidHom.comp_assoc, ← boundedFlatPerfectKPullback_comp, ← h,
    boundedFlatPerfectKPullback_comp]

variable {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left] (a : Under R)
local notation "X" => Opposite.unop (Functor.obj (boundedFlatCoefficientQuasiCompactRow P) a)

/-- The actual chosen polynomial inverse and original model inclusion give this K-equivalence. -/
def boundedFlatCoefficientNativePolynomialKEquiv (n : ℕ) :
    BoundedFlatPerfectK (space (op P, (polynomialUnderFunctor R).obj a)) n ≃*
      PerfectK (Relative.polynomialFunctor.obj X).obj n :=
  (((BoundedFlatPerfectKFunctor n).mapIso (polynomialIso P a).symm.op).groupIsoToMulEquiv).trans
    (boundedFlatPerfectKEquiv (Relative.polynomialFunctor.obj X).obj n)

/-- The Laurent comparison likewise keeps its original geometric inverse and model inclusion. -/
def boundedFlatCoefficientNativeLaurentKEquiv (n : ℕ) :
    BoundedFlatPerfectK (space (op P, (laurentUnderFunctor R).obj a)) n ≃*
      PerfectK (Relative.laurentFunctor.obj X).obj n :=
  (((BoundedFlatPerfectKFunctor n).mapIso (laurentIso P a).symm.op).groupIsoToMulEquiv).trans
    (boundedFlatPerfectKEquiv (Relative.laurentFunctor.obj X).obj n)

/-- The polynomial comparison's forward map is literally the displayed original composite. -/
theorem boundedFlatCoefficientNativePolynomialKEquiv_hom (n : ℕ) :
    (boundedFlatCoefficientNativePolynomialKEquiv P a n).toMonoidHom =
      (boundedFlatPerfectToPerfectKMap (Relative.polynomialFunctor.obj X).obj n).comp
        (boundedFlatPerfectKPullback (polynomialIso P a).inv n) := rfl

/-- The Laurent comparison's forward map is the same original geometric/model composite. -/
theorem boundedFlatCoefficientNativeLaurentKEquiv_hom (n : ℕ) :
    (boundedFlatCoefficientNativeLaurentKEquiv P a n).toMonoidHom =
      (boundedFlatPerfectToPerfectKMap (Relative.laurentFunctor.obj X).obj n).comp
        (boundedFlatPerfectKPullback (laurentIso P a).inv n) := rfl

/-- Original positive-chart pullback commutes with the actual native K-comparisons. -/
theorem boundedFlatCoefficientNativeKEquiv_plus (n : ℕ) :
    (perfectKRestrict (Relative.plus.app X).hom n).comp
      (boundedFlatCoefficientNativePolynomialKEquiv P a n).toMonoidHom =
      (boundedFlatCoefficientNativeLaurentKEquiv P a n).toMonoidHom.comp
        (boundedFlatPerfectKPullback (laurentPlus P a) n) := by
  have h : (laurentIso P a).inv ≫ laurentPlus P a =
      (Relative.plus.app X).hom ≫ (polynomialIso P a).inv := by
    apply (cancel_mono (polynomialIso P a).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [polynomialLaurentIso_plus, Iso.inv_hom_id_assoc]
    rfl
  have hk := boundedFlatK_flat_square (Relative.plus.app X).hom
    (laurentPlus P a) (laurentIso P a).inv (polynomialIso P a).inv h n
  simpa only [boundedFlatCoefficientNativePolynomialKEquiv_hom,
    boundedFlatCoefficientNativeLaurentKEquiv_hom, perfectKFlatPullback_eq_restrict,
    MonoidHom.comp_assoc] using hk

/-- The original inverse-coordinate chart has the same literal comparison square. -/
theorem boundedFlatCoefficientNativeKEquiv_minus (n : ℕ) :
    (perfectKRestrict (Relative.minus.app X).hom n).comp
      (boundedFlatCoefficientNativePolynomialKEquiv P a n).toMonoidHom =
      (boundedFlatCoefficientNativeLaurentKEquiv P a n).toMonoidHom.comp
        (boundedFlatPerfectKPullback (laurentMinus P a) n) := by
  have h : (laurentIso P a).inv ≫ laurentMinus P a =
      (Relative.minus.app X).hom ≫ (polynomialIso P a).inv := by
    apply (cancel_mono (polynomialIso P a).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [polynomialLaurentIso_minus, Iso.inv_hom_id_assoc]
    rfl
  have hk := boundedFlatK_flat_square (Relative.minus.app X).hom
    (laurentMinus P a) (laurentIso P a).inv (polynomialIso P a).inv h n
  simpa only [boundedFlatCoefficientNativePolynomialKEquiv_hom,
    boundedFlatCoefficientNativeLaurentKEquiv_hom, perfectKFlatPullback_eq_restrict,
    MonoidHom.comp_assoc] using hk

/-- The unchanged polynomial coefficient inclusion commutes with these actual comparisons. -/
theorem boundedFlatCoefficientNativeKEquiv_coefficient (n : ℕ) :
    (perfectKFlatPullback (Relative.polynomialProjection.app X).hom n).comp
      (boundedFlatPerfectToPerfectKMap (space (op P, a)) n) =
      (boundedFlatCoefficientNativePolynomialKEquiv P a n).toMonoidHom.comp
        (boundedFlatPerfectKPullback (polynomialProjection P a) n) := by
  have h : (polynomialIso P a).inv ≫ polynomialProjection P a =
      (Relative.polynomialProjection.app X).hom ≫ 𝟙 (X).obj := by
    change (polynomialIso P a).inv ≫ polynomialProjection P a =
      pullback.fst _ _ ≫ 𝟙 _
    rw [Category.comp_id, ← polynomialIso_hom_fst, Iso.inv_hom_id_assoc]
  have hk := boundedFlatK_flat_square (B := (X).obj) (D := (X).obj)
    (Relative.polynomialProjection.app X).hom
    (polynomialProjection P a) (polynomialIso P a).inv (𝟙 (X).obj) h n
  change (perfectKFlatPullback (Relative.polynomialProjection.app X).hom n).comp
      (boundedFlatPerfectToPerfectKMap (space (op P, a)) n) =
    (boundedFlatPerfectToPerfectKMap (Relative.polynomialFunctor.obj X).obj n).comp
      ((boundedFlatPerfectKPullback (polynomialIso P a).inv n).comp
        (boundedFlatPerfectKPullback (polynomialProjection P a) n))
  simpa only [boundedFlatPerfectKPullback_id, MonoidHom.comp_id,
    boundedFlatCoefficientQuasiCompactRow] using hk

end Quillen.PerfectComplexes
