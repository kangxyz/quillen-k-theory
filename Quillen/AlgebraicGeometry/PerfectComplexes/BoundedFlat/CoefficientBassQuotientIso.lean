/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassBoundary
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCornerComplex

/-!
# The original inverse-unit isomorphism of coefficient Bass quotients

The unchanged geometric first-coordinate boundary is a cokernel of the original two-chart
map. Its unique cokernel comparison identifies the original inverse-unit quotient map as an
isomorphism. Taking the inverse of this already natural map proves naturality of the same
geometric boundary under every coefficient map, without a nonflat perfect-pullback argument.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Bass.TwoChart
universe u
namespace Quillen.PerfectComplexes
attribute [local instance] Waldhausen.Additivity.KCommGroup
variable {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left]
variable [QuasiSeparatedSpace P.left] (a : Under R)

/-- The same actual first-coordinate boundary on the additive coefficient groups. -/
def boundedFlatCoefficientPositiveBassBoundaryAdd (n : ℕ) :
    (laurentUnderFunctor R ⋙ boundedFlatCoefficientKAddFunctor P (n + 1)).obj a ⟶
      (boundedFlatCoefficientKAddFunctor P n).obj a :=
  AddCommGrpCat.ofHom (boundedFlatCoefficientPositiveBassBoundary P a n).toAdditive

omit [CompactSpace P.left] [QuasiSeparatedSpace P.left] in
/-- The categorical difference has the literal original multiplicative representative. -/
theorem boundedFlatCoefficientDifference_pair (n : ℕ)
    (x y : BoundedFlatPerfectK (space (op P, (polynomialUnderFunctor R).obj a)) n) :
    (boundedFlatCoefficientDifference P n).app a
        ((AddCommGrpCat.biprodIsoProd _ _).inv (Additive.ofMul x, Additive.ofMul y)) =
      Additive.ofMul (boundedFlatCoefficientDifferenceHom P a n (x, y)) := by
  refine (polynomialDifference_pair (underToLaurent R) (underToLaurentInvert R)
    (boundedFlatCoefficientKAddFunctor P n) a (Additive.ofMul x) (Additive.ofMul y)).trans ?_
  change Additive.ofMul (boundedFlatPerfectKPullback (laurentPlus P a) n x /
    boundedFlatPerfectKPullback (laurentMinus P a) n y) =
      Additive.ofMul (boundedFlatPerfectKPullback (laurentPlus P a) n x *
        (boundedFlatPerfectKPullback (laurentMinus P a) n y)⁻¹)
  rw [div_eq_mul_inv]

/-- The unchanged first-coordinate boundary kills the original chart difference. -/
theorem boundedFlatCoefficientDifference_boundary (n : ℕ) :
    (boundedFlatCoefficientDifference P (n + 1)).app a ≫
      boundedFlatCoefficientPositiveBassBoundaryAdd P a n = 0 := by
  let e := AddCommGrpCat.biprodIsoProd
    ((boundedFlatCoefficientKAddFunctor P (n + 1)).obj ((polynomialUnderFunctor R).obj a))
    ((boundedFlatCoefficientKAddFunctor P (n + 1)).obj ((polynomialUnderFunctor R).obj a))
  apply (cancel_epi e.inv).mp
  apply AddCommGrpCat.hom_ext
  ext x
  change boundedFlatCoefficientPositiveBassBoundaryAdd P a n
      ((boundedFlatCoefficientDifference P (n + 1)).app a (e.inv x)) = 0
  have he := boundedFlatCoefficientDifference_pair P a (n + 1) x.1.toMul x.2.toMul
  change (boundedFlatCoefficientDifference P (n + 1)).app a (e.inv x) =
    Additive.ofMul (boundedFlatCoefficientDifferenceHom P a (n + 1)
      (x.1.toMul, x.2.toMul)) at he
  have h : boundedFlatCoefficientDifferenceHom P a (n + 1) (x.1.toMul, x.2.toMul) ∈
      (boundedFlatCoefficientDifferenceHom P a (n + 1)).range := ⟨_, rfl⟩
  rw [boundedFlatCoefficientDifference_range_eq_bassBoundary_ker] at h
  exact (congrArg (boundedFlatCoefficientPositiveBassBoundaryAdd P a n) he).trans h

/-- The original Laurent term and original boundary form the actual final short complex. -/
def boundedFlatCoefficientBoundarySequence (n : ℕ) : ShortComplex AddCommGrpCat.{u + 1} :=
  ShortComplex.mk ((boundedFlatCoefficientDifference P (n + 1)).app a)
    (boundedFlatCoefficientPositiveBassBoundaryAdd P a n)
    (boundedFlatCoefficientDifference_boundary P a n)

/-- Exactness of the actual additive boundary row follows from its unchanged geometric kernel. -/
theorem boundedFlatCoefficientBoundarySequence_exact (n : ℕ) :
    (boundedFlatCoefficientBoundarySequence P a n).Exact := by
  apply (ShortComplex.ab_exact_iff _).mpr
  intro x hx
  have hk : x.toMul ∈ (boundedFlatCoefficientPositiveBassBoundary P a n).ker := hx
  rw [← boundedFlatCoefficientDifference_range_eq_bassBoundary_ker] at hk
  obtain ⟨⟨y, z⟩, hyz⟩ := hk
  refine ⟨(AddCommGrpCat.biprodIsoProd _ _).inv (Additive.ofMul y, Additive.ofMul z), ?_⟩
  exact (boundedFlatCoefficientDifference_pair P a (n + 1) y z).trans
    (congrArg Additive.ofMul hyz)

instance boundedFlatCoefficientPositiveBassBoundaryAdd_epi (n : ℕ) :
    Epi (boundedFlatCoefficientPositiveBassBoundaryAdd P a n) :=
  (AddCommGrpCat.epi_iff_surjective _).mpr
    (boundedFlatCoefficientPositiveBassBoundary_surjective P a n)

/-- The unique comparison of the original quotient with the original geometric cokernel. -/
def boundedFlatCoefficientPositiveBassBoundaryQuotientIso (n : ℕ) :
    (contraction (underToLaurent R) (underToLaurentInvert R)
      (boundedFlatCoefficientKAddFunctor P (n + 1))).obj a ≅
        (boundedFlatCoefficientKAddFunctor P n).obj a := by
  let S := boundedFlatCoefficientBoundarySequence P a n
  letI : Epi S.g := boundedFlatCoefficientPositiveBassBoundaryAdd_epi P a n
  exact IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.f)
    (boundedFlatCoefficientBoundarySequence_exact P a n).gIsCokernel

/-- This comparison retains precisely the original quotient and first-coordinate boundary. -/
@[reassoc (attr := simp)]
theorem boundedFlatCoefficientPositiveBassBoundaryQuotientIso_π (n : ℕ) :
    (contractionπ (underToLaurent R) (underToLaurentInvert R)
      (boundedFlatCoefficientKAddFunctor P (n + 1))).app a ≫
        (boundedFlatCoefficientPositiveBassBoundaryQuotientIso P a n).hom =
      boundedFlatCoefficientPositiveBassBoundaryAdd P a n := by
  let S := boundedFlatCoefficientBoundarySequence P a n
  let : Epi S.g := boundedFlatCoefficientPositiveBassBoundaryAdd_epi P a n
  exact IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel S.f)
    (boundedFlatCoefficientBoundarySequence_exact P a n).gIsCokernel WalkingParallelPair.one

/-- The actual inverse-unit quotient is the inverse of the unchanged boundary comparison. -/
theorem boundedFlatCoefficientInverseUnitQuotient_eq_inv (n : ℕ) :
    (boundedFlatCoefficientInverseUnitQuotient P n).app a =
      (boundedFlatCoefficientPositiveBassBoundaryQuotientIso P a n).inv := by
  apply (cancel_mono (boundedFlatCoefficientPositiveBassBoundaryQuotientIso P a n).hom).mp
  rw [Iso.inv_hom_id, boundedFlatCoefficientInverseUnitQuotient_app, Category.assoc,
    boundedFlatCoefficientPositiveBassBoundaryQuotientIso_π]
  apply AddCommGrpCat.hom_ext
  exact congrArg MonoidHom.toAdditive
    (boundedFlatCoefficientPositiveBassBoundary_comp_inverse P a n)

instance boundedFlatCoefficientInverseUnitQuotient_app_isIso (n : ℕ) :
    IsIso ((boundedFlatCoefficientInverseUnitQuotient P n).app a) := by
  rw [boundedFlatCoefficientInverseUnitQuotient_eq_inv]
  infer_instance

instance boundedFlatCoefficientInverseUnitQuotient_isIso (n : ℕ) :
    IsIso (boundedFlatCoefficientInverseUnitQuotient P n) :=
  NatIso.isIso_of_isIso_app _

/-- The unchanged boundary is natural under every coefficient map, via its actual inverse. -/
def boundedFlatCoefficientPositiveBassBoundaryNatTrans (n : ℕ) :
    laurentUnderFunctor R ⋙ boundedFlatCoefficientKAddFunctor P (n + 1) ⟶
      boundedFlatCoefficientKAddFunctor P n :=
  contractionπ (underToLaurent R) (underToLaurentInvert R)
    (boundedFlatCoefficientKAddFunctor P (n + 1)) ≫
      inv (boundedFlatCoefficientInverseUnitQuotient P n)

/-- Every component of the natural boundary is the original geometric first coordinate. -/
@[simp]
theorem boundedFlatCoefficientPositiveBassBoundaryNatTrans_app (n : ℕ) :
    (boundedFlatCoefficientPositiveBassBoundaryNatTrans P n).app a =
      boundedFlatCoefficientPositiveBassBoundaryAdd P a n := by
  simp only [boundedFlatCoefficientPositiveBassBoundaryNatTrans, NatTrans.comp_app,
    NatIso.isIso_inv_app, boundedFlatCoefficientInverseUnitQuotient_eq_inv, IsIso.Iso.inv_inv,
    boundedFlatCoefficientPositiveBassBoundaryQuotientIso_π]

end Quillen.PerfectComplexes
