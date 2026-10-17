/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassQuotientIso
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassMiddleExactness
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Naturally split original coefficient Bass rows

The actual common-corner quotient injects into the original Laurent group, and the literal
inverse Laurent unit splits the unchanged first-coordinate boundary naturally. Hence additive
Bass contraction preserves this constructed split row; no right-exactness claim is used to
preserve an unsupported middle exactness assertion.
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
variable [QuasiSeparatedSpace P.left]

omit [CompactSpace P.left] [QuasiSeparatedSpace P.left] in
/-- The original categorical corner has exactly the two original coefficient representatives. -/
theorem boundedFlatCoefficientCorner_pair (n : ℕ) (a : Under R)
    (x : BoundedFlatPerfectK (space (op P, a)) n) :
    (boundedFlatCoefficientCorner P n).app a (Additive.ofMul x) =
      (AddCommGrpCat.biprodIsoProd _ _).inv
        (Additive.ofMul ((boundedFlatCoefficientPairHom P a n x).1),
          Additive.ofMul ((boundedFlatCoefficientPairHom P a n x).2)) := by
  have h : (boundedFlatCoefficientCorner P n).app a =
      AddCommGrpCat.ofHom
        ((boundedFlatPerfectKPullback (polynomialProjection P a) n).toAdditive.prod
          (boundedFlatPerfectKPullback (polynomialProjection P a) n).toAdditive) ≫
        (AddCommGrpCat.biprodIsoProd
          ((boundedFlatCoefficientKAddFunctor P n).obj ((polynomialUnderFunctor R).obj a))
          ((boundedFlatCoefficientKAddFunctor P n).obj
            ((polynomialUnderFunctor R).obj a))).inv := by
    apply biprod.hom_ext
    · simp only [boundedFlatCoefficientCorner, biprod.lift_fst, Category.assoc,
        AddCommGrpCat.biprodIsoProd_inv_comp_fst]
      rfl
    · simp only [boundedFlatCoefficientCorner, biprod.lift_snd, Category.assoc,
        AddCommGrpCat.biprodIsoProd_inv_comp_snd]
      rfl
  exact ConcreteCategory.congr_hom h (Additive.ofMul x)

/-- The actual middle sequence is exact at every original coefficient object. -/
theorem boundedFlatCoefficientMiddleSequence_evaluation_exact (n : ℕ) (a : Under R) :
    ((boundedFlatCoefficientMiddleSequence P n).map
      ((evaluation (Under R) AddCommGrpCat).obj a)).Exact := by
  apply (ShortComplex.ab_exact_iff _).mpr
  intro x hx
  obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (AddCommGrpCat.biprodIsoProd
      ((boundedFlatCoefficientKAddFunctor P n).obj ((polynomialUnderFunctor R).obj a))
      ((boundedFlatCoefficientKAddFunctor P n).obj ((polynomialUnderFunctor R).obj a))).inv).2 x
  change (boundedFlatCoefficientDifference P n).app a
    ((AddCommGrpCat.biprodIsoProd _ _).inv y) = 0 at hx
  have he := boundedFlatCoefficientDifference_pair P a n y.1.toMul y.2.toMul
  change (boundedFlatCoefficientDifference P n).app a
    ((AddCommGrpCat.biprodIsoProd _ _).inv y) =
      Additive.ofMul (boundedFlatCoefficientDifferenceHom P a n (y.1.toMul, y.2.toMul)) at he
  have hk : (y.1.toMul, y.2.toMul) ∈ (boundedFlatCoefficientDifferenceHom P a n).ker :=
    he.symm.trans hx
  rw [← boundedFlatCoefficientPair_range_eq_difference_ker] at hk
  obtain ⟨z, hz⟩ := hk
  refine ⟨Additive.ofMul z, ?_⟩
  change (boundedFlatCoefficientCorner P n).app a (Additive.ofMul z) = _
  exact (boundedFlatCoefficientCorner_pair P n a z).trans
    (congrArg (fun t => (AddCommGrpCat.biprodIsoProd
      ((boundedFlatCoefficientKAddFunctor P n).obj ((polynomialUnderFunctor R).obj a))
      ((boundedFlatCoefficientKAddFunctor P n).obj ((polynomialUnderFunctor R).obj a))).inv
      (Additive.ofMul t.1, Additive.ofMul t.2)) hz)

/-- Actual global middle exactness holds in the category of coefficient functors. -/
theorem boundedFlatCoefficientMiddleSequence_exact (n : ℕ) :
    (boundedFlatCoefficientMiddleSequence P n).Exact := by
  let S := boundedFlatCoefficientMiddleSequence P n
  rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
  apply NatTrans.ext
  funext a
  change 𝟙 (S.homology.obj a) = 0
  exact (IsZero.of_iso
    ((ShortComplex.exact_iff_isZero_homology _).mp
      (boundedFlatCoefficientMiddleSequence_evaluation_exact P n a))
    (S.mapHomologyIso ((evaluation (Under R) AddCommGrpCat).obj a)).symm).eq_of_src _ _

/-- The actual descended difference is injective as a natural transformation. -/
instance boundedFlatCoefficientDifferenceDesc_mono (n : ℕ) :
    Mono (boundedFlatCoefficientDifferenceDesc P n) :=
  (boundedFlatCoefficientMiddleSequence_exact P n).mono_cokernelDesc

/-- The same original Laurent difference and natural original boundary form the final row. -/
def boundedFlatCoefficientNaturalBoundarySequence (n : ℕ) :
    ShortComplex (Under R ⥤ AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk (boundedFlatCoefficientDifference P (n + 1))
    (boundedFlatCoefficientPositiveBassBoundaryNatTrans P n) (by
      apply NatTrans.ext
      funext a
      simpa only [NatTrans.comp_app, NatTrans.app_zero,
        boundedFlatCoefficientPositiveBassBoundaryNatTrans_app] using
        boundedFlatCoefficientDifference_boundary P a n)

/-- Exactness of the unchanged boundary is natural in every coefficient object. -/
theorem boundedFlatCoefficientNaturalBoundarySequence_exact (n : ℕ) :
    (boundedFlatCoefficientNaturalBoundarySequence P n).Exact := by
  let S := boundedFlatCoefficientNaturalBoundarySequence P n
  rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
  apply NatTrans.ext
  funext a
  change 𝟙 (S.homology.obj a) = 0
  have h : (S.map ((evaluation (Under R) AddCommGrpCat).obj a)).Exact := by
    apply (ShortComplex.ab_exact_iff _).mpr
    intro x hx
    change (boundedFlatCoefficientPositiveBassBoundaryNatTrans P n).app a x = 0 at hx
    rw [boundedFlatCoefficientPositiveBassBoundaryNatTrans_app] at hx
    exact (ShortComplex.ab_exact_iff _).mp
      (boundedFlatCoefficientBoundarySequence_exact P a n) x hx
  exact (IsZero.of_iso ((ShortComplex.exact_iff_isZero_homology _).mp h)
    (S.mapHomologyIso ((evaluation (Under R) AddCommGrpCat).obj a)).symm).eq_of_src _ _

/-- The original corner quotient, original Laurent group, and original coefficient group. -/
def boundedFlatCoefficientSplitBoundarySequence (n : ℕ) :
    ShortComplex (Under R ⥤ AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk (boundedFlatCoefficientDifferenceDesc P (n + 1))
    (boundedFlatCoefficientPositiveBassBoundaryNatTrans P n) (by
      apply (cancel_epi (cokernel.π (boundedFlatCoefficientCorner P (n + 1)))).mp
      rw [← Category.assoc, boundedFlatCoefficientDifferenceDesc_π, comp_zero]
      exact (boundedFlatCoefficientNaturalBoundarySequence P n).zero)

/-- Passing to the actual corner cokernel retains the exact original boundary row. -/
theorem boundedFlatCoefficientSplitBoundarySequence_exact (n : ℕ) :
    (boundedFlatCoefficientSplitBoundarySequence P n).Exact := by
  let φ : boundedFlatCoefficientNaturalBoundarySequence P n ⟶
      boundedFlatCoefficientSplitBoundarySequence P n :=
    { τ₁ := cokernel.π (boundedFlatCoefficientCorner P (n + 1))
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [boundedFlatCoefficientNaturalBoundarySequence,
        boundedFlatCoefficientSplitBoundarySequence]
      comm₂₃ := by
        simp only [Category.id_comp, Category.comp_id]
        rfl }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp
    (boundedFlatCoefficientNaturalBoundarySequence_exact P n)

/-- The literal inverse Laurent unit splits the original boundary as natural transformations. -/
@[reassoc (attr := simp)]
theorem boundedFlatCoefficientInverseUnitSection_boundary (n : ℕ) :
    boundedFlatCoefficientInverseUnitSection P n ≫
      boundedFlatCoefficientPositiveBassBoundaryNatTrans P n = 𝟙 _ := by
  change _ ≫ (_ ≫ inv (boundedFlatCoefficientInverseUnitQuotient P n)) = _
  rw [← Category.assoc]
  exact IsIso.hom_inv_id (boundedFlatCoefficientInverseUnitQuotient P n)

/-- A genuine natural splitting, with the unchanged inverse-unit section. -/
def boundedFlatCoefficientBoundarySplitting (n : ℕ) :
    (boundedFlatCoefficientSplitBoundarySequence P n).Splitting :=
  ShortComplex.Splitting.ofExactOfSection _
    (boundedFlatCoefficientSplitBoundarySequence_exact P n)
    (boundedFlatCoefficientInverseUnitSection P n)
    (boundedFlatCoefficientInverseUnitSection_boundary P n)
    (boundedFlatCoefficientDifferenceDesc_mono P (n + 1))

/-- The actual additive contraction preserves this constructed split boundary row. -/
def boundedFlatCoefficientContractedBoundarySplitting (n : ℕ) :
    ((boundedFlatCoefficientSplitBoundarySequence P n).map
      (contractionFunctor (underToLaurent R) (underToLaurentInvert R))).Splitting :=
  (boundedFlatCoefficientBoundarySplitting P n).map
    (contractionFunctor (underToLaurent R) (underToLaurentInvert R))

end Quillen.PerfectComplexes
