/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeTwoSummands
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.RestrictionIsoEquivalence
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.NativeBaseChange
public import Quillen.AlgebraicGeometry.PerfectComplexes.MayerVietoris

/-!
# Original native Bass charts and connective Mayer–Vietoris exactness

The actual native projective-line cover transports connective Mayer–Vietoris exactness to
both original polynomial charts and their original signed Laurent difference. The restriction
pair has exactly that difference kernel, including degree zero. No negative exactness,
projective-bundle equivalence or Laurent-unit section is assumed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes.ProjectiveLine.NativeBass
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative

/-- The commutative group structure on connective perfect K-theory supplied by Waldhausen
additivity. -/
local instance (Y : Scheme.{u}) (n : ℕ) : CommGroup (PerfectK Y n) :=
  Waldhausen.Additivity.KCommGroup (perfectWaldhausen Y) n

variable (X : QuasiCompactSchemes.{u})

/-- The range of the original native positive polynomial chart. -/
def positiveOpen : (nativeLineFunctor.obj X).obj.Opens :=
  (nativePlus.app X).hom.opensRange

/-- The literal intersection open in the original negative chart. -/
def overlapOpen : (polynomialFunctor.obj X).obj.Opens :=
  (nativeMinus.app X).hom ⁻¹ᵁ positiveOpen X

/-- The actual native Laurent chart has precisely this intersection as its range. -/
theorem minus_opensRange :
    (PolynomialLaurent.Relative.minus.app X).hom.opensRange = overlapOpen X := by
  let h := (native_chart_isPullback X).flip
  have hh : (h.isoPullback.hom ≫ pullback.fst
      (nativeMinus.app X).hom (nativePlus.app X).hom).opensRange =
      (nativeMinus.app X).hom ⁻¹ᵁ (nativePlus.app X).hom.opensRange := by
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_pullbackFst]
  simpa only [h.isoPullback_hom_fst, overlapOpen, positiveOpen] using hh

/-- The actual positive polynomial chart identifies its original range open. -/
def positiveOpenIso : (polynomialFunctor.obj X).obj ≅ (positiveOpen X).toScheme :=
  IsOpenImmersion.isoOfRangeEq (nativePlus.app X).hom (positiveOpen X).ι (by
    change ((nativePlus.app X).hom.opensRange : Set (nativeLineFunctor.obj X).obj) = _
    exact Subtype.range_coe.symm)

/-- The actual Laurent scheme identifies the original intersection open. -/
def overlapOpenIso : (laurentFunctor.obj X).obj ≅ (overlapOpen X).toScheme :=
  IsOpenImmersion.isoOfRangeEq (PolynomialLaurent.Relative.minus.app X).hom (overlapOpen X).ι (by
    change ((PolynomialLaurent.Relative.minus.app X).hom.opensRange :
      Set (polynomialFunctor.obj X).obj) = _
    rw [minus_opensRange]
    exact Subtype.range_coe.symm)

@[reassoc (attr := simp)]
theorem positiveOpenIso_hom_inclusion :
    (positiveOpenIso X).hom ≫ (positiveOpen X).ι = (nativePlus.app X).hom :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)]
theorem overlapOpenIso_hom_inclusion :
    (overlapOpenIso X).hom ≫ (overlapOpen X).ι = (PolynomialLaurent.Relative.minus.app X).hom :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The same overlap isomorphism preserves the original positive Laurent leg. -/
@[reassoc]
theorem overlapOpenIso_hom_toPositive :
    (overlapOpenIso X).hom ≫
        (nativeMinus.app X).hom.resLE (positiveOpen X) (overlapOpen X) le_rfl =
      (PolynomialLaurent.Relative.plus.app X).hom ≫ (positiveOpenIso X).hom := by
  apply (cancel_mono (positiveOpen X).ι).mp
  rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
    overlapOpenIso_hom_inclusion, Category.assoc, positiveOpenIso_hom_inclusion]
  exact (native_chart_isPullback X).w.symm

/-- Compactness comes from the original native polynomial source. -/
theorem positiveOpen_isCompact :
    IsCompact (positiveOpen X : Set (nativeLineFunctor.obj X).obj) :=
  isCompact_range (nativePlus.app X).hom.continuous

/-- The original negative chart and positive range form the actual projective-line cover. -/
theorem chart_cover (x : (nativeLineFunctor.obj X).obj) :
    x ∈ Set.range (nativeMinus.app X).hom ∨ x ∈ positiveOpen X := by
  rcases native_charts_cover X x with hx | hx
  · exact Or.inr hx
  · exact Or.inl hx

/-- The original two polynomial restrictions, in positive-negative order. -/
def restrictionPair (n : ℕ) : PerfectK (nativeLineFunctor.obj X).obj n →*
    PerfectK (polynomialFunctor.obj X).obj n × PerfectK (polynomialFunctor.obj X).obj n :=
  (perfectKRestrict (nativePlus.app X).hom n).prod
    (perfectKRestrict (nativeMinus.app X).hom n)

/-- Original positive Laurent restriction times inverse negative Laurent restriction. -/
def laurentDifference (n : ℕ) :
    PerfectK (polynomialFunctor.obj X).obj n × PerfectK (polynomialFunctor.obj X).obj n →*
      PerfectK (laurentFunctor.obj X).obj n :=
  GroupMayerVietoris.difference (perfectKRestrict (PolynomialLaurent.Relative.plus.app X).hom n)
    (perfectKRestrict (PolynomialLaurent.Relative.minus.app X).hom n)

/-- Polynomial coefficient extension into the original two chart factors. -/
def coefficientPair (n : ℕ) : PerfectK X.obj n →*
    PerfectK (polynomialFunctor.obj X).obj n × PerfectK (polynomialFunctor.obj X).obj n :=
  (perfectKFlatPullback (polynomialProjection.app X).hom n).prod
    (perfectKFlatPullback (polynomialProjection.app X).hom n)

/-- Actual restriction transports the first Mayer–Vietoris factor. -/
def positivePairEquiv (n : ℕ) :
    PerfectK (positiveOpen X).toScheme n × PerfectK (polynomialFunctor.obj X).obj n ≃*
      PerfectK (polynomialFunctor.obj X).obj n × PerfectK (polynomialFunctor.obj X).obj n :=
  MulEquiv.prodCongr (perfectKRestrictIsoEquiv (positiveOpenIso X) n) (MulEquiv.refl _)

/-- Actual restriction transports the original intersection to the native Laurent scheme. -/
def laurentOverlapEquiv (n : ℕ) :
    PerfectK (overlapOpen X).toScheme n ≃* PerfectK (laurentFunctor.obj X).obj n :=
  perfectKRestrictIsoEquiv (overlapOpenIso X) n

theorem restrictionPair_square (n : ℕ) :
    (positivePairEquiv X n).toMonoidHom.comp
        (PerfectMayerVietoris.restrictionPair (nativeMinus.app X).hom (positiveOpen X) n) =
      restrictionPair X n := by
  apply MonoidHom.ext
  intro x
  apply Prod.ext
  · change perfectKRestrict (positiveOpenIso X).hom n
      (perfectKRestrict (positiveOpen X).ι n x) =
        perfectKRestrict (nativePlus.app X).hom n x
    have h := perfectKRestrict_comp (positiveOpenIso X).hom (positiveOpen X).ι n
    simp only [positiveOpenIso_hom_inclusion] at h
    exact (DFunLike.congr_fun h x).symm
  · rfl

theorem laurentDifference_square (n : ℕ) :
    (laurentOverlapEquiv X n).toMonoidHom.comp
        (PerfectMayerVietoris.overlapDifference (nativeMinus.app X).hom (positiveOpen X) n) =
      (laurentDifference X n).comp (positivePairEquiv X n).toMonoidHom := by
  have hp := perfectKRestrict_comp (overlapOpenIso X).hom
    ((nativeMinus.app X).hom.resLE (positiveOpen X) (overlapOpen X) le_rfl) n
  simp only [overlapOpenIso_hom_toPositive] at hp
  have hp' := perfectKRestrict_comp
    (PolynomialLaurent.Relative.plus.app X).hom (positiveOpenIso X).hom n
  have hm := perfectKRestrict_comp (overlapOpenIso X).hom (overlapOpen X).ι n
  simp only [overlapOpenIso_hom_inclusion] at hm
  ext x
  change perfectKRestrict (overlapOpenIso X).hom n
      (perfectKRestrict
          ((nativeMinus.app X).hom.resLE (positiveOpen X) (overlapOpen X) le_rfl) n x.1 *
        (perfectKRestrict (overlapOpen X).ι n x.2)⁻¹) =
    perfectKRestrict (PolynomialLaurent.Relative.plus.app X).hom n
      (perfectKRestrict (positiveOpenIso X).hom n x.1) *
        (perfectKRestrict (PolynomialLaurent.Relative.minus.app X).hom n x.2)⁻¹
  rw [map_mul, map_inv]
  exact congrArg₂ (fun a b => a * b⁻¹)
    (DFunLike.congr_fun (hp.symm.trans hp') x.1)
    (DFunLike.congr_fun hm x.2).symm

variable [QuasiSeparatedSpace X.obj]

/-- The original projective-line restriction pair is exactly the signed Laurent kernel,
including degree zero, on any quasi-compact quasi-separated scheme. -/
theorem range_restrictionPair_eq_ker_laurentDifference (n : ℕ) :
    (restrictionPair X n).range = (laurentDifference X n).ker := by
  let j := (nativeMinus.app X).hom
  let T := positiveOpen X
  have h : (PerfectMayerVietoris.restrictionPair j T n).range =
      (PerfectMayerVietoris.overlapDifference j T n).ker := by
    cases n with
    | zero =>
      exact PerfectMayerVietoris.qcqs_range_restrictionPair_zero_eq_ker_overlapDifference
        j T (positiveOpen_isCompact X) (chart_cover X)
    | succ n =>
      exact (PerfectMayerVietoris.qcqs_positiveExactSequence
        j T (positiveOpen_isCompact X) (chart_cover X) n).1
  have hr : Function.MulExact (PerfectMayerVietoris.restrictionPair j T n)
      (PerfectMayerVietoris.overlapDifference j T n) := MonoidHom.mulExact_iff.mpr h.symm
  have hr' := (MonoidHom.mulExact_iff_of_surjective_of_bijective_of_injective
    (PerfectMayerVietoris.restrictionPair j T n) (PerfectMayerVietoris.overlapDifference j T n)
    (restrictionPair X n) (laurentDifference X n)
    (MonoidHom.id _) (positivePairEquiv X n).toMonoidHom
    (laurentOverlapEquiv X n).toMonoidHom
    (by simpa only [MonoidHom.comp_id] using (restrictionPair_square X n).symm)
    (laurentDifference_square X n).symm Function.surjective_id
    (positivePairEquiv X n).bijective (laurentOverlapEquiv X n).injective).mp hr
  exact (MonoidHom.mulExact_iff.mp hr').symm

end Quillen.PerfectComplexes.ProjectiveLine.NativeBass
