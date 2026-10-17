/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeCoefficientObjectBoundary

/-!
# Original native projective Mayer–Vietoris sequence

The actual overlap and positive-range isomorphisms transport the unchanged qcqs connecting
map and both exact positions to the original polynomial and Laurent schemes. This retains
the original boundary at degree zero and uses no projective-bundle inverse.
-/
@[expose] public section
open AlgebraicGeometry.Scheme.Products
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes.ProjectiveLine.NativeBass
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Waldhausen.Additivity.KCommGroup

variable (X : QuasiCompactSchemes.{u}) [QuasiSeparatedSpace X.obj]

/-- Actual overlap transport retains the unchanged original qcqs connecting homomorphism. -/
theorem projectiveConnecting_square (n : ℕ) :
    (projectiveConnecting X n).comp (laurentOverlapEquiv X (n + 1)).toMonoidHom =
      PerfectMayerVietoris.qcqsConnectingHom (nativeMinus.app X).hom (positiveOpen X)
        (positiveOpen_isCompact X) (chart_cover X) n := by
  ext x
  change PerfectMayerVietoris.qcqsConnectingHom (nativeMinus.app X).hom (positiveOpen X)
    (positiveOpen_isCompact X) (chart_cover X) n
      ((laurentOverlapEquiv X (n + 1)).symm (laurentOverlapEquiv X (n + 1) x)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The signed original Laurent difference is exactly the original projective boundary kernel.
-/
theorem range_laurentDifference_eq_ker_projectiveConnecting (n : ℕ) :
    (laurentDifference X (n + 1)).range = (projectiveConnecting X n).ker := by
  have h := (PerfectMayerVietoris.qcqs_positiveExactSequence (nativeMinus.app X).hom
    (positiveOpen X) (positiveOpen_isCompact X) (chart_cover X) n).2.1
  have he := MonoidHom.mulExact_iff.mpr h.symm
  have ht := (MonoidHom.mulExact_iff_of_surjective_of_bijective_of_injective
    (PerfectMayerVietoris.overlapDifference (nativeMinus.app X).hom (positiveOpen X) (n + 1))
    (PerfectMayerVietoris.qcqsConnectingHom (nativeMinus.app X).hom (positiveOpen X)
      (positiveOpen_isCompact X) (chart_cover X) n)
    (laurentDifference X (n + 1)) (projectiveConnecting X n)
    (positivePairEquiv X (n + 1)).toMonoidHom
    (laurentOverlapEquiv X (n + 1)).toMonoidHom (MonoidHom.id _)
    (laurentDifference_square X (n + 1)).symm
    (by simpa only [MonoidHom.id_comp] using projectiveConnecting_square X n)
    (positivePairEquiv X (n + 1)).surjective
    (laurentOverlapEquiv X (n + 1)).bijective Function.injective_id).mp he
  exact (MonoidHom.mulExact_iff.mp ht).symm

/-- The unchanged projective boundary image is exactly the two original chart kernel. -/
theorem range_projectiveConnecting_eq_ker_restrictionPair (n : ℕ) :
    (projectiveConnecting X n).range = (restrictionPair X n).ker := by
  have h := (PerfectMayerVietoris.qcqs_positiveExactSequence (nativeMinus.app X).hom
    (positiveOpen X) (positiveOpen_isCompact X) (chart_cover X) n).2.2
  have he := MonoidHom.mulExact_iff.mpr h.symm
  have ht := (MonoidHom.mulExact_iff_of_surjective_of_bijective_of_injective
    (PerfectMayerVietoris.qcqsConnectingHom (nativeMinus.app X).hom (positiveOpen X)
      (positiveOpen_isCompact X) (chart_cover X) n)
    (PerfectMayerVietoris.restrictionPair (nativeMinus.app X).hom (positiveOpen X) n)
    (projectiveConnecting X n) (restrictionPair X n)
    (laurentOverlapEquiv X (n + 1)).toMonoidHom (MonoidHom.id _)
    (positivePairEquiv X n).toMonoidHom
    (by simpa only [MonoidHom.id_comp] using projectiveConnecting_square X n)
    (by simpa only [MonoidHom.comp_id] using (restrictionPair_square X n).symm)
    (laurentOverlapEquiv X (n + 1)).surjective Function.bijective_id
    (positivePairEquiv X n).injective).mp he
  exact (MonoidHom.mulExact_iff.mp ht).symm

end Quillen.PerfectComplexes.ProjectiveLine.NativeBass
