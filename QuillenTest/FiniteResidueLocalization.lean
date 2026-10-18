/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.GTheory.Dedekind.FiniteResidueLocalization
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic

/-! # Arithmetic integer and literal public-map consumers of finite-residue G2 injectivity -/

public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry
open scoped nonZeroDivisors

namespace QuillenTest.FiniteResidueLocalization

/-- Actual integer height-one residue fields are finite by finite integer
quotients and the original quotient-to-residue algebra equivalence. -/
theorem integerResidueFinite (p : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Finite p.asIdeal.ResidueField := by
  let : Finite (ℤ ⧸ p.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient p.ne_bot
  exact Finite.of_surjective (Quillen.DedekindResidue.quotientResidueFieldAlgEquiv ℤ p)
    (Quillen.DedekindResidue.quotientResidueFieldAlgEquiv ℤ p).surjective

example : Function.Injective (Quillen.FiniteModuleLocalization.localizationKMap (nonZeroDivisors ℤ)
    2) :=
  Quillen.DedekindFiniteResidue.genericGTwo_injective ℤ integerResidueFinite

example : Function.Injective (Scheme.pullbackG
    (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization (nonZeroDivisors ℤ))))) 2) :=
  Quillen.DedekindFiniteResidue.spec_genericGTwo_pullback_injective ℤ integerResidueFinite

local instance rationalSpecMap_flat :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) :=
  Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat ℚ (nonZeroDivisors ℤ)))

example : Function.Injective
    (Scheme.pullbackG (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) 2) :=
  Quillen.DedekindFiniteResidue.spec_genericGTwo_pullback_field_injective ℤ ℚ integerResidueFinite

end QuillenTest.FiniteResidueLocalization
