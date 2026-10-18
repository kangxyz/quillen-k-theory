/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.GTheory.Dedekind.FiniteResidueLocalization
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic

/-!
# Actual arithmetic generic G2 class detection

The consumers use the original public spectrum pullback and the original native
finite-module localization map. Finiteness is established from arithmetic finite
quotients and the actual residue equivalence, with no point-K2 vanishing premise.
-/

public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open AlgebraicGeometry
open scoped nonZeroDivisors

namespace DownstreamFiniteResidue

variable (R : Type u) [CommRing R] [IsDedekindDomain R] [Ring.HasFiniteQuotients R]

/-- The arithmetic finite-quotient condition implies finiteness of the actual
native residue fields, through their original quotient algebra maps. -/
theorem actualResidueFinite (p : IsDedekindDomain.HeightOneSpectrum R) :
    Finite p.asIdeal.ResidueField := by
  let : Finite (R ⧸ p.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient p.ne_bot
  exact Finite.of_surjective (Quillen.DedekindResidue.quotientResidueFieldAlgEquiv R p)
    (Quillen.DedekindResidue.quotientResidueFieldAlgEquiv R p).surjective

/-- Equality after the original native generic G2 localization detects equality
of the original integral finite-module classes. -/
theorem generic_detects_integral_class
    (a b : Quillen.FiniteModuleLocalization.G R 2)
    (h : Quillen.FiniteModuleLocalization.localizationKMap (nonZeroDivisors R) 2 a =
      Quillen.FiniteModuleLocalization.localizationKMap (nonZeroDivisors R) 2 b) : a = b :=
  Quillen.DedekindFiniteResidue.genericGTwo_injective R (actualResidueFinite R) h

variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
local instance fractionSpecMap_flat :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R)))

/-- The literal public pullback to the supplied actual fraction field detects
equality on the integral affine scheme's original G2 group. -/
theorem supplied_fraction_detects_public_class
    (a b : Scheme.G (Spec (CommRingCat.of R)) 2)
    (h : Scheme.pullbackG (Spec.map (CommRingCat.ofHom (algebraMap R K))) 2 a =
      Scheme.pullbackG (Spec.map (CommRingCat.ofHom (algebraMap R K))) 2 b) : a = b :=
  Quillen.DedekindFiniteResidue.spec_genericGTwo_pullback_field_injective
    R K (actualResidueFinite R) h

end DownstreamFiniteResidue
