/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.GTheory.FiniteModules.LocalizationNaturality
public import Quillen.GTheory.Dedekind.LocalDvrComparison

/-!
# Original native local-DVR boundary coordinates

The canonical ordinary two-step localization isomorphism gives naturality of
the original finite-module connecting homomorphisms. The supported map is the
original scalar-localization restriction, and the generic map is the original
tensor scalar-extension functor along `fractionRingMap`.

In every positive supported degree, the original local-DVR boundary after this
generic map agrees with the global native residue-field coordinate. This uses
the proved diagonal and off-diagonal residue-support comparisons through
`localResidueSupportCoordinate`. It implies the native G₂ kernel-intersection
formula and lifts arbitrary finite residue-field G₁ families under the explicit
native generic G₁ injectivity premise.

All groups and functors use the native common universe `u`. The statements here
concern finite-module boundaries; comparison with a scheme localization
boundary is a separate theorem.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open ModuleCat ModuleCat.FiniteLocalization
open scoped nonZeroDivisors

namespace Quillen.DedekindLocalDvr

attribute [local instance] Abelian.hasFiniteBiproducts

variable (R : Type u) [CommRing R] [IsDedekindDomain R]
  (p : IsDedekindDomain.HeightOneSpectrum R)

/-- The original supported scalar-localization K-map commutes with both
original finite-module connecting maps in every nonnegative degree. -/
theorem supportKMap_connectingHom_naturality (n : ℕ) :
    (supportKMap R p n).comp
        (FiniteModuleLocalization.connectingHom (nonZeroDivisors R) n) =
      (FiniteModuleLocalization.connectingHom
        (nonZeroDivisors (Localization.AtPrime p.asIdeal)) n).comp
          (canonicalFractionRestrictionKMap R p (n + 1)) := by
  exact FiniteModuleLocalization.connectingHom_naturality_of_exactSquare
    (nonZeroDivisors R) (nonZeroDivisors (Localization.AtPrime p.asIdeal))
    (FiniteModuleLocalization.exactFunctor p.asIdeal.primeCompl)
    (canonicalFractionRestrictionExact R p)
    (small_localization_preserves_torsion R p) (fractionLocalizationComparison R p) n

/-- The boundary square retains the original tensor scalar-extension functor
between the two native fraction-ring module categories. -/
theorem supportKMap_connectingHom_extension_naturality (n : ℕ) :
    (supportKMap R p n).comp
        (FiniteModuleLocalization.connectingHom (nonZeroDivisors R) n) =
      (FiniteModuleLocalization.connectingHom
        (nonZeroDivisors (Localization.AtPrime p.asIdeal)) n).comp
          ((Field.finiteModuleExtensionExact (fractionRingMap R p)).smallKMap (n + 1)) := by
  rw [← canonicalFractionRestrictionKMap_eq_extension]
  exact supportKMap_connectingHom_naturality R p n

open scoped DirectSum

/-- In every positive supported degree, the original local-DVR boundary after
canonical fraction restriction is the global native residue-field coordinate. -/
theorem localDvrBoundary_comp_fractionRestriction (n : ℕ) :
    (localDvrBoundary R p (n + 1)).comp
        (canonicalFractionRestrictionKMap R p (n + 2)) =
      DedekindResidue.residueFieldBoundary R (n + 1) p := by
  apply MonoidHom.ext
  intro b
  let a := (DedekindResidue.residueFieldAssemblyKEquiv R n).symm
    (Additive.ofMul (FiniteModuleLocalization.connectingHom (nonZeroDivisors R) (n + 1) b))
  have hb : Additive.ofMul
      (FiniteModuleLocalization.connectingHom (nonZeroDivisors R) (n + 1) b) =
        DedekindResidue.residueFieldAssemblyKEquiv R n a :=
    (AddEquiv.apply_symm_apply _ _).symm
  have hb' := congrArg Additive.toMul hb
  change FiniteModuleLocalization.connectingHom (nonZeroDivisors R) (n + 1) b =
    (DedekindResidue.residueFieldAssemblyKEquiv R n a).toMul at hb'
  have hn := DFunLike.congr_fun (supportKMap_connectingHom_naturality R p (n + 1)) b
  change supportKMap R p (n + 1)
      (FiniteModuleLocalization.connectingHom (nonZeroDivisors R) (n + 1) b) =
    FiniteModuleLocalization.connectingHom
      (nonZeroDivisors (Localization.AtPrime p.asIdeal)) (n + 1)
        (canonicalFractionRestrictionKMap R p (n + 2) b) at hn
  change (localResidueSupportKEquiv R p (n + 1)).symm
      (FiniteModuleLocalization.connectingHom
        (nonZeroDivisors (Localization.AtPrime p.asIdeal)) (n + 1)
          (canonicalFractionRestrictionKMap R p (n + 2) b)) = _
  rw [← hn, hb']
  exact (localResidueSupportCoordinate R p n a).trans
    (DedekindResidue.residueFieldBoundary_eq_of_assembly R n a b hb p).symm

/-- The same coordinate equality with the original generic tensor
scalar-extension map written explicitly. -/
theorem localDvrBoundary_comp_extension (n : ℕ) :
    (localDvrBoundary R p (n + 1)).comp
        ((Field.finiteModuleExtensionExact (fractionRingMap R p)).smallKMap (n + 2)) =
      DedekindResidue.residueFieldBoundary R (n + 1) p := by
  rw [← canonicalFractionRestrictionKMap_eq_extension]
  exact localDvrBoundary_comp_fractionRestriction R p n

/-- The original native local-DVR boundary pulled back along the original
generic tensor scalar-extension map from the global fraction ring. -/
def localDvrBoundaryFromGlobal (n : ℕ) :
    FiniteModuleLocalization.G (FractionRing R) (n + 1) →*
      FiniteModuleLocalization.G p.asIdeal.ResidueField n :=
  (localDvrBoundary R p n).comp
    ((Field.finiteModuleExtensionExact (fractionRingMap R p)).smallKMap (n + 1))

/-- Every positive-degree original native local-DVR coordinate is the global
native residue-field coordinate. -/
theorem localDvrBoundaryFromGlobal_eq_residueFieldBoundary (n : ℕ) :
    localDvrBoundaryFromGlobal R p (n + 1) =
      DedekindResidue.residueFieldBoundary R (n + 1) p :=
  localDvrBoundary_comp_extension R p n

/-- The native generic image is the intersection of the kernels of all actual
native local-DVR boundary coordinates in positive supported degree. -/
theorem localization_range_eq_iInf_localDvrBoundaryFromGlobal_ker (n : ℕ) :
    (FiniteModuleLocalization.localizationKMap (nonZeroDivisors R) (n + 2)).range =
      ⨅ p, (localDvrBoundaryFromGlobal R p (n + 1)).ker := by
  simpa only [localDvrBoundaryFromGlobal_eq_residueFieldBoundary] using
    DedekindResidue.localization_range_eq_iInf_residueFieldBoundary_ker R (n + 1)

/-- Native G₂ generic classes are detected by all actual local-DVR G₁ boundary
coordinates, with the original generic scalar-extension maps retained. -/
theorem genericG2_range_eq_iInf_localDvrBoundaryK1_ker :
    (FiniteModuleLocalization.localizationKMap (nonZeroDivisors R) 2).range =
      ⨅ p, (localDvrBoundaryFromGlobal R p 1).ker :=
  localization_range_eq_iInf_localDvrBoundaryFromGlobal_ker R 0

/-- Explicit native generic injectivity lifts each finite residue-field family
through the original boundary to its actual assembly and all original native
local-DVR coordinates. -/
theorem exists_localDvrBoundary_lift (n : ℕ)
    (h : Function.Injective
      (FiniteModuleLocalization.localizationKMap (nonZeroDivisors R) (n + 1)))
    (a : ⨁ p, Additive (DedekindResidue.ResidueFieldK R p (n + 1))) :
    ∃ b : FiniteModuleLocalization.G (FractionRing R) (n + 2),
      Additive.ofMul (FiniteModuleLocalization.connectingHom (nonZeroDivisors R) (n + 1) b) =
        DedekindResidue.residueFieldAssemblyKEquiv R n a ∧
      ∀ p, localDvrBoundaryFromGlobal R p (n + 1) b = (a p).toMul := by
  obtain ⟨b, hb, hbp⟩ := DedekindResidue.exists_residueFieldBoundary_lift R n h a
  refine ⟨b, hb, fun p => ?_⟩
  simpa only [localDvrBoundaryFromGlobal_eq_residueFieldBoundary] using hbp p

/-- Native generic G₁ injectivity lifts an arbitrary finite native residue-field
G₁ family to original G₂, with actual support assembly and every original
local-DVR boundary after the original generic tensor extension prescribed. -/
theorem localDvrG1_finite_family_lift
    (h : Function.Injective
      (FiniteModuleLocalization.localizationKMap (nonZeroDivisors R) 1))
    (a : ⨁ p, Additive (DedekindResidue.ResidueFieldK R p 1)) :
    ∃ b : FiniteModuleLocalization.G (FractionRing R) 2,
      Additive.ofMul (FiniteModuleLocalization.connectingHom (nonZeroDivisors R) 1 b) =
        DedekindResidue.residueFieldAssemblyKEquiv R 0 a ∧
      ∀ p, localDvrBoundary R p 1
        ((Field.finiteModuleExtensionExact (fractionRingMap R p)).smallKMap 2 b) =
          (a p).toMul :=
  exists_localDvrBoundary_lift R 0 h a

end Quillen.DedekindLocalDvr
