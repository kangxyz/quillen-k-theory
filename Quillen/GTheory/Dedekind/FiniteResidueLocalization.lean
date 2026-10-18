/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.GTheory.Dedekind.Localization
public import Quillen.KTheory.Field.FiniteFieldKTwo
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.LocalizationNaturality

/-!
# Generic G2 injectivity for Dedekind domains with finite residue fields

The actual finite-field lower G2 theorem passes through the original native
residue-field comparison and quotient-to-primary dévissage. Every point-primary
G2 group and the original supported G2 group are therefore subsingletons.
Original localization exactness gives injectivity of the unchanged finite-module
generic G2 map.

The canonical affine square gives the same conclusion for the literal public
coherent pullback along the spectrum of the localization map. A supplied fraction
field uses its canonical localization equivalence and the genuine spectrum
isomorphism; the final pullback is still along the original algebra map.

No generic G1 injectivity premise or conclusion is used. Applications to a
distinct scheme stalk and any arithmetic generic G1 statement remain separate.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.ExactCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Coherent
open scoped nonZeroDivisors

namespace Quillen.DedekindFiniteResidue

variable (R : Type u) [CommRing R] [IsDedekindDomain R]

/-- Finiteness of the actual native residue field makes the actual point-primary
K2 group trivial, through the original two residue comparison maps. -/
theorem primaryKTwo_subsingleton (p : IsDedekindDomain.HeightOneSpectrum R)
    [Finite p.asIdeal.ResidueField] : Subsingleton (DedekindPrimary.PrimaryK R p 2) := by
  let e := (DedekindResidue.residueFieldKEquiv R p 2).trans
    (DedekindResidue.residuePrimaryKEquiv R p 2)
  constructor
  intro a b
  apply e.symm.injective
  exact @Subsingleton.elim _ (Field.finiteModuleGTwo_subsingleton p.asIdeal.ResidueField) _ _

/-- Arithmetic finiteness at every actual height-one residue field annihilates
the original native supported G2 group. -/
theorem supportedGTwo_subsingleton
    (hfinite : ∀ p : IsDedekindDomain.HeightOneSpectrum R, Finite p.asIdeal.ResidueField) :
    Subsingleton (FiniteModuleLocalization.SupportedG (nonZeroDivisors R) 2) := by
  apply DedekindPrimary.supportedK_subsingleton_of_primaryK_subsingleton R 2
  intro p
  let : Finite p.asIdeal.ResidueField := hfinite p
  exact primaryKTwo_subsingleton R p

/-- The original generic finite-module G2 localization map is injective when
all actual height-one residue fields are finite. -/
theorem genericGTwo_injective
    (hfinite : ∀ p : IsDedekindDomain.HeightOneSpectrum R, Finite p.asIdeal.ResidueField) :
    Function.Injective (FiniteModuleLocalization.localizationKMap (nonZeroDivisors R) 2) := by
  apply DedekindPrimary.genericG2_injective_of_primaryK2_subsingleton R
  intro p
  let : Finite p.asIdeal.ResidueField := hfinite p
  exact primaryKTwo_subsingleton R p

/-- The literal public coherent G2 pullback along the canonical generic
localization spectrum map is injective under actual residue-field finiteness. -/
theorem spec_genericGTwo_pullback_injective
    (hfinite : ∀ p : IsDedekindDomain.HeightOneSpectrum R, Finite p.asIdeal.ResidueField) :
    Function.Injective (Scheme.pullbackG
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization (nonZeroDivisors R))))) 2) := by
  intro a b hab
  apply (publicSpecGRingEquiv (CommRingCat.of R) 2).injective
  apply genericGTwo_injective R hfinite
  have h := congrArg
    (publicSpecGRingEquiv (CommRingCat.of (Localization (nonZeroDivisors R))) 2) hab
  have ha := DFunLike.congr_fun
    (publicSpecGRingEquiv_localization_pullback (nonZeroDivisors R) 2) a
  have hb := DFunLike.congr_fun
    (publicSpecGRingEquiv_localization_pullback (nonZeroDivisors R) 2) b
  exact ha.symm.trans (h.trans hb)

private theorem pullbackG_iso_injective {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (e : X ≅ Y) (n : ℕ) :
    Function.Injective (Scheme.pullbackG e.hom n) := by
  have hc : (Scheme.pullbackG e.inv n).comp (Scheme.pullbackG e.hom n) =
      MonoidHom.id (Scheme.G Y n) := by
    simp only [← Scheme.pullbackG_comp, e.inv_hom_id, Scheme.pullbackG_id]
  exact (show Function.LeftInverse (Scheme.pullbackG e.inv n)
    (Scheme.pullbackG e.hom n) from fun a => DFunLike.congr_fun hc a).injective

section SuppliedFractionField
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

private def fractionSpecIso : Spec (CommRingCat.of K) ≅
    Spec (CommRingCat.of (Localization (nonZeroDivisors R))) :=
  Scheme.Spec.mapIso
    ((IsLocalization.algEquiv (nonZeroDivisors R)
      (Localization (nonZeroDivisors R)) K).toRingEquiv.toCommRingCatIso.op)

local instance fractionSpecMap_flat :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R)))

omit [IsDedekindDomain R] in
private theorem fractionSpecIso_triangle :
    (fractionSpecIso R K).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization (nonZeroDivisors R)))) =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
  change Spec.map (CommRingCat.ofHom
      (IsLocalization.algEquiv (nonZeroDivisors R) (Localization (nonZeroDivisors R)) K).toRingHom)
      ≫ Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization (nonZeroDivisors R)))) = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext r
  exact (IsLocalization.algEquiv (nonZeroDivisors R)
    (Localization (nonZeroDivisors R)) K).commutes r

/-- For a supplied actual fraction field, the original public G2 pullback
along its original algebra map is injective under actual residue-field finiteness. -/
theorem spec_genericGTwo_pullback_field_injective
    (hfinite : ∀ p : IsDedekindDomain.HeightOneSpectrum R, Finite p.asIdeal.ResidueField) :
    Function.Injective (Scheme.pullbackG (Spec.map (CommRingCat.ofHom (algebraMap R K))) 2) := by
  have hi := (pullbackG_iso_injective (fractionSpecIso R K) 2).comp
    (spec_genericGTwo_pullback_injective R hfinite)
  change Function.Injective ((Scheme.pullbackG (fractionSpecIso R K).hom 2).comp
    (Scheme.pullbackG (Spec.map (CommRingCat.ofHom
      (algebraMap R (Localization (nonZeroDivisors R))))) 2)) at hi
  simpa only [← Scheme.pullbackG_comp, fractionSpecIso_triangle R K,
    CommRingCat.of_carrier] using hi

end SuppliedFractionField

end Quillen.DedekindFiniteResidue
