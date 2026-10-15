/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.ScalarSupportExtension
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedProjectorExtension
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.StabilizedExtensionTransport
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedZero

/-! # Genuine supported stabilized extension from compact affine opens

An original perfect complex on a compact open W, vanishing on W intersect Z
for another compact open Z, admits an actual global finite-projective module
complex whose associated restriction is the original E plus E[1] and whose
restriction to all Z vanishes. Actual scalar cones force the finite-principal
support; the support-preserving projector roof retains it during stabilization.
No exponent, supported extension, or global weak denominator is assumed.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes.Affine
open Quillen.ModuleComplex.PrincipalLocalization
attribute [local instance] standardDerivedModules standardDerivedSheaves
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Every original perfect complex on a compact affine open, vanishing on a
specified finite principal part of that open, has a global stabilized strict
extension vanishing on those same entire principal opens. -/
lemma locallyPerfect_exists_stabilized_extension_with_principal_support
    (R : CommRingCat.{u}) (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (s : Finset R) (E : Complex W.toScheme) (hE : locallyPerfect W.toScheme E)
    (hzero : ∀ z ∈ s, IsZero ((toDerived (W ⊓ PrimeSpectrum.basicOpen z).toScheme).obj
      ((restrict ((Spec R).homOfLE (inf_le_left : W ⊓ PrimeSpectrum.basicOpen z ≤ W))).obj E))) :
    ∃ (Q : ModuleComplex R), moduleStrictPerfect R Q ∧
      Nonempty ((toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj Q)) ≅
        (toDerived W.toScheme).obj (E ⊞ E⟦(1 : ℤ)⟧)) ∧
      ∀ z ∈ s, IsZero (DerivedCategory.Q.obj ((localize z (.up ℤ)).obj Q)) := by
  obtain ⟨P, P', hP, hP', g, hg, ⟨eg⟩⟩ :=
    locallyPerfect_exists_stabilized_extension_cone R W hW E hE
  let P₀ := CochainComplex.mappingCone g
  let r₀ : Retract E (E ⊞ E⟦(1 : ℤ)⟧) :=
    { i := biprod.inl, r := biprod.fst, retract := biprod.inl_fst }
  let r := (r₀.map (toDerived W.toScheme)).trans (Retract.ofIso eg.symm)
  have hz (z : R) (hz : z ∈ s) :
      IsZero ((toDerived (W ⊓ PrimeSpectrum.basicOpen z).toScheme).obj
        ((restrict (W ⊓ PrimeSpectrum.basicOpen z).ι).obj ((associatedComplex R).obj P₀))) := by
    let I := W ⊓ PrimeSpectrum.basicOpen z
    let k := (Spec R).homOfLE (inf_le_left : I ≤ W)
    let e := (toDerived I.toScheme).mapIso
      (restrictOpenInclusionIso (inf_le_left : I ≤ W) ((associatedComplex R).obj P₀)).symm ≪≫
        restrictDerivedIso k eg ≪≫ (toDerived I.toScheme).mapIso (restrictStabilizationIso k E)
    exact (isZero_toDerived_stabilization_of_isZero (hzero z hz)).of_iso e
  obtain ⟨Q, hQ, i, rQ, hi, hQS, hQO, hQP⟩ :=
    exists_finite_scalar_cone_support R W hW s hg r hz
  obtain ⟨Q', hQ', eQ', hsupport⟩ :=
    exists_stabilized_extension_preserving_support_of_retract R W hW hQ E hE rQ
  exact ⟨Q', hQ', eQ', fun z hz => hsupport z (hQS z hz)⟩

/-- Actual principal-local module acyclicity detects the original associated
restriction on their specified finite open union. -/
lemma isZero_restrict_associated_of_principalUnion (R : CommRingCat.{u})
    (Z : (Spec R).Opens) (s : Finset R)
    (hs : Quillen.SheafCohomology.principalUnion R s = Z) (P : ModuleComplex R)
    (hP : ∀ z ∈ s, IsZero (DerivedCategory.Q.obj ((localize z (.up ℤ)).obj P))) :
    IsZero ((toDerived Z.toScheme).obj ((restrict Z.ι).obj ((associatedComplex R).obj P))) := by
  have hq (z : R) (hz : z ∈ s) : QuasiIso ((localize z (.up ℤ)).map (0 : P ⟶ P)) := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp
    exact (hP z hz).isIso (hP z hz) _
  have hq' := quasiIso_restrict_associated_of_principalUnion R Z s hs (0 : P ⟶ P) hq
  have hi : IsIso ((toDerived Z.toScheme).map ((restrict Z.ι).map
      ((associatedComplex R).map (0 : P ⟶ P)))) := inferInstance
  simp only [Functor.map_zero] at hi
  exact (isIsoZero_iff_source_target_isZero _ _).mp hi |>.1

/-- A perfect complex on a compact affine open, supported away from its
intersection with a second compact open, has a genuine globally strict
stabilized extension supported away from that entire second open. -/
lemma locallyPerfect_exists_stabilized_extension_with_open_support
    (R : CommRingCat.{u}) (W Z : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) (hZ : IsCompact (Z : Set (Spec R)))
    (E : Complex W.toScheme) (hE : locallyPerfect W.toScheme E)
    (hzero : IsZero ((toDerived (W ⊓ Z).toScheme).obj
      ((restrict ((Spec R).homOfLE (inf_le_left : W ⊓ Z ≤ W))).obj E))) :
    ∃ (Q : ModuleComplex R), moduleStrictPerfect R Q ∧
      Nonempty ((toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj Q)) ≅
        (toDerived W.toScheme).obj (E ⊞ E⟦(1 : ℤ)⟧)) ∧
      IsZero ((toDerived Z.toScheme).obj ((restrict Z.ι).obj ((associatedComplex R).obj Q))) := by
  obtain ⟨s, hs⟩ := exists_finite_principal_cover R Z hZ
  have hz (z : R) (hz : z ∈ s) :
      IsZero ((toDerived (W ⊓ PrimeSpectrum.basicOpen z).toScheme).obj
        ((restrict ((Spec R).homOfLE (inf_le_left : W ⊓ PrimeSpectrum.basicOpen z ≤ W))).obj E)) :=
          by
    have hle : PrimeSpectrum.basicOpen z ≤ Z := by
      rw [← hs]
      exact Quillen.SheafCohomology.basicOpen_le_principalUnion R hz
    exact isZero_restrict_homOfLE_of_le (inf_le_inf le_rfl hle) inf_le_left E hzero
  obtain ⟨Q, hQ, eQ, hzeroQ⟩ :=
    locallyPerfect_exists_stabilized_extension_with_principal_support R W hW s E hE hz
  exact ⟨Q, hQ, eQ, isZero_restrict_associated_of_principalUnion R Z s hs Q hzeroQ⟩

end Quillen.PerfectComplexes.Affine
