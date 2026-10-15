/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.ModuleComplex.PrincipalDenominators
public import Quillen.AlgebraicGeometry.PerfectComplexes.Restriction
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.AffineProjective
public import Mathlib.Data.Int.Interval

/-!
# Actual affine strict-perfect module models

Bounded finite-projective module complexes give actual strict-perfect sheaf
complexes, and global sections of an affine strict-perfect complex give a
bounded finite-projective module complex. All rings are arbitrary.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Quillen.PerfectComplexes.Affine
open Quillen.ModuleComplex.PrincipalLocalization

/-- The category of integer-indexed cochain complexes of `R`-modules. -/
abbrev ModuleComplex (R : CommRingCat.{u}) := CochainComplex (ModuleCat.{u} R) ℤ

/-- Boundedness of the actual terms, together with finite projectivity. -/
def moduleStrictPerfect (R : CommRingCat.{u}) : ObjectProperty (ModuleComplex R) := fun K =>
  (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (K.X i)) ∧
    ∀ i, Module.Finite R (K.X i) ∧ Module.Projective R (K.X i)

/-- The actual termwise associated-sheaf functor. -/
abbrev associatedComplex (R : CommRingCat.{u}) : ModuleComplex R ⥤ Complex (Spec R) :=
  (tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Actual affine global sections applied term by term. -/
abbrev sectionsComplex (R : CommRingCat.{u}) : Complex (Spec R) ⥤ ModuleComplex R :=
  (moduleSpecΓFunctor (R := R)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Finite projective terms give finite locally free associated sheaves. -/
theorem strictPerfect_associated (R : CommRingCat.{u}) {K : ModuleComplex R}
    (hK : moduleStrictPerfect R K) : strictPerfect (Spec R) ((associatedComplex R).obj K) := by
  obtain ⟨⟨a, b, hb⟩, hp⟩ := hK
  refine ⟨⟨a, b, fun i hi => (tilde.functor R).map_isZero (hb i hi)⟩, fun i => ?_⟩
  let := (hp i).1
  let := (hp i).2
  exact AlgebraicGeometry.Scheme.Modules.finiteLocallyFree_tilde_of_finite_projective R (K.X i)

/-- Global sections of an affine strict-perfect sheaf complex are bounded
and degreewise finite projective, without a noetherianity assumption. -/
theorem moduleStrictPerfect_sections (R : CommRingCat.{u}) {K : Complex (Spec R)}
    (hK : strictPerfect (Spec R) K) : moduleStrictPerfect R ((sectionsComplex R).obj K) := by
  obtain ⟨⟨a, b, hb⟩, hp⟩ := hK
  refine ⟨⟨a, b, fun i hi => moduleSpecΓFunctor.map_isZero (hb i hi)⟩, fun i => ?_⟩
  let := hp i
  exact ⟨AlgebraicGeometry.Scheme.Modules.finite_globalSections_of_finiteLocallyFree R (K.X i),
    AlgebraicGeometry.Scheme.Modules.projective_globalSections_of_finiteLocallyFree R (K.X i)⟩

/-- The actual counit reconstructs every termwise quasicoherent affine
sheaf complex from its genuine module complex of global sections. -/
def associatedSectionsIsoOfQuasicoherent (R : CommRingCat.{u}) (K : Complex (Spec R))
    (hK : ∀ i, (K.X i).IsQuasicoherent) :
    (associatedComplex R).obj ((sectionsComplex R).obj K) ≅ K := by
  let f : (associatedComplex R).obj ((sectionsComplex R).obj K) ⟶ K :=
    { f := fun i => (K.X i).fromTildeΓ
      comm' := fun i j _ => (Scheme.Modules.fromTildeΓNatTrans.naturality (K.d i j)).symm }
  have (i : ℤ) : IsIso (f.f i) := by
    let := hK i
    exact Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (K.X i)
  have : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  exact asIso f

/-- The actual counit reconstructs an affine strict-perfect sheaf complex
from its genuine bounded finite-projective module complex. -/
def associatedSectionsIso (R : CommRingCat.{u}) {K : Complex (Spec R)}
    (hK : strictPerfect (Spec R) K) :
    (associatedComplex R).obj ((sectionsComplex R).obj K) ≅ K :=
  associatedSectionsIsoOfQuasicoherent R K (fun i => by
    let := hK.2 i
    infer_instance)

/-- Bounded finite-projective complexes have finite-support terms and
finitely presented terms, precisely the denominator theorem's inputs. -/
theorem moduleStrictPerfect_denominator_inputs (R : CommRingCat.{u}) {K : ModuleComplex R}
    (hK : moduleStrictPerfect R K) :
    (∃ s : Finset ℤ, ∀ i ∉ s, IsZero (K.X i)) ∧
      ∀ i, Module.FinitePresentation R (K.X i) := by
  obtain ⟨⟨a, b, hb⟩, hp⟩ := hK
  refine ⟨⟨Finset.Icc a b, fun i hi => hb i ?_⟩, fun i => ?_⟩
  · simp only [Finset.mem_Icc, not_and_or, not_le] at hi
    exact hi
  · let := (hp i).1
    let := (hp i).2
    exact Module.finitePresentation_of_projective R (K.X i)

/-- Concrete fraction replacement for the genuine bounded finite-projective
module model. The same source is retained and the denominator is proved
invertible under actual localization. -/
theorem exists_moduleStrictPerfect_fraction (R : CommRingCat.{u}) (r : R)
    {K L : ModuleComplex R} (hK : moduleStrictPerfect R K)
    (f : (localize r (ComplexShape.up ℤ)).obj K ⟶
      (localize r (ComplexShape.up ℤ)).obj L) :
    ∃ (n : ℕ) (g : K ⟶ L),
      IsIso ((localize r (ComplexShape.up ℤ)).map (r ^ n • 𝟙 K)) ∧
      (localize r (ComplexShape.up ℤ)).map (r ^ n • 𝟙 K) ≫ f =
        (localize r (ComplexShape.up ℤ)).map g := by
  obtain ⟨⟨s, hs⟩, hfp⟩ := moduleStrictPerfect_denominator_inputs R hK
  exact exists_chain_fraction r s hs hfp f


/-- Scalar localization followed by the actual associated sheaf agrees
naturally with actual geometric restriction to the principal open. -/
def principalRestrictionAssociatedIso (R : CommRingCat.{u}) (r : R) :
    ModuleCat.localizedModuleFunctor (Submonoid.powers r) ⋙
      tilde.functor (CommRingCat.of (Localization.Away r)) ≅
    tilde.functor R ⋙ Scheme.Modules.restrictFunctor
      (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r) := by
  let F := tilde.functor R ⋙ Scheme.Modules.restrictFunctor
    (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)
  let T := tilde.functor (CommRingCat.of (Localization.Away r))
  let Γ := moduleSpecΓFunctor (R := CommRingCat.of (Localization.Away r))
  let α : F ⋙ Γ ⋙ T ⟶ F ⋙ 𝟭 _ :=
    Functor.whiskerLeft F Scheme.Modules.fromTildeΓNatTrans
  have (M : ModuleCat.{u} R) : IsIso (α.app M) := by
    have : (F.obj M).IsQuasicoherent :=
      Scheme.Modules.isQuasicoherent_restrictFunctor
        (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r) (tilde M)
    exact Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (F.obj M)
  have : IsIso α := NatIso.isIso_of_isIso_app α
  exact Functor.isoWhiskerRight
    (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.localizationRestrictionNatIso R r) T ≪≫
    Functor.associator F Γ T ≪≫ asIso α ≪≫ Functor.rightUnitor F

/-- The actual localization/restriction comparison on complexes. -/
def principalRestrictionAssociatedComplexIso (R : CommRingCat.{u}) (r : R) :
    localize r (ComplexShape.up ℤ) ⋙
      associatedComplex (CommRingCat.of (Localization.Away r)) ≅
    associatedComplex R ⋙ restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R
      r) :=
  by
    letI : (tilde.functor (CommRingCat.of (Localization.Away r))).Additive :=
      AlgebraicGeometry.instAdditiveModuleCatCarrierModulesSpecFunctor
    letI : (ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers r) ⋙
        tilde.functor (CommRingCat.of (Localization.Away r))).Additive := by
      infer_instance
    exact NatIso.mapHomologicalComplex (principalRestrictionAssociatedIso R r) (ComplexShape.up ℤ)


/-- Actual principal localization preserves the bounded finite-projective
module model over an arbitrary commutative ring. -/
theorem moduleStrictPerfect_localize (R : CommRingCat.{u}) (r : R) {K : ModuleComplex R}
    (hK : moduleStrictPerfect R K) :
    moduleStrictPerfect (CommRingCat.of (Localization.Away r))
      ((localize r (ComplexShape.up ℤ)).obj K) := by
  obtain ⟨⟨a, b, hb⟩, hp⟩ := hK
  refine ⟨⟨a, b, fun i hi =>
    (ModuleCat.localizedModuleFunctor (Submonoid.powers r)).map_isZero (hb i hi)⟩, fun i => ?_⟩
  let := (hp i).1
  let := (hp i).2
  change Module.Finite (Localization.Away r) ((K.X i).localizedModule (Submonoid.powers r)) ∧
    Module.Projective (Localization.Away r) ((K.X i).localizedModule (Submonoid.powers r))
  exact ⟨Module.Finite.of_isLocalizedModule (Submonoid.powers r)
      ((K.X i).localizedModuleMkLinearMap (Submonoid.powers r)),
    Module.projective_of_isLocalizedModule (Submonoid.powers r)
      ((K.X i).localizedModuleMkLinearMap (Submonoid.powers r))⟩

/-- The associated-complex functor is full, so localized sheaf chain maps
between associated complexes retain actual module chain representatives. -/
theorem associatedComplex_full (R : CommRingCat.{u}) : (associatedComplex R).Full := by
  infer_instance

/-- Genuine principal-open replacement for chain maps between associated
sheaf complexes. The source is a bounded finite-projective complex, and
restriction is the existing geometric functor. -/
theorem exists_principal_chain_fraction (R : CommRingCat.{u}) (r : R)
    {K L : ModuleComplex R} (hK : moduleStrictPerfect R K)
    (f : (restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj
      ((associatedComplex R).obj K) ⟶
      (restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj
        ((associatedComplex R).obj L)) :
    ∃ (n : ℕ) (g : K ⟶ L),
      IsIso ((restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).map
        ((associatedComplex R).map (r ^ n • 𝟙 K))) ∧
      (restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).map
        ((associatedComplex R).map (r ^ n • 𝟙 K)) ≫ f =
      (restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).map
        ((associatedComplex R).map g) := by
  let B := associatedComplex (CommRingCat.of (Localization.Away r))
  let e := principalRestrictionAssociatedComplexIso R r
  let : B.Full := associatedComplex_full _
  obtain ⟨β, hβ⟩ := B.map_surjective (e.hom.app K ≫ f ≫ e.inv.app L)
  obtain ⟨n, g, hd, hg⟩ := exists_moduleStrictPerfect_fraction R r hK β
  let := hd
  have hf : f = e.inv.app K ≫ B.map β ≫ e.hom.app L := by
    rw [hβ]
    simp
  refine ⟨n, g, ?_, ?_⟩
  · change IsIso ((associatedComplex R ⋙ restrict
    (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).map _)
    rw [← NatIso.naturality_1 e (r ^ n • 𝟙 K)]
    change IsIso (e.inv.app K ≫ B.map ((localize r (ComplexShape.up ℤ)).map
      (r ^ n • 𝟙 K)) ≫ e.hom.app K)
    infer_instance
  · change (associatedComplex R ⋙ restrict
    (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).map _ ≫ f =
      (associatedComplex R ⋙ restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen
        R r)).map g
    rw [hf, ← NatIso.naturality_1 e (r ^ n • 𝟙 K), ← NatIso.naturality_1 e g]
    simpa only [Functor.comp_map, B, Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
      using
      congrArg (fun t => e.inv.app K ≫ B.map t ≫ e.hom.app L) hg

end Quillen.PerfectComplexes.Affine
